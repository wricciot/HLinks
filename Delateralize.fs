(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** Delateralize.fs - Implements the delateralization algorithm             **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)

module Delateralize

module Q = Query

let (>>=) (o : 'a option) (f : 'a -> 'b option) =
    match o with
    | Some a -> f a
    | _ -> None

let (||=) o o' =
    match o with
    | None -> o'
    | _ -> o

let squash o = o >>= fun x -> x

let rec (>>>=) (l : ('a option) list) (f : 'a -> 'b option) : ('b list) option =
    match l with
    | [] -> Some []
    | o::ol ->
           o >>= fun a ->
           f a >>= fun b ->
           (ol >>>= f) >>= fun bl -> 
           Some (b :: bl)

let unopt_default ox x' = match ox with None -> x' | Some x'' -> x''

let rec (>>==) (l : 'a list) (f : 'a -> 'a option) : 'a list option =
    match l with
    | [] -> None
    | a::al -> 
        match f a, al >>== f with
        | None, None -> None
        | fa, fal -> Some (unopt_default fa a::unopt_default fal al)

// C(q1, x.q2) := for x :- q1, #y :- q2 do {(x,#y)}
// also returns the fieltypes of the graph
let graph_query (q1,ty1) x (q2,ty2) =
    let y = Var.fresh_raw_var () in
    let p = Q.flattened_pair (Q.Var (x,ty1)) (Q.Var (y,ty2)) in
    let ftys = Q.flattened_pair_ft (Q.Var (x,ty1)) (Q.Var (y,ty2)) in
    Q.For ([(x, q1); (y, q2)], Q.Singleton p), ftys

// DELATERALIZING REWRITE for iota
// for gs, y :- I(q3) do q1     -- s.t. x :- q2 in gs
//  ~> for gs, p :- I(C(Dq2,x.q3)) where x = p.1 do ([y]q1) p.2
let prom_delateralize gs q1 x (q2,ty2) y (q3,ty3) =
    let p = Var.fresh_raw_var () in
    let graph, ftys = graph_query (Q.Dedup q2,ty2) x (q3,ty3) in
    let vp = Q.Var (p,ftys) in
    let vx = Q.Var (x,ty2) in
    let eq_test a b = Q.Apply (Q.Primitive "==", [a;b]) in
    let and_query a b = Q.Apply (Q.Primitive "&&", [a;b]) in
    // eta-expanded vx == p.1, with record flattening
    let eq_query = 
        Map.fold 
            (fun acc f _ ->  and_query acc (eq_test (Q.Project (vx, f)) (Q.Project (vp, Q.flatfield "1" f))))
            (Q.Constant (Constant.Bool true))
            ty2
    // eta-expanded p.2, with record flattening
    let rp = 
        ty3
        |> Map.fold (fun acc f _ -> Map.add f (Q.Project (vp, Q.flatfield "2" f)) acc) Map.empty
        |> Q.Record
    Q.For (gs @ [(p, Q.Prom graph)],
        Q.If (eq_query, Q.Apply (Q.Closure (([y], q1), Map.empty), [rp]), Q.nil))

// Returns (Some ty) if v occurs free with type ty, None otherwise
let occurs_free (v : Var.var) =
    let rec occf bvs = function
    | Q.Var (w,tyw) ->
        if w = v && not (List.contains v bvs)
            then Some tyw
            else None
    | Q.If (c,t,e) -> occf bvs c ||= occf bvs t ||= occf bvs e
    | Q.Closure ((wl,b),e) ->
        // XXX: to be checked
        let bvs' = bvs @ wl @ List.map (fun (w,_) -> w) (Map.toList e) in
        occf bvs' b ||= Map.tryPick (fun _ q -> occf bvs q) e
    | Q.Apply (t, args) -> occf bvs t ||= List.tryPick (occf bvs) args
    | Q.Singleton t
    | Q.Dedup t
    | Q.Prom t
    | Q.Project (t,_) -> occf bvs t
    | Q.Concat tl -> List.tryPick (occf bvs) tl
    | Q.For (gs, b) -> 
        let bvs'', res = List.fold (fun (bvs',acc) (w,q) -> w::bvs', acc ||= occf bvs' q) (bvs, None) gs in
        res ||= occf bvs'' b
    | Q.Record fl -> Map.tryPick (fun _ t -> occf bvs t) fl
    | _ -> None
    in occf []

// Returns Some (x,qx,tyx) for the first generator x <- qx such that x occurs free with type tyx
let rec occurs_free_gens (gs : (Var.var * Q.t) list) q =
    match gs with
    | [] -> None
    | (x,qx)::gs' -> 
        match occurs_free x (Q.For (gs',q)) with
        | Some tyx -> Some (x,qx,tyx)
        | None -> occurs_free_gens gs' q

// returns None if q is already delateralized
// returns Some q' if q simplifies to a less lateral q'
// (this actually performs PARALLEL delateralization steps)
let rec delateralize_step q =
    let ds = delateralize_step in
    match q with
    | Q.For (gs, q) -> 
        let rec findgs gsx = function
        | (y,Q.Prom qy as gy)::gsy -> 
            match occurs_free_gens gsx qy with 
            // tail-consing is annoying, but occurs_free_list needs arguments in this order
            | None -> findgs (gsx@[gy]) gsy
            | Some (x,qx,tyx) -> Some (gsx,x,qx,tyx,y,qy,gsy)
        | gy::gsy -> findgs (gy::gsx) gsy
        | [] -> None
        in
        match findgs [] gs with
        | Some (gsx,x,qx,tyx,y,qy,gsy) ->
            let qf = Q.For (gsy,q) in
            let tyy = Q.field_types_of_query qy in
            Some (prom_delateralize gsx qf x (qx,tyx) y (qy,tyy))
        | None ->
            let ogs = gs >>== (fun (z,qz) -> ds qz >>= fun qz' -> Some (z,qz')) in
            let oq = ds q in
            match ogs, oq with
            | None, None -> None
            | _ -> Some (Q.For (unopt_default ogs gs, unopt_default oq q))
    | Q.If (c,t,e) -> 
        match ds c, ds t, ds e with
        | None, None, None -> None
        | c', t', e' -> Some (Q.If (unopt_default c' c, unopt_default t' t, unopt_default e' e))
    // XXX: can t in Apply (t,...) even contain a For? however let's perform recursion for safety
    | Q.Apply (t,args) -> 
        let ot = ds t in
        let oargs = args >>== ds in
        match ot, oargs with
        | None, None -> None
        | _ -> Some (Q.Apply (unopt_default ot t, unopt_default oargs args))
    | Q.Singleton t -> match ds t with None -> None | Some t' -> Some (Q.Singleton t')
    | Q.Concat tl -> match tl >>== ds with None -> None | Some tl' -> Some (Q.Concat tl')
    | Q.Dedup t -> match ds t with None -> None | Some t' -> Some (Q.Dedup t')
    | Q.Prom t -> match ds t with None -> None | Some t' -> Some (Q.Prom t')
    | Q.Record fl ->
        let ofl = Map.toList fl >>== fun (z,qz) -> ds qz >>= fun qz' -> Some (z,qz') in
        match ofl with
        | None -> None
        | Some fl' -> Some (Q.Record (Map.ofList fl'))
    | Q.Project (t,f) -> 
        match ds t with
        | None -> None 
        | Some t' -> Some (Q.Project (t',f))
    (* XXX: assumes no Closures are left *)
    | _ -> None

let rec delateralize q =
    let q = Q.norm false Map.empty q in
    Printf.printfn "*** normalization step"
    Printf.printfn "%s\n" (Q.string_of_t q)
    match delateralize_step q with
    | Some q' -> 
        Printf.printfn "*** delateralization step"
        Printf.printfn "%s\n" (Q.string_of_t q')
        delateralize q'
    | None -> q