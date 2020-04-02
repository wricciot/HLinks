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
let graph_query (q1,ty1) x (q2,ty2) =
    let y = Var.fresh_raw_var () in
    Q.For ([(x, q1); (y, q2)], 
        Q.Singleton (
            Q.Record (Q.box_pair (Q.Var (x,ty1)) (Q.Var (y,ty2)))))

// DELATERALIZING REWRITE for iota
// for gs, y :- I(q3) do q1     -- s.t. x :- q2 in gs
//  ~> for gs, p :- I(C(Dq2,x.q3)) where x = p.1 do ([y]q1) p.2
let prom_delateralize gs q1 x (q2,ty2) y (q3,ty3) =
    let p = Var.fresh_raw_var () in
    // FIXME types of 1 and 2 should be RecordType ty2, RecordType ty3
    let typ = [("1",());("2",())] |> Map.ofList in
    let vp = Q.Var (p,typ) in
    let eq_query a b = Q.Apply (Q.Primitive "==", [a;b]) in
    Q.For (gs @ [(p, Q.Prom (graph_query (Q.Dedup q2,ty2) x (q3,ty3)))],
        Q.If (eq_query (Q.Var (x,ty2)) (Q.Project (vp, "1")),
            Q.Apply (Q.Closure (([y], q1), Map.empty),
                [Q.Project (vp,"2")]),
            Q.nil))

// TODO
let occurs_free (v : Var.var) (q : Q.t) : bool = failwith "Delateralize.occurs_free"
let occurs_free_list (vl : (Var.var * Q.t) list) (q : Q.t) : 'a option = failwith "Delateralize.occurs_free_list"

// returns None if q is already delateralized
// returns Some q' if q simplifies to a less lateral q'
let rec prom_lateral_search q =
    let pls = prom_lateral_search in
    match q with
    | Q.For (gs, q) -> 
        let rec findgs gsx = function
        | (y,Q.Prom qy as gy)::gsy -> 
            match occurs_free_list gsx qy with 
            // tail-consing is annoying, but occurs_free_list needs arguments in this order
            | None -> findgs (gsx@[gy]) gsy
            | Some (x,qx,tyx) -> Some (gsx,x,qx,tyx,y,qy,gsy)
        | gy::gsy -> findgs (gy::gsx) gsy
        | [] -> None
        in
        match findgs [] gs with
        | Some (gsx,x,qx,tyx,y,qy,gsy) ->
            let qf = Q.For (gsy,q) in
            let tyy = tyx in    // FIXME!!! how can I deduce the type of y?
            Some (prom_delateralize gsx qf x (qx,tyx) y (qy,tyy))
        | None ->
            let ogs = gs >>== (fun (z,qz) -> pls qz >>= fun qz' -> Some (z,qz')) in
            let oq = pls q in
            match ogs, oq with
            | None, None -> None
            | _ -> Some (Q.For (unopt_default ogs gs, unopt_default oq q))
    | Q.If (c,t,e) -> 
        match pls c, pls t, pls e with
        | None, None, None -> None
        | c', t', e' -> Some (Q.If (unopt_default c' c, unopt_default t' t, unopt_default e' e))
    // XXX: can t in Apply (t,...) even contain a For? however let's perform recursion for safety
    | Q.Apply (t,args) -> 
        let ot = pls t in
        let oargs = args >>== pls in
        match ot, oargs with
        | None, None -> None
        | _ -> Some (Q.Apply (unopt_default ot t, unopt_default oargs args))
    | Q.Singleton t -> match pls t with None -> None | Some t' -> Some (Q.Singleton t')
    | Q.Concat tl -> match tl >>== pls with None -> None | Some tl' -> Some (Q.Concat tl')
    | Q.Dedup t -> match pls t with None -> None | Some t' -> Some (Q.Dedup t')
    | Q.Prom t -> match pls t with None -> None | Some t' -> Some (Q.Prom t')
    | Q.Record fl ->
        let ofl = Map.toList fl >>== fun (z,qz) -> pls qz >>= fun qz' -> Some (z,qz') in
        match ofl with
        | None -> None
        | Some fl' -> Some (Q.Record (Map.ofList fl'))
    | Q.Project (t,f) -> 
        match pls t with
        | None -> None 
        | Some t' -> Some (Q.Project (t',f))
    (* XXX: assumes no Closures are left *)
    | _ -> None