﻿(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** Query.fs - DB queries syntax and normalization                          **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)

module Query

  open System.Collections.Generic

  type computation = unit

  type tail_computation = unit

  let concat_map f l = List.concat (List.map f l)

  let runtime_type_error error = 
    failwith (Printf.sprintf "Runtime type error: %s.\n\
                              This should not happen if the type system / checker is correct.\n\
                              Please file a bug report."
      error)

  let query_error error = failwith (Printf.sprintf "Query error: %s." error)

  (*
   * we use the same constructors for set/bag Singleton, Concat, For
   * default semantics is bag, but within Prom it's set
   * (dually, within a Dedup it's bag again)
   *)
  type t =
  | Constant   of Constant.t
  | Primitive  of string
  | Var        of Var.var * Map<string, Types.datatype>
  | If         of t * t * t
  | Closure    of (Var.var list * t) * env
  | Apply      of t * t list
  | Singleton  of t
  | Concat     of t list
  | For        of (Var.var * t) list * t
  | Dedup      of t
  | Prom       of t
  | Record     of Map<string, t>
  | Project    of t * string
  | Table      of string * Map<string, Types.datatype>
  and env = Map<string, t>

  let bind env (x, t) = Map.add x t env
  (* this is according to the Links implementation, which allows bindingds in e2 to shadow those in e1*)
  let (++) (e1 : env) (e2 : env) = Map.fold (fun acc x t -> Map.add x t acc) e1 e2
  let lookup (env : env) v = Map.find v env

  let nil = Concat []
  
  // I daren't call this "pretty" printing but it'll do the job for now
  let rec string_of_t = function
  | Constant c -> Printf.sprintf "$%s" (Constant.string_of_t c)
  | Primitive s -> Printf.sprintf "@%s" s
  | Var (v,ft) -> Printf.sprintf "'%s" (Var.string_of_var v)
  | If (c,t,e) -> 
      Printf.sprintf "(if %s then %s else %s)"
        (string_of_t c) (string_of_t t) (string_of_t e)
  | Closure ((vs, body), _env) -> 
      Printf.sprintf "<<%s>>%s" (vs |> List.map Var.string_of_var |> String.concat ",") (string_of_t body)
  | Apply (t,us) -> 
      Printf.sprintf "%s(%s)"
        (string_of_t t) (us |> List.map string_of_t |> String.concat ",")
  | Singleton t -> Printf.sprintf "[%s]" (string_of_t t)
  | Concat ts -> Printf.sprintf "++[%s]" (ts |> List.map string_of_t |> String.concat ";")
  | For (gs, body) -> 
      Printf.sprintf "(for (%s) do %s)"
        (gs 
         |> List.map (fun (v,t) -> Printf.sprintf "%s <- %s" (Var.string_of_var v) (string_of_t t))
         |> String.concat ",")
        (string_of_t body)
  | Dedup t -> Printf.sprintf "δ%s" (string_of_t t)
  | Prom t -> Printf.sprintf "ι%s" (string_of_t t)
  | Record fields -> 
      Printf.sprintf "{%s}"
        (fields 
         |> Map.fold (fun acc name t -> (Printf.sprintf "%s := %s" name (string_of_t t))::acc) [] 
         |> String.concat ";")
  | Project (t,field) -> Printf.sprintf "%s.%s" (string_of_t t) field
  | Table (t,_) -> Printf.sprintf "&%s" t
  
  let rec contains_free fvs =
      let rec cfree bvs = function
      | Var (w,tyw) -> List.contains w fvs && not (List.contains w bvs)
      | If (c,t,e) -> cfree bvs c || cfree bvs t || cfree bvs e
      | Closure ((wl,b),e) ->
          // XXX: to be checked
          let bvs' = bvs @ wl @ List.map (fun (w,_) -> w) (Map.toList e) in
          cfree bvs' b || Map.exists (fun _ q -> cfree bvs q) e
      | Apply (t, args) -> cfree bvs t || List.exists (cfree bvs) args
      | Singleton t
      | Dedup t
      | Prom t
      | Project (t,_) -> cfree bvs t
      | Concat tl -> List.exists (cfree bvs) tl
      | For (gs, b) -> 
          let bvs'', res = List.fold (fun (bvs',acc) (w,q) -> w::bvs', acc || cfree bvs' q) (bvs, false) gs in
          res || cfree bvs'' b
      | Record fl -> Map.exists (fun _ t -> cfree bvs t) fl
      | _ -> false
      in cfree []
  

  let rec tail_of_t : t -> t = fun v ->
    let tt = tail_of_t in
    match v with
     | For (_gs, Singleton (Record fields)) -> Record fields
     | For (_gs, If (_, t, Concat [])) -> tt (For (_gs, t))
     | _ -> (* Debug.print ("v: "^string_of_t v); *) failwith "Query.tail_of_t"

  (** Return the type associated with an expression *)
  (* Inferring the type of an expression is straightforward because all
     variables are annotated with their types. *)
  let rec type_of_expression v : Types.datatype =
      let te = type_of_expression in
      let record fields : Types.datatype =
        Types.make_record_type (Map.map (fun _ -> te) fields)
      in
        match v with
          | Var (_,ftys) -> Types.make_record_type ftys
          | Concat [] -> Types.make_list_type(Types.unit_type)
          | Concat (v::_) -> te v
          | For (_,body) -> te body
          | Singleton t -> Types.make_list_type (te t)
          | Record fields -> record fields
          | If (_, t, _) -> te t
          | Dedup u
          | Prom u -> te u
          | Table (_, ftys) -> Types.make_record_type ftys
          | Constant (Constant.Bool   _) -> Types.bool_type
          | Constant (Constant.Int    _) -> Types.int_type
          | Constant (Constant.Char   _) -> Types.char_type
          | Constant (Constant.Float  _) -> Types.float_type
          | Constant (Constant.String _) -> Types.string_type
          //| Project (Var (_, field_types), name) -> Map.find name field_types
          | Project (w, name) -> 
            match te w with
            | Types.RcdTy field_types -> Map.find name field_types
            | _ -> failwith (Printf.sprintf "%s was expected to have record type, but it doesn't" (string_of_t w))
          | Apply _ | Primitive _ -> Types.unit_type    // HACKHACK
          | e -> failwith ("Can't deduce type for: " + string_of_t e)

  let field_types_of_record q =
    match type_of_expression q with
    | Types.RcdTy ftys -> ftys
    | _ -> failwith "Query.field_types_of_expression"

  let field_types_of_query q =
    match type_of_expression q with
    | Types.ListTy (Types.RcdTy ftys) -> ftys
    | _ -> failwith "Query.field_types_of_expression"

  let rec freshen_for_bindings : Map<string,Var.var> -> t -> t = fun env v -> 
    let ffb = freshen_for_bindings env in
      match v with
      | For (gs, b) ->
        let gs', env' =
          List.fold
            (fun (gs', env') (x, source) ->
              let y = Var.fresh_raw_var () in
                ((y, ffb source)::gs', bind env' (x,y)))
            ([], env)
            gs
        in
          For (List.rev gs', freshen_for_bindings env' b)
      | If (c, t, e) -> If (ffb c, ffb t, ffb e)
      | Table _ as t -> t
      | Singleton v -> Singleton (ffb v)
      | Concat vs -> Concat (List.map ffb vs)
      | Record fields -> Record (Map.map (fun _ -> ffb) fields)
      | Project (v, name) -> Project (ffb v, name)
      | Dedup v' -> Dedup (ffb v')
      | Prom v' -> Prom (ffb v')
      | Apply (u, vs) -> Apply (ffb u, List.map ffb vs)
      | Closure _ as c ->
        (* we don't attempt to freshen closure bindings *)
        c
      | Primitive _ -> v
      | Var (x, ts) ->
        begin
          match Map.tryFind x env with
          | None -> v (* Var (x, ts) *)
          | Some y -> Var (y, ts)
        end
      | Constant c -> Constant c

  let box_pair x y =
    [("1",x); ("2",y)]
    |> Map.ofList
    |> Record

  let flatfield f1 f2 = f1 + "@" + f2

  let rec flattened_pair x y = 
    match x, y with
    | Var (nx, ftx), _ ->
        let x' = Record (Map.fold (fun acc f _ -> Map.add f (Project (x,f)) acc) Map.empty ftx)
        in flattened_pair x' y
    | _, Var (ny, fty) ->
        let y' = Record (Map.fold (fun acc f _ -> Map.add f (Project (y,f)) acc) Map.empty fty)
        in flattened_pair x y'
    | Record fty1, Record fty2 ->
        let out1 = 
            Map.fold (fun acc f v -> Map.add (flatfield "1" f) v acc) Map.empty fty1
        in 
        let out2 = Map.fold (fun acc f v -> Map.add (flatfield "2" f) v acc) out1 fty2
        in Record out2
    | _ -> failwith "Query.flattened_pair"

  let flattened_pair_ft x y = 
    match x, y with
    | Var (nx, ftx), Var (ny, fty) -> 
        let out1 = 
            Map.fold (fun acc f t -> Map.add (flatfield "1" f) t acc) Map.empty ftx
        in 
        Map.fold (fun acc f t -> Map.add (flatfield "2" f) t acc) out1 fty
    | _ -> failwith "Query.flattened_pair_ft"

  let unbox_pair =
    function
      | Record fields ->
        let x = Map.find "1" fields in
        let y = Map.find "2" fields in
        x, y
      | _ -> raise (runtime_type_error "failed to unbox pair")

  let rec unbox_list =
    function
      | Concat vs-> concat_map unbox_list vs
      | Singleton v -> [v]
      | _ -> raise (runtime_type_error "failed to unbox list")

  let rec field_types_of_list = function
    | Concat (v::_) -> field_types_of_list v
    | Singleton (Record fields) -> Map.map (fun _ -> type_of_expression) fields
    | Table (table, ft) -> ft
    | _ -> failwith "Query.field_types_of_list"

(* takes a normal form expression and returns true iff it has list type *)
  let is_list = function
    | For _
    | Table _
    | Singleton _
    | Concat _
    | Dedup _
    | Prom _
    | If (_, _, Concat []) -> true
    | _ -> false


  (* simple optimisations *)
  let reduce_and (a, b) =
    match a, b with
    | Constant (Constant.Bool true), x
    | x, Constant (Constant.Bool true)
    | (Constant (Constant.Bool false) as x), _
    | _, (Constant (Constant.Bool false) as x) -> x
    | _ -> Apply  (Primitive "&&", [a; b])

  let reduce_or (a, b) =
    match a, b with
    | (Constant (Constant.Bool true) as x), _
    | _, (Constant (Constant.Bool true) as x)
    | Constant (Constant.Bool false), x
    | x, Constant (Constant.Bool false) -> x
    | _ -> Apply  (Primitive "||", [a; b])

  let reduce_not a =
    match a with
    | Constant (Constant.Bool false) -> Constant (Constant.Bool true)
    | Constant (Constant.Bool true)  -> Constant (Constant.Bool false)
    | _                       -> Apply  (Primitive "not", [a])

  let rec reduce_eq (a, b) =
    let bool x = Constant (Constant.Bool x) in
    let eq_constant = function
    | (Constant.Bool a  , Constant.Bool b)   -> bool (a = b)
    | (Constant.Int a   , Constant.Int b)    -> bool (a = b)
    | (Constant.Float a , Constant.Float b)  -> bool (a = b)
    | (Constant.Char a  , Constant.Char b)   -> bool (a = b)
    | (Constant.String a, Constant.String b) -> bool (a = b)
    | (a, b)                 -> Apply (Primitive "==", [Constant a; Constant b])
    in
    match a, b with
    | (Constant a, Constant b) -> eq_constant (a, b)
    | (Record lfields, Record rfields) ->
      List.foldBack2 (fun (_, v1) (_, v2) e -> reduce_and (reduce_eq (v1, v2), e))
          (Map.toList lfields)
          (Map.toList rfields)
        (Constant (Constant.Bool true))
    | (a, b) -> Apply (Primitive "==", [a; b])

  let reduce_concat vs =
    let vs = 
        concat_map (function 
        | Prom (Concat []) -> []
        | Prom (Singleton v) -> [v]
        | Concat vs -> vs 
        | v -> [v]) vs in
    match vs with
    | [v] -> v
    | vs -> Concat vs

  let field_types_of_for_var gen = 
    match type_of_expression gen with
    | Types.ListTy (Types.RcdTy ftys) -> ftys
    // BUGBUG can't synthesize a type for the variable (but then it probably doesn't matter)
    | _ -> Map.empty

  let rec reduce_where_then (c, t) =
    match t with
    (* optimisation *)
    | Constant (Constant.Bool true) -> t
    | Constant (Constant.Bool false) -> Concat []

    | Prom t' -> Prom (reduce_where_then (c, t'))
    | Concat vs ->
        reduce_concat (List.map (fun v -> reduce_where_then (c, v)) vs)
    | For (gs, body) ->
        For (gs, reduce_where_then (c, body))
    | If (c', t', Concat []) ->
        reduce_where_then (reduce_and (c, c'), t')
    | _ -> If (c, t, Concat [])

  let reduce_for_body (gs, body) =
    match body with
    | For (gs', body') -> For (gs @ gs', body')
    | _                         -> For (gs, body)

  let rec reduce_for_source : t * Types.datatype * (t -> t) -> t = 
    fun (source, ty, body) ->
    let rs = fun (source,ty) -> reduce_for_source (source, ty, body) in
    match source with
        | Singleton v -> body v
        | Concat vs ->
            reduce_concat (List.map (fun x -> rs (x,ty)) vs)
        | If (c, t, Concat []) ->
            reduce_for_source (t, ty, fun v-> reduce_where_then (c, body v))
        | For (gs, v) ->
        (* NOTE:
            We are relying on peculiarities of the way we manage
            the environment in order to avoid having to
            augment it with the generator bindings here.
            In particular, we rely on the fact that if a variable
            is not found on a lookup then we return the eta
            expansion of that variable rather than complaining that
            it isn't bound in the environment.
        *)
            let tyv = type_of_expression v in
            reduce_for_body (gs, rs (v,tyv))
        | Table (table, field_types) 
        | Dedup (Table (table, field_types)) ->
            (* we need to generate a fresh variable in order to
                correctly handle self joins *)
            let x = Var.fresh_raw_var () in
            (* Debug.print ("fresh variable: " ^ string_of_int x); *)
            reduce_for_body ([(x, source)], body (Var (x, field_types)))
        // BUGBUG: what should we do when we have a Prom?
        // BUGBUG the type of x is wrong: can we receive it as an argument?
        | Prom _ -> 
            let x = Var.fresh_raw_var () in 
            let field_types = field_types_of_for_var source
            in reduce_for_body ([(x,source)], body (Var (x, field_types)))
        | v -> query_error (Printf.sprintf "Bad source in for comprehension: %s" (string_of_t v))

  let rec reduce_if_body (c, t, e) =
    match t with
    | Record then_fields ->
        match e with
        | Record else_fields -> 
          assert (Map.fold (fun acc key _ -> (Map.tryFind key else_fields <> None) && acc) true then_fields);
          Record (Map.fold
             (fun fields name t ->
               let e = Map.find name else_fields in
                 Map.add name (reduce_if_body (c, t, e)) fields)
             Map.empty
             then_fields)        
        (* NOTE: this relies on any record variables having
           been eta-expanded by this point *)
        | _ -> query_error "Mismatched fields"
    | _ ->
        begin
        match t, e with
        | Constant (Constant.Bool true), _ ->
            reduce_or (c, e)
        | _, Constant (Constant.Bool false) ->
            reduce_and (c, t)
        | _ ->
            If (c, t, e)
        end

  let reduce_if_condition (c, t, e) =
    match c with
    | Constant (Constant.Bool true) -> t
    | Constant (Constant.Bool false) -> e
    | If (c', t', _) ->
        reduce_if_body (reduce_or (reduce_and (c', t'), reduce_and (reduce_not c', t')), t, e)
    | _ ->
        if is_list t then
            if e = nil then
                reduce_where_then (c, t)
            else
                reduce_concat [reduce_where_then (c, t);
                            reduce_where_then (reduce_not c, e)]
        else
        reduce_if_body (c, t, e)

//module Q = Lang

//let _show_env = Q.show_env (* Generated by ppx_deriving show *)

//(** Returns which database was used if any.
//   Currently this assumes that at most one database is used.
//*)
//let used_database v : Value.database option =
//  let rec generators =
//    function
//      | [] -> None
//      | (_x, source)::gs ->
//          begin
//            match used source with
//              | None -> generators gs
//              | Some db -> Some db
//          end
//  and used =
//    function
//      | Q.For (_, gs, _, _body) -> generators gs
//      | Q.Table ((db, _), _, _, _) -> Some db
//      | _ -> None in
//  let rec comprehensions =
//    function
//      | [] -> None
//      | v::vs ->
//          begin
//            match used v with
//              | None -> comprehensions vs
//              | Some db -> Some db
//          end
//  in
//    match v with
//      | Q.Concat vs -> comprehensions vs
//      | v -> used v

//let string_of_t = Q.string_of_t

//let labels_of_field_types field_types =
//  StringMap.fold
//    (fun name _ labels' ->
//      StringSet.add name labels')
//    field_types
//    StringSet.empty

//let record_field_types (t : Types.datatype) : Types.datatype StringMap.t =
//  let (field_spec_map, _, _) = TypeUtils.extract_row t in
//  StringMap.map (function
//                  | `Present t -> t
//                  | _ -> assert false) field_spec_map

//module Eval =
//struct
//  let env_of_value_env policy value_env =
//    let open Lang in
//    { venv = value_env; qenv = Env.Int.empty; policy }

//  let empty_env policy =
//    let open Lang in
//    { venv = Value.Env.empty; qenv = Env.Int.empty; policy }

//  let (++) e1 e2 =
//    let open Lang in
//    if (e1.policy <> e2.policy) then
//      raise (internal_error "Trying to append environments with different query policies")
//    else
//      let venv = Value.Env.shadow e1.venv ~by:e2.venv in
//      let qenv = Env.Int.extend e1.qenv e2.qenv in
//      { policy = e1.policy; venv; qenv }

//  let lookup_fun env (f, fvs) =
//    let open Q in
//    match Tables.lookup Tables.fun_defs f with
//    | Some (finfo, (xs, body), z, location) ->
//      Some
//      begin
//        match Var.name_of_binder (f, finfo) with
//        | "concatMap" ->
//          Q.Primitive "ConcatMap"
//        | "map" ->
//          Q.Primitive "Map"
//        | "empty" ->
//          Q.Primitive "Empty"
//        | "sortByBase" ->
//          Q.Primitive "SortBy"
//        | _ ->
//          begin
//            match location with
//            | Location.Server | Location.Unknown ->
//                let env' =
//                  match z, fvs with
//                  | None, None       -> Value.Env.empty
//                  | Some z, Some fvs -> Value.Env.bind z (fvs, Scope.Local) Value.Env.empty
//                  | _, _ -> assert false in
//                Closure ((xs, body), env_of_value_env env.policy env')
//            | Location.Client ->
//              raise (Errors.runtime_error ("Attempt to use client function: " ^
//                Js.var_name_binder (f, finfo) ^ " in query"))
//          end
//      end
//    | None -> None

//  let find_fun env (f, fvs) =
//    match lookup_fun env (f, fvs) with
//    | Some v -> v
//    | None ->
//      raise (internal_error ("Attempt to find undefined function: " ^
//        string_of_int f))

//  let rec expression_of_value : Lang.env -> Value.t -> Q.t = fun env v ->
//    let open Q in
//    match v with
//      | `Bool b   -> Constant (Constant.Bool b)
//      | `Int i    -> Constant (Constant.Int i)
//      | `Char c   -> Constant (Constant.Char c)
//      | `Float f  -> Constant (Constant.Float f)
//      | `String s -> Constant (Constant.String s)
//      | `Table t -> Table t
//      | `Database db -> Database db
//      | `List vs ->
//          Concat (List.map (fun v -> Singleton (expression_of_value env v)) vs)
//      | `Record fields ->
//          Q.Record
//            (List.fold_left
//               (fun fields (name, v) -> StringMap.add name (expression_of_value env v) fields)
//               StringMap.empty
//               fields)
//      | `Variant (name, v) -> Variant (name, expression_of_value env v)
//      | `XML xmlitem -> XML xmlitem
//      | `FunctionPtr (f, fvs) -> find_fun env (f, fvs)
//      | `PrimitiveFunction (f,_) -> Primitive f
//      | v ->
//          raise (internal_error (Printf.sprintf
//              "Cannot convert value %s to expression" (Value.string_of_value v)))


//  let bind env (x, v) =
//    let open Lang in
//    { env with qenv = Env.Int.bind x v env.qenv }

//  let lookup env var =
//    let open Lang in
//    let val_env = env.venv in
//    let exp_env = env.qenv in
//    match lookup_fun env (var, None) with
//    | Some v -> v
//    | None ->
//      begin
//        match Value.Env.lookup var val_env, Env.Int.find_opt var exp_env with
//        | None, Some v -> v
//        | Some v, None -> expression_of_value env v
//        | Some _, Some v -> v (*query_error "Variable %d bound twice" var*)
//        | None, None ->
//          begin
//            try expression_of_value env (Lib.primitive_stub (Lib.primitive_name var)) with
//            | NotFound _ ->
//                raise (internal_error ("Variable " ^ string_of_int var ^ " not found"));
//          end
//      end

  let eta_expand_var (x, field_types) =
    Record
      (Map.fold
         (fun fields name _t ->
            Map.add name (Project (Var (x, field_types), name)) fields)
         Map.empty
         field_types)

  let eta_expand_list xs =
    let x = Var.fresh_raw_var () in
    let field_types = field_types_of_list xs in
      ([x, xs], [], Singleton (eta_expand_var (x, field_types)))

//  let reduce_artifacts = function
//  | Q.Apply (Q.Primitive "stringToXml", [u]) ->
//    Q.Singleton (Q.XML (Value.Text (Q.unbox_string u)))
//  | Q.Apply (Q.Primitive "AsList", [xs]) -> xs
//  | u -> u

//  let check_policies_compatible env_policy block_policy =
//    let open QueryPolicy in
//    let resolve = function
//      | Flat -> `Flat
//      | Nested -> `Nested
//      | Default ->
//          if (Settings.get Database.shredding) then `Nested else `Flat in
//    let show = function | `Nested -> "nested" | `Flat -> "flat" in
//    let expected = resolve env_policy in
//    let actual = resolve block_policy in
//    if expected = actual then () else
//      let error = Printf.sprintf
//        "Incompatible query evaluation annotations. Expected %s, got %s."
//        (show expected) (show actual) in
//      raise (Errors.runtime_error error)

//  let rec xlate env : Ir.value -> Q.t = let open Ir in function
//    | Constant c -> Q.Constant c
//    | Variable var ->
//        begin
//          match lookup env var with
//            | Q.Var (x, field_types) ->
//                (* eta-expand record variables *)
//                eta_expand_var (x, field_types)
//            | Q.Primitive "Nil" -> Q.nil
//            (* We could consider detecting and eta-expand tables here.
//               The only other possible sources of table values would
//               be `Special or built-in functions that return table
//               values. (Currently there are no pure built-in functions
//               that return table values.)
//               Currently eta-expansion happens later, in the SQL
//               module.
//               On second thoughts, we *never* need to explicitly
//               eta-expand tables, as it is not possible to call
//               "AsList" directly. The "asList" function in the prelude
//               is defined as:
//               fun asList(t) server {for (x <-- t) [x]}
//            *)
//            | v ->
//              (* In order to maintain the invariant that each
//                 bound variable is unique we freshen all for-bound
//                 variables in v here.
//                 This is necessary in order to ensure that each
//                 instance of a table in a self-join is given a
//                 distinct alias, as the alias is generated from the
//                 name of the variable binding the table.
//                 We are assuming that any closure-bound variables will
//                 be eliminated anyway.
//              *)
//              (* Debug.print ("env v: "^string_of_int var^" = "^string_of_t v); *)
//              Q.freshen_for_bindings (Env.Int.empty) v
//        end
//    | Extend (ext_fields, r) ->
//      begin
//        match opt_app (xlate env) (Q.Record StringMap.empty) r with
//          | Q.Record fields ->
//            Q.Record (StringMap.fold
//                       (fun label v fields ->
//                         if StringMap.mem label fields then
//                           query_error
//                             "Error adding fields: label %s already present"
//                             label
//                         else
//                           StringMap.add label (xlate env v) fields)
//                       ext_fields
//                       fields)
//          | _ -> query_error "Error adding fields: non-record"
//      end
//    | Project (label, r) -> Q.Project (xlate env r, label)
//    | Erase (labels, r) -> Q.Erase (xlate env r, labels)
//    | Inject (label, v, _) -> Q.Variant (label, xlate env v)
//    | TAbs (_, v) -> xlate env v
//    | TApp (v, _) -> xlate env v

//    | XmlNode (tag, attrs, children) ->
//        (* TODO: deal with variables in XML *)
//        let children =
//          List.fold_right
//            (fun v children ->
//               let v = xlate env v in
//               List.map Q.unbox_xml (Q.unbox_list v) @ children)
//            children [] in
//        let children =
//          StringMap.fold
//            (fun name v attrs ->
//               Value.Attr (name, Q.unbox_string (xlate env v)) :: attrs)
//            attrs children
//        in
//          Q.Singleton (Q.XML (Value.Node (tag, children)))

//    | ApplyPure (f, ps) ->
//        reduce_artifacts (Q.Apply (xlate env f, List.map (xlate env) ps))
//    | Closure (f, _, v) ->
//      let open Lang in
//      let (_finfo, (xs, body), z_opt, _location) = Tables.find Tables.fun_defs f in
//      let z = OptionUtils.val_of z_opt in
//      (* Debug.print ("Converting evalir closure: " ^ Var.show_binder (f, _finfo) ^ " to query closure"); *)
//      (* yuck! *)
//      let env' = bind (empty_env env.policy) (z, xlate env v) in
//      Q.Closure ((xs, body), env')
//      (* (\* Debug.print("looking up query closure: "^string_of_int f); *\) *)
//      (* begin *)
//      (*   match value env (`Variable f) with *)
//      (*   | `Closure ((z::xs, body), closure_env) -> *)
//      (*     (\* Debug.print("binding query closure parameter: "^string_of_int z); *\) *)
//      (*     (\* partially apply the closure to bind the closure *)
//      (*        environment *\) *)
//      (*     `Closure ((xs, body), bind closure_env (z, value env v)) *)
//      (*   | _ -> *)
//      (*     failwith "ill-formed closure in query compilation" *)
//      (* end *)
//    | Coerce (v, _) -> xlate env v

//  and computation env (binders, tailcomp) : Q.t =
//    let open Ir in
//    match binders with
//      | [] -> tail_computation env tailcomp
//      | b::bs ->
//          begin
//            match b with
//              | Let (xb, (_, tc)) ->
//                  let x = Var.var_of_binder xb in
//                    computation (bind env (x, tail_computation env tc)) (bs, tailcomp)
//              | Fun (_, _, _, Location.Client) ->
//                  query_error "Client function"
//              | Fun ((f, _), _, _, _) ->
//                (* This should never happen now that we have closure conversion*)
//                raise (internal_error
//                  ("Function definition in query: " ^ string_of_int f ^
//                   ". This should have been closure-converted."))
//              | Rec _ ->
//                  query_error "Recursive function"
//              | Alien _ -> (* just skip it *)
//                  computation env (bs, tailcomp)
//              | Module _ -> raise (internal_error "Not implemented modules yet")
//          end
//  and tail_computation env : Ir.tail_computation -> Q.t = let open Ir in function
//    | Return v -> xlate env v
//    | Apply (f, args) ->
//        reduce_artifacts (Q.Apply (xlate env f, List.map (xlate env) args))
//    | Special (Ir.Query (None, policy, e, _)) ->
//        let open Lang in
//        check_policies_compatible env.policy policy;
//        computation env e
//    | Special (Ir.Table (db, name, keys, (readtype, _, _))) as _s ->
//       (** WR: this case is because shredding needs to access the keys of tables
//           but can we avoid it (issue #432)? *)
//       (* Copied almost verbatim from evalir.ml, which seems wrong, we should probably call into that. *)
//       begin
//         match xlate env db, xlate env name, xlate env keys, (TypeUtils.concrete_type readtype) with
//         | Q.Database (db, params), name, keys, `Record row ->
//        let unboxed_keys =
//          List.map
//        (fun key ->
//         List.map Q.unbox_string (Q.unbox_list key))
//        (Q.unbox_list keys)
//        in
//            Q.Table ((db, params), Q.unbox_string name, unboxed_keys, row)
//         | _ -> query_error "Error evaluating table handle"
//       end
//    | Special _s ->
//      (* FIXME:
//         There's no particular reason why we can't allow
//         database declarations in query blocks. (However, we do still
//         have the problem that we currently have no way of enforcing
//         that only one database be used inside a query block - see
//         SML#.)  *)
//      raise (Errors.runtime_error "special not allowed in query block")
//    | Case (v, cases, default) ->
//        let v' = xlate env v in
//        let cases' = StringMap.map (fun (x,y) -> (x, computation env y)) cases in
//        let default' = opt_app (fun (x,y) -> Some (x, computation env y)) None default in
//        Q.Case (v', cases', default')
//    | If (c, t, e) ->
//      let c = xlate env c in
//      let t = computation env t in
//      let e = computation env e in
//        Q.If (c, t, e)

  let rec norm in_dedup env : t -> t = function
    | Var (var, _) ->
        begin
          match lookup env var with
            // XXX it should never be in_dedup, should it?
            | Var (x, field_types) when not in_dedup ->
                (* eta-expand record variables *)
                eta_expand_var (x, field_types)
            (* We could consider detecting and eta-expand tables here.
               The only other possible sources of table values would
               be `Special or built-in functions that return table
               values. (Currently there are no pure built-in functions
               that return table values.)
               Currently eta-expansion happens later, in the SQL
               module.
               On second thoughts, we *never* need to explicitly
               eta-expand tables, as it is not possible to call
               "AsList" directly. The "asList" function in the prelude
               is defined as:
               fun asList(t) server {for (x <-- t) [x]}
            *)
            | v ->
              (* In order to maintain the invariant that each
                 bound variable is unique we freshen all for-bound
                 variables in v here.
                 This is necessary in order to ensure that each
                 instance of a table in a self-join is given a
                 distinct alias, as the alias is generated from the
                 name of the variable binding the table.
                 We are assuming that any closure-bound variables will
                 be eliminated anyway.
              *)
              (* Debug.print ("env v: "^string_of_int var^" = "^string_of_t v); *)
                freshen_for_bindings Map.empty (retn in_dedup v)
        end
    | Record fl -> Record (Map.map (fun _ -> norm false env) fl)
    | Singleton u -> Singleton (norm false env u)
    | Concat xs -> reduce_concat (List.map (norm in_dedup env) xs)
    | Project (r, label) as orig ->
        let rec project (r, label) = 
          match r with
          | Record fields ->
              assert (Map.containsKey label fields);
              Map.find label fields
          | If (c, t, e) -> If (c, project (t, label), project (e, label))
          | Var (_x, field_types) ->
              assert (Map.containsKey label field_types);
              Project (r, label)
          | Project _ -> Project (r, label) 
          | _ -> query_error (Printf.sprintf ("Error projecting from record: %s\nOriginal term: %s") (string_of_t r) (string_of_t orig))
        in
        retn in_dedup (project (norm false env r, label))
    | Apply (f, xs) -> apply in_dedup env (norm false env f, List.map (norm false env) xs)
    | For (gs, u) -> 
        let rec reduce_gs env = function
        | [] -> 
            match norm in_dedup env u with
            // this special case allows us to hoist a non-standard For body into a generator
            | Prom _ as u' ->
                let z = Var.fresh_raw_var () in
                let tyz = type_of_expression u' in
                let ftz = field_types_of_for_var u' in
                let vz = Var (z, ftz) in
                reduce_for_source (u', tyz, fun v -> norm in_dedup (bind env (z,v)) (Singleton vz))
            | u' -> u'
        | (x,g)::gs' -> (* equivalent to xs = For gs' u, body = g, but possibly the arguments aren't normalized *)
            let tyg = type_of_expression g in
            reduce_for_source (norm in_dedup env g, tyg, fun v -> reduce_gs (bind env (x,v)) gs')
        in
        reduce_gs env gs
    | If (c, t, e) ->
        reduce_if_condition (norm false env c, norm in_dedup env t, norm in_dedup env e)
    | Dedup v -> norm true env v
    | Prom v when in_dedup -> norm false env v
    | Prom v (* when not in_dedup *) -> 
        //match norm false env v with
        //| Singleton _ | Concat [] as u -> u
        //| u -> Prom u
        Prom (norm false env v)
    | v -> retn in_dedup v

  and apply in_dedup env : t * t list -> t = function
    | Closure ((xs, body), closure_env), args ->
      (* Debug.print ("Applying closure"); *)
      (* Debug.print ("body: " ^ Ir.show_computation body); *)
      (* Debug.print("Applying query closure: " ^ show_t (`Closure ((xs, body), closure_env))); *)
      (* Debug.print("args: " ^ mapstrcat ", " show_t args); *)
        let env = env ++ closure_env in
        let env = List.foldBack2 (fun x arg env ->
            bind env (x, arg)) xs args env in
        (* Debug.print("Applied"); *)
          norm in_dedup env body
    // in_dedup shouldn't happen with primitives that don't return collections so we ignore it
    | Primitive "not", [v] ->
      reduce_not (v)
    | Primitive "&&", [v; w] ->
      reduce_and (v, w)
    | Primitive "||", [v; w] ->
      reduce_or (v, w)
    | Primitive "==", [v; w] ->
      reduce_eq (v, w)
    | Primitive f, args ->
        Apply (Primitive f, args) |> retn in_dedup
    | If (c, t, e), args ->
        reduce_if_condition (c, apply in_dedup env (t, args), apply in_dedup env (e, args))
    | Apply (f, args), args' ->
        apply in_dedup env (f, args @ args')
    | t, _ -> query_error (Printf.sprintf "Application of non-function: %s" (string_of_t t))
  and dedup = function
    | Prom u -> u
    | Singleton _ | Concat [] as u -> u
    | For (gs, u) -> For ([ for (x,g) in gs -> (x, dedup g) ], dedup u)
    | If (c, t, e) -> If (c, dedup t, dedup e)
    | Var _ | Table _ as u -> Dedup u (* Dedup NFs allowed on tables/variables *)
    // XXX normally this should never happen, so an error would be ok; 
    // however for testing purposes it is sometimes desirable to have ill-formed queries;
    // just make sure to revert this code
    // | u -> query_error (Printf.sprintf ("Error deduplicating bag: %s") (string_of_t u))
    | u -> Dedup u
  and retn in_dedup u = if in_dedup then Dedup u else u

//  let eval policy env e =
//(*    Debug.print ("e: "^Ir.show_computation e); *)
//    Debug.debug_time "Query.eval" (fun () ->
//      norm_comp (env_of_value_env policy env) e)
//end

//(* The following code is specific to nested queries *)
//(* The index parameter is essentially a free variable in the query
//   that can only be replaced by Sql.RowNumber index.
//   It would be nice to be able to remove this parameter and just
//   substitute the SQL RowNumber expression when we generate SQL.
//   Then the following nesting-specific code could live somewhere else, such as
//   evalNestedQuery. *)




//let update : Value.database -> ((Ir.var * string) * Q.t option * Q.t) -> string =
//  fun db ((_, table), where, body) ->
//    Sql.reset_dummy_counter ();
//    let base = (base []) ->- (Sql.string_of_base db true) in
//    let where =
//      match where with
//        | None -> ""
//        | Some where ->
//            " where (" ^ base where ^ ")" in
//    let fields =
//      match body with
//        | Q.Record fields ->
//            String.concat ","
//              (List.map
//                (fun (label, v) -> db#quote_field label ^ " = " ^ base v)
//                (StringMap.to_alist fields))
//        | _ -> assert false
//    in
//      "update "^table^" set "^fields^where

//let delete : Value.database -> ((Ir.var * string) * Q.t option) -> string =
//  fun db ((_, table), where) ->
//  Sql.reset_dummy_counter ();
//  let base = base [] ->- (Sql.string_of_base db true) in
//  let where =
//    match where with
//      | None -> ""
//      | Some where ->
//          " where (" ^ base where ^ ")"
//  in
//    "delete from "^table^where

//let compile_update : Value.database -> Value.env ->
//  ((Ir.var * string * Types.datatype StringMap.t) * Ir.computation option * Ir.computation) -> string =
//  fun db env ((x, table, field_types), where, body) ->
//    let env = Eval.bind (Eval.env_of_value_env QueryPolicy.Default env) (x, Q.Var (x, field_types)) in
//(*      let () = opt_iter (fun where ->  Debug.print ("where: "^Ir.show_computation where)) where in*)
//    let where = opt_map (Eval.norm_comp env) where in
//(*       Debug.print ("body: "^Ir.show_computation body); *)
//    let body = Eval.norm_comp env body in
//    let q = update db ((x, table), where, body) in
//      Debug.print ("Generated update query: "^q);
//      q

//let compile_delete : Value.database -> Value.env ->
//  ((Ir.var * string * Types.datatype StringMap.t) * Ir.computation option) -> string =
//  fun db env ((x, table, field_types), where) ->
//    let env = Eval.bind (Eval.env_of_value_env QueryPolicy.Default env) (x, Q.Var (x, field_types)) in
//    let where = opt_map (Eval.norm_comp env) where in
//    let q = delete db ((x, table), where) in
//      Debug.print ("Generated update query: "^q);
//      q

//let is_list = Q.is_list
//let table_field_types = Q.table_field_types
//let value_of_expression = Q.value_of_expression
//let default_of_base_type = Q.default_of_base_type
//let type_of_expression = Q.type_of_expression
//let unbox_xml = Q.unbox_xml
//*)

