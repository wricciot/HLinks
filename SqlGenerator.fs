(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** SqlGenerator.fs - Sql syntax generation                                 **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)

module SqlGenerator

    open System.Text.RegularExpressions

    module Q = Query
    module C = Constant

    type index = (Var.var * string) list

    type query =
      | UnionAll  of query list * int
      | Select    of select_clause
      | With      of Var.var * query * Var.var * query
    and select_clause = (base_exp * string) list * (string * Var.var) list * base_exp * base_exp list
    and base_exp =
      | Case      of base_exp * base_exp * base_exp
      | Constant  of Constant.t
      | Project   of Var.var * string
      | Apply     of string * base_exp list
      | Empty     of query
      | Length    of query

    (* optimizing smart constructor for && *)
    let smart_and c c' =  
      match c, c' with
      (* optimisations *)
      | Constant (C.Bool true), c
      | c, Constant (C.Bool true) -> c
      | Constant (C.Bool false), _
      | _, Constant (C.Bool false) ->
            Constant (C.Bool false)
      (* default case *)
      | c, c' -> Apply ("&&", [c; c'])

    (* Table variables that are actually used are always bound in a for
       comprehension. In this case the IR variable from the for
       comprehension is used to generate the table variable.
       e.g. if the IR variable is 1485 then the table variable is t1485
    *)
    let fresh_table_var : unit -> Var.var = Var.fresh_raw_var
    let string_of_table_var var = "t" + string var
    let string_of_subquery_var var = "q" + string var

    (* Because of limitations of SQL we sometimes need to generate dummy
       table variables. These have the prefix "dummy" and have their own
       name source. *)
    let dummy_counter = ref 0
    let reset_dummy_counter () = dummy_counter := 0
    let fresh_dummy_var () =
      incr dummy_counter;
      "dummy" + string (!dummy_counter)

    let string_of_label label =
      if Regex.IsMatch(label, "[0-9]+") then
        "\"" + label + "\""     (* The SQL-standard way to quote an identifier;
                                   works in MySQL and PostgreSQL *)
      else
        label

    module Arithmetic =
          let private builtin_ops =
            Map.ofList
              [ "+",   Some "+"  ;
                "+.",  Some "+"  ;
                "-",   Some "-"  ;
                "-.",  Some "-"  ;
                "*",   Some "*"  ;
                "*.",  Some "*"  ;
                "/",   None      ;
                "^",   None      ;
                "^.",  None      ;
                "/.",  Some "/"  ;
                "mod", Some "%"  ;
                (* FIXME: The SQL99 || operator is supported in PostgreSQL and
                   SQLite but not in MySQL, where it denotes the logical or
                   operator *)
                "^^",  Some "||" ]

          let is x = Map.containsKey x builtin_ops
          let private sql_name op = Option.get (Map.find op builtin_ops)
          let gen (l, op, r) =
            match op with
              | "/" -> Printf.sprintf "floor(%s/%s)" l r
              | "^" -> Printf.sprintf "floor(pow(%s,%s))" l r
              | "^." -> Printf.sprintf "pow(%s,%s)" l r
              | _ -> Printf.sprintf "(%s%s%s)" l (sql_name op) r
    (* end module Arithmetic *)

    module SqlFuns =
      let private funs =
        Map.ofList
          [ "toUpper",  "upper";
            "toLower",  "lower";
            "ord",      "ord";
            "chr",      "char";
            "random",   "rand" ]

      let is f = Map.containsKey f funs
      let name f = Map.find f funs
    (* end module SqlFuns *)

    (* For Empty and Length we don't care about the actual data
       returned. This allows these operators to take lists that have any
       element type at all. *)

    let quote_field _ = failwith "quote_field"
    let mapstrcat sep f l = l |> List.map f |> String.concat sep

    let rec string_of_query_base ignore_fields q =
      let sq = string_of_query_base ignore_fields in
      let sb = string_of_base false in
      let string_of_fields fields =
        if ignore_fields then
          "0 as \"@unit@\"" (* SQL doesn't support empty records! *)
        else
          match fields with
            | [] -> "0 as \"@unit@\"" (* SQL doesn't support empty records! *)
            | fields -> 
                fields 
                |> mapstrcat "," (fun (b, l) -> Printf.sprintf "(%s) as %s" (sb b) (quote_field l))
      in
      let string_of_select fields tables condition =
        let tables = String.concat "," tables in
        let fields = string_of_fields fields in
        let where =
          match condition with
            | Constant (Constant.Bool true) -> ""
            | _ ->  " where " + sb condition
        in
          "select " + fields + " from " + tables + where
      in
        match q with
          | UnionAll ([], _) -> "select 42 as \"@unit@\" where false"
          | UnionAll ([q], _n) -> sq q // ^ order_by_clause n
          | UnionAll (qs, _n) ->
            mapstrcat " union all " (fun q -> "(" + sq q + ")") qs // ^ order_by_clause n
          | Select (fields, [], Constant (Constant.Bool true), _os) ->
              let fields = string_of_fields fields in
                "select " + fields
          | Select (fields, [], condition, _os) ->
              let fields = string_of_fields fields in
                "select * from (select " + fields + ") as " + fresh_dummy_var () + " where " + sb condition
          | Select (fields, tables, condition, _os) ->
              (* using quote_field assumes tables contains table names (not nested queries) *)
              let tables = List.map (fun (t, x) -> quote_field t + " as " + (string_of_table_var x)) tables
              in string_of_select fields tables condition
          | With (_, q, z, q') ->
              match q' with
              | Select (fields, tables, condition, os) ->
                  (* Inline the query *)
                  let tables = List.map (fun (t, x) -> quote_field t + " as " + (string_of_table_var x)) tables in
                  let q = "(" + sq q + ") as " + string_of_table_var z in
                  string_of_select fields (q::tables) condition
              | _ -> failwith "string_of_query"

    and string_of_base one_table b =
      let sb = string_of_base one_table in
        match b with
          | Case (c, t, e) ->
              "case when " + sb c + " then " + sb t + " else " + sb e + " end"
          | Constant c -> Constant.string_of_t c
          | Project (var, label) -> string_of_projection one_table (var, label)
          | Apply (op, [l; r]) when Arithmetic.is op ->
                Arithmetic.gen (sb l, op, sb r)
          | Apply (("intToString" | "stringToInt" | "intToFloat" | "floatToString" | "stringToFloat"), [v]) -> sb v
          | Apply ("floatToInt", [v]) -> "floor("+sb v+")"

          (* optimisation *)
          | Apply ("not", [Empty q]) -> "exists (" + string_of_query_base true q + ")"

          | Apply ("not", [v]) -> "not (" + sb v + ")"
          | Apply (("negate" | "negatef"), [v]) -> "-(" + sb v + ")"
          | Apply ("&&", [v; w]) -> "(" + sb v + ")" + " and " + "(" + sb w + ")"
          | Apply ("||", [v; w]) -> "(" + sb v + ")" + " or " + "(" + sb w + ")"
          | Apply ("==", [v; w]) -> "(" + sb v + ")" + " = " + "(" + sb w + ")"
          | Apply ("<>", [v; w]) -> "(" + sb v + ")" + " <> " + "(" + sb w + ")"
          | Apply ("<", [v; w]) -> "(" + sb v + ")" + " < " + "(" + sb w + ")"
          | Apply (">", [v; w]) -> "(" + sb v + ")" + " > " + "(" + sb w + ")"
          | Apply ("<=", [v; w]) -> "(" + sb v + ")" + " <= " + "(" + sb w + ")"
          | Apply (">=", [v; w]) -> "(" + sb v + ")" + " >= " + "(" + sb w + ")"
          | Apply ("RLIKE", [v; w]) -> "(" + sb v + ")" + " RLIKE " + "(" + sb w + ")"
          | Apply ("LIKE", [v; w]) -> "(" + sb v + ")" + " LIKE " + "(" + sb w + ")"
          | Apply (f, args) when SqlFuns.is f -> SqlFuns.name f + "(" + String.concat "," (List.map sb args) + ")"
          | Apply (f, args) -> f + "(" + String.concat "," (List.map sb args) + ")"
          | Empty q -> "not exists (" + string_of_query_base true q + ")"
          | Length q -> "select count(*) from (" + string_of_query_base true q + ") as " + fresh_dummy_var ()

    and string_of_projection one_table (var, label) =
      if one_table then
        quote_field label
      else
        string_of_table_var var + "." + (quote_field label)

    let string_of_query range q =
      let range =
        match range with
          | None -> ""
          | Some (limit, offset) -> " limit " + string limit + " offset " + string offset
      in
        string_of_query_base false q + range

    let rec select_clause : bool -> Q.t -> select_clause =
      fun unit_query v ->
      (*  Debug.print ("select_clause: "^string_of_t v); *)
      match v with
        | Q.Concat _ -> failwith "select_clause"
        | Q.For ([], body) ->
            select_clause unit_query body
        | Q.For ((x, Q.Table (table, _ft))::gs, body) ->
            let body = select_clause unit_query (Q.For (gs, body)) in
            begin
                match body with
                  | (fields, tables, condition, []) ->
                      (fields, (table, x)::tables, condition, [])
                  | _ -> failwith "select_clause"
            end
        | Q.If (c, body, Q.Concat []) ->
              (* Turn conditionals into where clauses. We might want to do
                 this earlier on.  *)
              let c = base_exp c in
              let (fields, tables, c', os) = select_clause unit_query body in
              let c = smart_and c c' in
              (fields, tables, c, os)
        | Q.Table (table, field_types) ->
              (* eta expand tables. We might want to do this earlier on.  *)
              (* In fact this should never be necessary as it is impossible
                 to produce non-eta expanded tables. *)
              let var = fresh_table_var () in
              let fields =
                List.rev
                  (Map.fold
                     (fun fields name _ ->
                       (Project (var, name), name)::fields)
                     [] 
                     field_types)
              in
              (fields, [(table, var)], Constant (Constant.Bool true), [])
        | Q.Singleton _ when unit_query ->
          (* If we're inside an Sql.Empty or a Sql.Length it's safe to ignore
             any fields here. *)
          (* We currently detect this earlier, so the unit_query stuff here
             is redundant. *)
          ([], [], Constant (Constant.Bool true), [])
        | Q.Singleton (Q.Record field_types) ->
          let fields =
            List.rev
              (Map.fold
                 (fun fields name v ->
                   (base_exp v, name)::fields)
                 []
                 field_types)
          in
            (fields, [], Constant (Constant.Bool true), [])
        | _ -> failwith "select_clause"
    and clause : bool -> Q.t -> query =
      fun unit_query v -> Select(select_clause unit_query v)
    and base_exp : Q.t -> base_exp =
      function
        | Q.If (c, t, e) -> Case (base_exp c, base_exp t, base_exp e)
        // we don't support LIKE in this prototype
        //| Q.Apply (Primitive "tilde", [s; r]) ->
        | Q.Apply (Q.Primitive "Empty", [v]) -> Empty (unit_query v)
        | Q.Apply (Q.Primitive "length", [v]) -> Length (unit_query v)
        | Q.Apply (Q.Primitive f, vs) -> Apply (f, List.map base_exp vs)
        | Q.Project (Q.Var (x, _field_types), name) -> Project (x, name)
        | Q.Constant c -> Constant c
        // we don't support indices in this prototype
        //| Primitive "index" ->
        | e ->
              Printf.printf "Not a base expression: %s" (Q.string_of_t e)
              failwith "base_exp"

    and unit_query v =
      let prepare_clauses : Q.t -> Q.t list =
        function
          | Q.Concat vs -> vs
          | v -> [v]
      in
      (* queries passed to Empty and Length
         (where we don't care about what data they return)
      *)
      UnionAll (List.map (clause true) (prepare_clauses v), 0)
    and sql_of_query v =
      clause false v

    type let_clause = Var.var * Q.t * Var.var * Q.t
    type let_query = let_clause list

    let extract_gens =
      function
        | Q.For (gs, _) -> gs
        | _ -> failwith "extract_gens"

    let let_clause : let_clause -> query =
      fun (q, outer, z, inner) ->
        let gs_out = extract_gens outer in
        let gs_in = extract_gens inner in
          With (q, clause false outer, z, clause false inner)

    let sql_of_let_query : let_query -> query =
      fun cs ->
        UnionAll (List.map (let_clause) cs, 0)