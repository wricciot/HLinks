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
      | Union     of bool * query list      (* is_set? *)
      | Select    of bool * select_clause   (* is_set? *)
      | With      of Var.var * query * Var.var * query
    and select_clause = (base_exp * string) list * (from_clause * Var.var) list * base_exp
    and from_clause =
      | FromQuery      of bool * query      (* is_lateral? *)
      | FromTable      of string
      | FromDedupTable of string 
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

    // from the Postgres driver, other DBMS may have it different
    let quote_field f = 
        "\"" + Regex.Replace(f, "\"", "\"\"") + "\""

    let mapstrcat sep f l = l |> List.map f |> String.concat sep

    // convert an NRC-style query into an SQL-style query
    let rec sql_of_query is_set = function
    | Q.Concat ds -> Union (is_set, List.map (disjunct is_set) ds)
    | q -> disjunct is_set q

    and disjunct is_set = function
    | Q.Prom p -> sql_of_query true p
    | Q.For (gs, j) ->
        let _, froms =
            List.fold (fun (locvars,acc) (v,_q as g) -> (v::locvars, generator locvars g::acc)) ([],[]) gs
        in
        let selects, where = body j in
        Select (is_set, (selects, List.rev froms, where))
    | _ -> failwith "disjunct"

    and generator locvars = function
    | (v, Q.Prom p) -> (FromQuery (Q.contains_free locvars p, sql_of_query true p), v)
    | (v, Q.Table (tname, _)) -> (FromTable tname, v)
    | (v, Q.Dedup (Q.Table (tname, _))) -> (FromDedupTable tname, v)
    | _ -> failwith "generator"

    and body = function
    | Q.Singleton (Q.Record fields) ->
        (List.map (fun (f,x) -> (base_exp x, f)) (Map.toList fields), Constant (Constant.Bool true))
    | Q.If (c, Q.Singleton (Q.Record fields), Q.Concat []) -> 
        let c' = base_exp c in
        let t = List.map (fun (f,x) -> (base_exp x, f)) (Map.toList fields) in
        (t, c')
    | _ -> failwith "body"

    and base_exp = function
    | Q.Project ((Q.Table (n, _) | Q.Var (n,_)), l) -> Project (n,l)
    | Q.If (c, t, e) -> Case (base_exp c, base_exp t, base_exp e)
    // we don't support LIKE in this prototype
    //| Q.Apply (Primitive "tilde", [s; r]) ->
    | Q.Apply (Q.Primitive "Empty", [v]) -> Empty (sql_of_query false v)
    | Q.Apply (Q.Primitive "length", [v]) -> Length (sql_of_query false v)
    | Q.Apply (Q.Primitive f, vs) -> Apply (f, List.map base_exp vs)
    | Q.Constant c -> Constant c
    // we don't support indices in this prototype
    //| Primitive "index" ->
    | e ->
          Printf.printf "Not a base expression: %s" (Q.string_of_t e)
          failwith "base_exp"

    // Raw SQL string generation
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
      let selectstr is_set = 
          if is_set then "select distinct " else "select " 
      in
      let unionstr is_set = 
          if is_set then " union " else " union all " 
      in
      let lateralstr is_lat =
        if is_lat then "lateral " else ""
      in
      let string_of_select is_set fields tables condition =
        let tables = String.concat "," tables in
        let fields = string_of_fields fields in
        let where =
          match condition with
            | Constant (Constant.Bool true) -> ""
            | _ ->  " where " + sb condition
        in
          selectstr is_set + fields + " from " + tables + where
      in
      let string_of_from_clause = function
      | FromTable n -> quote_field n
      | FromDedupTable n -> "(select distinct * from " + quote_field n + ")"
      | FromQuery (is_lat, q) -> lateralstr is_lat + "(" + sq q + ")"
      in
        match q with
          // is_set is only meaningful for proper Unions of two or more clauses
          | Union (_is_set, []) -> 
                "select 42 as \"@unit@\" where false"
          | Union (_is_set, [q]) -> sq q // ^ order_by_clause n
          | Union (is_set, qs) ->
                mapstrcat (unionstr is_set) (fun q -> "(" + sq q + ")") qs // ^ order_by_clause n
          | Select (is_set, (fields, [], Constant (Constant.Bool true))) ->
              let fields = string_of_fields fields in
                selectstr is_set + fields
          | Select (is_set, (fields, [], condition)) ->
              let fields = string_of_fields fields in
                selectstr is_set + "* from (select " + fields + ") as " + fresh_dummy_var () + " where " + sb condition
          | Select (is_set, (fields, tables, condition)) ->
              let tables = List.map (fun (t, x) -> string_of_from_clause t + " as " + (string_of_table_var x)) tables
              in string_of_select is_set fields tables condition
          | With (_, q, z, q') ->
              match q' with
              | Select (is_set, (fields, tables, condition)) ->
                  (* Inline the query *)
                  let tables = List.map (fun (t, x) -> string_of_from_clause t + " as " + (string_of_table_var x)) tables in
                  let q = "(" + sq q + ") as " + string_of_table_var z in
                  string_of_select is_set fields (q::tables) condition
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

    let string_of_query q = string_of_query_base false q