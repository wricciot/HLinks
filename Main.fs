﻿(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** Main.fs - Program entry point and tests                                 **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)
module Main

open Query

let dummy = Types.int_type
let sItems = [("name",dummy); ("quantity",dummy)] |> Map.ofList 
let sOrders = [("oid",dummy); ("item",dummy); ("quantity",dummy)] |> Map.ofList
let tbItems = Table ("Items", sItems)
let tbOrders = Table ("Orders", sOrders)

(*
  distinct
    for o <- tbOrders do
    for i <- tbItems do
      if (i.quantity < o.quantity) then [{ badorder := o.name}]
*)
let qTest = 
  Prom (Dedup 
    (For (["o", tbOrders],
      (For (["i", tbItems],
        If (Apply (Primitive "<", [Project (Var ("o", sOrders), "quantity"); Project (Var ("i", sItems), "quantity")]),
          Singleton (Record (["badorder", Project (Var ("o", sOrders), "oid")] |> Map.ofList)),
          nil))))))

(*
for x <- table, y <- ID(for z <- ID(Singleton (const(x))) do const(z)) do const(x,y)
*)

let tyX = [("fx",dummy)] |> Map.ofList
let var x = Var (x, tyX)
let vx = var "x"
let vy = var "y"
let vz = var "z"

let tbDelat = Table ("TableX", [("fx",dummy)] |> Map.ofList)
// wraps a query so that it cannot be normalized out
let blobOf q = For (["x'", tbDelat], Singleton q) |> Dedup |> Prom

let qDelat = 
    For ([("x1", tbDelat) 
         ;("x2", Prom (Dedup (For (["z", blobOf (var "x1")], Singleton (var "z")))))],
        blobOf (Apply (Primitive "opaque4", [var "x1"; var "x2"])))

let qDelatNested =
    let pairx3 = flattened_pair (var "z1") (var "z2") in
    let ftyx3 = field_types_of_record pairx3 in
    let vx3 = Var ("x3", ftyx3) in
    let pairx4 = flattened_pair (var "z1") vx3 in
    let ftyx4 = field_types_of_record pairx4 in
    let vx4 = Var ("x4", ftyx4) in
    let vz3 = Var ("z3", ftyx3) in
    For ([("x1", tbDelat) 
         ;("x2", Prom (Dedup (For (["z", blobOf (var "x1")], Singleton (var "z")))))
         ;("x3", Prom (Dedup (For ([("z1", blobOf (var "x1")); ("z2", blobOf (var "x2"))], Singleton (flattened_pair (var "z1") (var "z2"))))))
         ;("x4", Prom (Dedup 
                (For ([("z1", blobOf (var "x1")); ("z2", blobOf (var "x2")); ("z3", blobOf vx3)], 
                    Singleton (flattened_pair (var "z1") (flattened_pair (var "z2") vz3))))))],
        blobOf vx4)

(* for (x <- Table, z <- prom (for y <- dedup Table) when x.a = y.a [(a = x.a)]) [(a = z.a)]
*)

let qDelatSimple =
    For ([("x", tbDelat)
         ;("z", Prom
            (For ([("y", Dedup tbDelat)], 
                If (Apply (Primitive "==", [Project (var "x", "fx"); Project (var "y", "fx")]),
                    Singleton (Record (Map.ofList ["fx", Project (var "x", "fx")])),
                    Concat []))))],
         Singleton (Record (Map.ofList ["fx", Project (var "z", "fx")])))

let qDelatPromBody = 
    For ([("x", tbDelat)],
        Prom 
            (For (["y", Dedup tbDelat],
                If (Apply (Primitive "==", [Project (var "x", "fx"); Project (var "y", "fx")]),
                    Singleton (Record (Map.ofList ["fx", Project (var "x", "fx")])),
                    Concat []))))

[<EntryPoint>]
let main _argv =
    let thequery = qDelatNested in
    printfn "*** printing test query"
    printfn "%s\n" (string_of_t thequery)
    let sqlquery = 
        thequery
        |> norm false Map.empty
        |> SqlGenerator.sql_of_query false
        |> SqlGenerator.string_of_query
    in
    printfn "*** printing SQL query without delateralization"
    printfn "%s\n" sqlquery
    let thequery = Delateralize.delateralize thequery in
    printfn "*** printing delateralized test query"
    printfn "%s\n" (string_of_t thequery)
    let thequery = 
        thequery
        |> SqlGenerator.sql_of_query false
        |> SqlGenerator.string_of_query
    in
    printfn "*** printing SQL test query with delateralization"
    printfn "%s" thequery
    0 // return an integer exit code
