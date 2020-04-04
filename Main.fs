(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** Main.fs - Program entry point and tests                                 **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)
module Main

open Query

let sItems = [("name",()); ("quantity",())] |> Map.ofList 
let sOrders = [("oid",()); ("item",()); ("quantity",())] |> Map.ofList
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

let vx = Var ("x", [("fx",())] |> Map.ofList)
let vy = Var ("y", [("fy",())] |> Map.ofList)
let vz = Var ("z", [("fz",())] |> Map.ofList)
let tbDelat = Table ("TableX", [("fx",())] |> Map.ofList)
// wraps a query so that it cannot be normalized out
let blobOf q = For (["x'", tbDelat], Singleton q) |> Dedup |> Prom

let qDedup = 
    For ([("x", tbDelat); 
          ("y", Prom (Dedup 
            (For (["z", blobOf (Apply (Primitive "opaque1", [vx]))],
                blobOf (Apply (Primitive "opaque1", [vz]))))))],
        blobOf (Apply (Primitive "opaque2", [vx;vy])))

[<EntryPoint>]
let main _argv =
    let thequery = qDedup in
    printfn "*** printing test query"
    printfn "%s" (string_of_t thequery)
    let thequery = norm Map.empty thequery in
    printfn "*** printing normalized test query"
    printfn "%s" (string_of_t thequery)
    0 // return an integer exit code
