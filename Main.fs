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

[<EntryPoint>]
let main _argv =
    printfn "*** printing test query"
    printfn "%s" (string_of_t qTest)
    let qTest = norm Map.empty qTest in
    printfn "*** printing normalized test query"
    printfn "%s" (string_of_t qTest)
    0 // return an integer exit code
