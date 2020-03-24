module Constant

    type t = 
    | Bool of bool
    | Int of int
    | Char of char
    | Float of float
    | String of string

    let bar () = ()