(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** Constant.fs - Constants                                                 **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)

module Constant

    type t = 
    | Bool of bool
    | Int of int
    | Char of char
    | Float of float
    | String of string

    let string_of_t = function
    | Bool b -> b.ToString()
    | Int i -> i.ToString()
    | Char c -> Printf.sprintf "'%c'" c
    | Float f -> f.ToString()
    | String s -> Printf.sprintf "\"%s\"" s