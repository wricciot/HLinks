(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** Var.fs - Variable names                                                 **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)

module Var

    type var = string

    let var_counter = ref 0

    let fresh_raw_var () = 
      incr var_counter
      "var" + (!var_counter).ToString()

    let string_of_var (v : var) = v