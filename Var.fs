module Var

    type var = string

    let var_counter = ref 0

    let fresh_raw_var () = 
      incr var_counter
      "var" + (!var_counter).ToString()