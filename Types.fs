(*****************************************************************************
 ** HLinks -- Links-inspired prototype for DB queries mixing sets and bags  **
 ** (C) 2020 The University of Edinburgh                                    **
 ** ----------------------------------------------------------------------- **
 ** Types.fs - Types for the querying language                              **
 **                                                                         **
 ** author: Wilmer Ricciotti                                                **
 *****************************************************************************)

module Types

  type datatype = 
  | Not_typed
  | Arrow of datatype * datatype
  | RcdTy of Map<string,datatype>
  | ListTy of datatype
  | PrimTy of string

  let make_list_type ty = ListTy ty
  let make_record_type ftys = RcdTy ftys
  let unit_type     = RcdTy Map.empty
  let bool_type     = PrimTy "bool"
  let int_type      = PrimTy "int"
  let char_type     = PrimTy "char"
  let float_type    = PrimTy "float"
  let string_type   = PrimTy "string"