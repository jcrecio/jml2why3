type error =
  | Normal_error of string
  | Unknown_variant of {class_name: string; types: string list}

type component = Field of string | Index of int

type path = component list

type 'a json_result = ('a, error * path) result

val compilation_unit : Yojson.Safe.t -> JmlAst.compilation_unit json_result

val pp_error : Format.formatter -> error * component list -> unit
