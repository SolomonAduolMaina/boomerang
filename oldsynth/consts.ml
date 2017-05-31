(*******************************************************************************
 * consts.ml - global constants
 ******************************************************************************)

let use_iterative_deepen_strategy : bool ref = ref false
let force_expand_regexps : bool ref = ref false

(* The set of directories to search for includes *)
let include_directories : string list ref = ref ["."]

let naive_strategy : bool ref = ref false
let naive_pqueue : bool ref = ref false
let short_circuit : bool ref = ref true
let use_lens_context : bool ref = ref true