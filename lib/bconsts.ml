let processed_qre_variables : string list ref = ref []
let processed_re_and_quotient_variables : string list ref = ref []
let processed_lenses : string list ref = ref []

let qre_sizes : int ref = ref 0
let regex_canonizer_size : int ref = ref 0
let synthed_lens_size : int ref = ref 0
let example_sizes : int ref = ref 0
