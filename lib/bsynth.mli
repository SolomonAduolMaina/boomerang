open Blenses
open Regexcontext
open Lenscontext

val synth : Bvalue.t -> Bvalue.t -> Bvalue.t -> RegexContext.t -> LensContext.t -> 
						Info.t * MLens.t