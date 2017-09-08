open Hbase
open Synth
open Blenses
open Regexcontext
open Lenscontext

val synth : Bvalue.t -> Bvalue.t -> (Bvalue.t list) -> RegexContext.t -> LensContext.t -> 
						Info.t * MLens.t