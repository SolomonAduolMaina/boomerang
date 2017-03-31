open Lexing
open Parser2
open Lexer2
open Lang

let fromPosix (s : string) : regex = from_string s |> regex token