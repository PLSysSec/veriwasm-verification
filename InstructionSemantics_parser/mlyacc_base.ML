(* Glue to make mlyacc/mllex run inside Isabelle/ML *)

open Unsynchronized
open IntInf

val valOf = Option.valOf
val isSome = Option.isSome
val foldl = List.foldl
val foldr = List.foldr

fun print s = tracing s

val explode = String.explode
fun revfold f init lst = foldl f lst init

