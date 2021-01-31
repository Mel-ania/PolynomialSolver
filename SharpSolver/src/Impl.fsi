(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: file di signature per le implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module SharpSolver.Impl

open Prelude
open Absyn

val rationalize : float -> rational

val monomial_degree : monomial -> int

val monomial_negate : monomial -> monomial

val aux_poly_degree : polynomial -> int
val polynomial_degree : polynomial -> int

val aux_poly_negate : polynomial -> monomial list
val polynomial_negate : polynomial -> polynomial

val coefficienti : monomial list -> int -> rational
val rtn_lst : monomial list -> int -> rational list
val aux_normalize : polynomial -> rational array
val normalize : polynomial -> normalized_polynomial

val normalized_polynomial_degree : normalized_polynomial -> int

val aux_derive : polynomial -> monomial list
val derive : polynomial -> polynomial

val reduce : expr -> polynomial
val aux_equazione : expr * expr -> polynomial * polynomial
val equazione : expr * expr -> polynomial

val solve0 : normalized_polynomial -> bool
val solve1 : normalized_polynomial -> rational
val delta : rational array -> float
val solve2 : normalized_polynomial -> (float * float option) option
