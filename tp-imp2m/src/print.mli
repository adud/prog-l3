(*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 *)

val string_of_aexpr : Syntax.aexpr -> string
val string_of_bexpr : Syntax.bexpr -> string
val string_of_imp : Syntax.imp -> string
val string_of_ml : string -> Syntax.ml -> string
