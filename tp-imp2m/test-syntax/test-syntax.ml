(*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 *)

type variable = string

type aoper = | Aadd | Asub | Amul
type aexpr =
  | Acst of int
  | Avar of variable
  | Abin of aoper * aexpr * aexpr

type bcomp = | Beq | Bne | Ble | Blt | Bge | Bgt
type boper = | Band | Bor
type bexpr =
  | Btest of bcomp * aexpr * aexpr
  | Boper of boper * bexpr * bexpr
  | Bneg of bexpr

type imp =
  | Cskip
  | Cassign of variable * aexpr
  | Cseq of imp * imp
  | Cifte of bexpr * imp * imp
  | Cwhiledo of bexpr * imp

type tuple = variable list

type ml =
  | Faexpr of aexpr
  | Fbexpr of bexpr
  | Ftuple of tuple
  | Fletin of variable * aexpr * ml
  | Fletsin of tuple * ml * ml
  | Fletrecin of int * tuple * ml * ml
  | Fcall of int * tuple
  | Fifte of bexpr * ml * ml
  (* used by standalone module *)
  | Fcaml of string * tuple * ml


(* Détermination de l'ensemble (non ordonné des variables libres *)

module S = Set.Make(String)

let rec vars_of_aexpr = function
  | Acst _ ->  S.empty
  | Avar x -> S.singleton(x)
  | Abin (_, a, b) -> S.union (vars_of_aexpr a) (vars_of_aexpr b)
and vars_of_bexpr = function
  | Btest (_, a, b) ->  S.union (vars_of_aexpr a) (vars_of_aexpr b)
  | Boper (_, p, q) -> S.union (vars_of_bexpr p) (vars_of_bexpr q)
  | Bneg p -> vars_of_bexpr p
and vars_of_imp = function
  | Cskip -> S.empty
  | Cassign (x, a) -> S.add x (vars_of_aexpr a)
  | Cseq (c1, c2) -> S.union (vars_of_imp c1) (vars_of_imp c2)
  | Cifte (b, c1, c2) -> S.union (vars_of_bexpr b) (S.union (vars_of_imp c1) (vars_of_imp c2))
  | Cwhiledo (b, c) -> S.union (vars_of_bexpr b) (vars_of_imp c)

let vars_of_imp c = S.elements (vars_of_imp c) (* liste ordonnée *)


(* print functions *)

let string_of_aoper = function
  | Aadd -> "+" | Asub -> "-" | Amul -> "*"

let rec string_of_aexpr = function
  | Acst n -> string_of_int n
  | Avar x -> x
  | Abin (op, a, b) ->
     let sop = string_of_aoper op in
     let sa = string_of_aexpr a and sb = string_of_aexpr b in
     Printf.sprintf "(%s %s %s)" sa sop sb

let string_of_bcomp = function
  | Beq -> "="  | Bne -> "<>"
  | Ble -> "<=" | Blt -> "<"
  | Bge -> ">=" | Bgt -> ">"

let string_of_boper = function
  | Band -> "&&" | Bor -> "||"

let string_of_bexpr bexpr =
  let rec loop = function
    | Btest (cmp, a, b) ->
       let scmp = string_of_bcomp cmp in
       let sa = string_of_aexpr a and sb = string_of_aexpr b in
       Printf.sprintf "%s %s %s" sa scmp sb
    | Boper (op, p, q) ->
       let so = string_of_boper op in
       let sp = loop p and sq = loop q in
       Printf.sprintf "%s %s %s" sp so sq
    | Bneg p ->
       let sp = loop p in
       Printf.sprintf "not %s" sp
  in loop bexpr

let tab = "  " (* Ocaml standard tab value *)

let string_of_imp command =
  let rec loop tab_shift return = function
  | Cskip -> Printf.sprintf "%sskip%s" tab_shift return
  | Cassign (x, e) -> Printf.sprintf "%s%s <- %s%s" tab_shift x (string_of_aexpr e) return
  | Cifte (b, c1, c2) ->
     let sb = string_of_bexpr b in
     let sc1 = loop (tab ^ tab_shift) "\n" c1 in
     let sc2 = loop (tab ^ tab_shift) "\n" c2 in
     Printf.sprintf "%sif %s\n%s%s else \n%s%s\nfi%s" tab_shift sb sc1 tab_shift sc2 tab_shift return
  | Cwhiledo (b, c)  ->
     let sb = string_of_bexpr b in
     let sc = loop (tab ^ tab_shift) "\n" c in
      Printf.sprintf "%swhile %s do\n%s%s\ndone%s" tab_shift sb sc tab_shift return
  | Cseq (c1, c2) ->
     let sc1 = loop tab_shift "" c1 in
     let sc2 = loop tab_shift return c2 in
     Printf.sprintf "%s;\n%s" sc1 sc2
  in loop "" "" command

let string_of_tuple t =
  "(" ^ String.concat ", " t ^ ")"

let rec same_tuple = function
  | [], [] -> true
  | x :: l, y :: r when x = y -> same_tuple (l, r)
  | _, _ -> false

let rec substitute x v t = function
  | [] -> []
  | y :: l when x = y -> v :: List.tl t
  | y :: l -> List.hd t :: substitute x v (List.tl t) l


let string_of_ml left_margin expression =
  let string_of_call tab_shift n =
    Printf.sprintf "%sloop_%s" tab_shift (string_of_int n) in
  let rec loop tab_shift return = function
  | Faexpr a -> string_of_aexpr a
  | Fbexpr b -> string_of_bexpr b
  | Ftuple t -> tab_shift ^ string_of_tuple t
  | Fletin (x, a, Ftuple t) ->
     let sa = string_of_aexpr a in
     "$$ " ^ string_of_tuple (substitute x sa t t)
     (* Printf.sprintf "%s%s" tab_shift (string_of_tuple (substitute x sa t vars)) *)
     (* Printf.sprintf "%slet %s = %s in %s" tab_shift x sa (string_of_tuple t) *)
  | Fletin (x, a, e) ->
     let sa = string_of_aexpr a in
     let se = loop tab_shift return e in
     Printf.sprintf "%slet %s = %s in\n%s" tab_shift x sa se
  | Fletsin (t, Fletin (x, a, e1), e2) ->
     loop tab_shift return (Fletin (x, a, Fletsin (t, e1, e2)))
  | Fletsin (t, Ftuple r, e2) ->
     if same_tuple (t, r) then 
       loop tab_shift return e2
     else (* should NOT occur *)
       let st = string_of_tuple t in
       let se1 = loop (tab ^ tab_shift) return (Ftuple r) in
       let se2 = loop tab_shift return e2 in
       Printf.sprintf "%slet %s = \n%s\n%sin\n%s" tab_shift st se1 tab_shift se2
  | Fletsin (t, e1, e2) ->
     let st = string_of_tuple t in
     let se1 = loop (tab ^ tab_shift) return e1 in
     let se2 = loop tab_shift return e2 in
     (match e2 with
      | Fcall _
      | Ftuple _ ->
         Printf.sprintf "%slet %s = \n%s\n%sin %s" tab_shift st se1 tab_shift se2
      | _ ->
         Printf.sprintf "%slet %s = \n%s\n%sin\n%s" tab_shift st se1 tab_shift se2)
  | Fletrecin (n, t, e1, e2) ->
     let sn = string_of_call "" n in
     let st = string_of_tuple t in
     let se1 = loop (tab ^ tab_shift) return e1 in
     let se2 = loop "" return e2 in
     Printf.sprintf "%slet rec %s %s = \n%s\n%sin %s" tab_shift sn st se1 tab_shift se2
  | Fcall (n, t) ->
     let sn = string_of_call tab_shift n in
     let st = string_of_tuple t in
     Printf.sprintf "%s %s" sn st
  | Fifte (b, e1, e2) ->
     let sb = string_of_bexpr b in
     let se1 = loop (tab ^ tab_shift) return e1 in
     let se2 = loop (tab ^ tab_shift) return e2 in
     Printf.sprintf "%sif %s then\n%s\n%selse\n%s" tab_shift sb se1 tab_shift se2
  (* used by standalone module *)
  | Fcaml (ident, t, e) ->
     let st = string_of_tuple t in
     let se = loop (tab ^ tab_shift) return e in
     Printf.sprintf "let %s %s =\n%s" ident st se

  in loop left_margin "" expression


(* Imp code for (x,y) -> z:= x+y *)

let imp_ex1 = Cassign ("z",Abin(Aadd,(Avar "x"),(Avar "y")));;
let () = print_string (string_of_imp imp_ex1);print_string "\n\n";;

(* Imp code for x -> y:= max(x,0) *)

let imp_ex2 = Cifte(Btest(Bge,Avar("x"),Acst(0)),
                    Cassign("y",Avar("x")),
                    Cassign("y",Acst(0)));;
let () = print_string (string_of_imp imp_ex2);print_string "\n\n";;

(* Imp code for x -> f:= x! *)

let imp_ex3 =
  Cseq(Cassign("f",Acst(1)),
       Cwhiledo(Btest(Bne,Avar("x"),Acst(0)),
                Cseq(Cassign("f",Abin(Amul,Avar("f"),Avar("x"))),
                     Cassign("x",Abin(Asub,Avar("x"),Acst(1)))
                    )
               )
      );;
let () = print_string (string_of_imp imp_ex3);;
let () = print_string "\n\n";;


(* ML code for (x,y) -> z:= x+y *)

let ml_ex1 = Fletrecin(0,["x";"y"],Faexpr(Abin(Aadd,Avar("x"),Avar("y"))),Fcall(0,["a";"b"]));;
let () = print_string (string_of_ml "" ml_ex1);;
let () = print_string "\n\n";; 

(* ML code for x -> y:= sign(x) = max(x,0) *)

let ml_ex2 = () ;;
let () = print_string (string_of_ml "" ml_ex2);;
let () = print_string "\n\n";;
   
   
(* ML code for x -> f:= x! *)

let ml_ex3 = ();;
let () = print_string (string_of_ml "" ml_ex3);;
let () = print_string "\n\n";;
      

