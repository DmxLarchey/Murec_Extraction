```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*           [*] Affiliation LORIA - CNRS                     *)
(*           [+] Affiliation VERIMAG - Univ. Grenoble Alpes   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)
```

This artifact contains the Coq code intimately associated with submission 
to the _International Conference on Interactive Theorem Proving_ [(ITP 2023)](https://mizar.uwb.edu.pl/ITP2023/).

     "Proof pearl: extraction of µ-recursive schemes in Coq"

The code in this GitHub repository is distributed under the
[`CeCILL v2.1` open source software license](Licence_CeCILL_V2.1-en.txt).

This artifact consists, in the sub-directory [`theories`](theories):
+ a `makefile`, generating a well suited `Makefile.coq` from;
+ a `_CoqProject` file listing;
+ Coq source code files `*.v`;
+ and also two diff files: `[unit,hide].diff`;

The diff files or the two _pull requests (PR)_ below are intended to visualize 
the difference between the three branches of the source code:
+ the regular `murec_artifact` branch used as main basis for the paper;
+ the [`murec_artifact_unit`](https://github.com/DmxLarchey/Murec_Extraction/pull/1) 
  and [`murec_artifact_hide`](https://github.com/DmxLarchey/Murec_Extraction/pull/2) branches/PR, 
  discussed in the Extraction section of the paper, and which explore
  ways to get the cleanest possible OCaml extraction.
  
The Coq code was developed under Coq `8.15`: 
- but it should compile under various versions of Coq, 
  starting from at least Coq `8.10`. 
- we positively tested the following version of
  Coq on this code: `8.10.2`, `8.11.2`, `8.12.2`, 
     `8.13.[1,2]`, `8.14.1`, and `8.15.[0,2]`.
- the code does not use any external libraries except 
  from the `Init`, `Utf8` and `Extraction` modules of the 
  Coq standard library which requires no additional
  installation process besides that of Coq itself.

To run the compilation and extraction process,
just type `make all` in a terminal. This process 
should last no more than 5 seconds. The extracted 
OCaml code should appear under the `ra.ml` file as 
well as in the terminal directly.

After compilation, the Coq code can be reviewed using 
your favorite IDE. We also distribute colored versions 
of the diff files to help at spotting the not so many 
updates needed for switching between branches.

Below, we give a typical example for terminal interaction 
in the directory of the artifact:

```
mkdir artifact
cd artifact
tar zxvf .../artifact.tar.gz

make all
more ra.ml
coqide interpreter.v
./switch.pl main
./switch.pl unit
make all
more ra.ml
nano unit.diff # gives colorized display of the diff file 
./switch.pl hide
make all
more ra.ml
nano hide.diff
./switch.pl main
make clean
```

Without using the above mentionned _unit_ or _hide_ tricks, we
already obtain the following Ocaml extracted code from the
certified implementation of µ-recursive algorithms:

```
type nat =
| O
| S of nat

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val vec_prj : 'a1 list -> nat -> 'a1 **)

let rec vec_prj u i =
  match u with
  | [] -> assert false (* absurd case *)
  | x::v -> (match i with
             | O -> x
             | S j -> vec_prj v j)

type recalg =
| Ra_zero
| Ra_succ
| Ra_proj of nat
| Ra_comp of recalg * recalg list
| Ra_prec of recalg * recalg
| Ra_umin of recalg

type 'x computable = __ -> 'x

(** val vec_map_compute : ('a1 -> 'a2 computable) -> 'a1 list -> 'a2 list **)

let rec vec_map_compute fcomp = function
| [] -> []
| x::xa -> (fcomp x __)::(vec_map_compute fcomp xa)

(** val prim_rec_compute :
    ('a1 -> 'a2 computable) -> ('a1 -> nat -> 'a2 -> 'a2 computable) -> 'a1
    -> nat -> 'a2 **)

let rec prim_rec_compute fcomp gcomp x = function
| O -> fcomp x __
| S n -> gcomp x n (prim_rec_compute fcomp gcomp x n) __

(** val umin_compute : (nat -> nat computable) -> nat -> nat **)

let rec umin_compute f s =
  match f s __ with
  | O -> s
  | S _ -> umin_compute f (S s)

(** val ra_compute : recalg -> nat list -> nat **)

let rec ra_compute sk vk =
  match sk with
  | Ra_zero -> O
  | Ra_succ ->
    (match vk with
     | [] -> assert false (* absurd case *)
     | y::_ -> S y)
  | Ra_proj i -> vec_prj vk i
  | Ra_comp (sb, skb) ->
    ra_compute sb (vec_map_compute (fun sa _ -> ra_compute sa vk) skb)
  | Ra_prec (sb, sb'') ->
    (match vk with
     | [] -> assert false (* absurd case *)
     | y::u ->
       prim_rec_compute (fun v _ -> ra_compute sb v) (fun v n x _ ->
         ra_compute sb'' (n::(x::v))) u y)
  | Ra_umin sb' -> umin_compute (fun n _ -> ra_compute sb' (n::vk)) O
```

