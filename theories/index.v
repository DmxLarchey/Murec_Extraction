(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*           [*] Affiliation Univ. Lorraine - CNRS - LORIA    *)
(*           [+] Affiliation VERIMAG - Univ. Grenoble Alpes   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

From Coq Require Import Utf8.

(* The type of positions/indices [0,...,n-1] with small inversion *)

Inductive idx : nat → Set :=
  | idx_fst {n} : idx (S n)
  | idx_nxt {n} : idx n → idx (S n).

Notation 𝕆 := idx_fst.
Notation 𝕊 := idx_nxt.

Inductive idx_shape_O : idx 0 → Set := .

Inductive idx_shape_S n : idx (S n) → Set :=
  | idx_shape_S_fst : idx_shape_S n 𝕆
  | idx_shape_S_nxt p : idx_shape_S n (𝕊 p).

Definition idx_inv {n} p :
  match n with
  | O   => idx_shape_O
  | S n => idx_shape_S n
  end p.
Proof. destruct p; constructor. Defined.
