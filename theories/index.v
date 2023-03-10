(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-FranΓ§ois Monin           [+]              *)
(*                                                            *)
(*           [*] Affiliation Univ. Lorraine - CNRS - LORIA    *)
(*           [+] Affiliation VERIMAG - Univ. Grenoble Alpes   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

From Coq Require Import Utf8.

(* The type of positions/indices [0,...,n-1] with small inversion *)

Inductive idx : nat β Set :=
  | idx_fst {n} : idx (S n)
  | idx_nxt {n} : idx n β idx (S n).

Notation π := idx_fst.
Notation π := idx_nxt.

Inductive idx_shape_O : idx 0 β Set := .

Inductive idx_shape_S n : idx (S n) β Set :=
  | idx_shape_S_fst : idx_shape_S n π
  | idx_shape_S_nxt p : idx_shape_S n (π p).

Definition idx_inv {n} p :
  match n with
  | O   => idx_shape_O
  | S n => idx_shape_S n
  end p.
Proof. destruct p; constructor. Defined.
