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

(** A predicate is computable if a value
    can be computed out of a proof of inhabitation *)

Definition computable {X} (P : X → Prop) := ex P → sig P.
Definition computable_unit {X} (P : X → Prop) := {_ : unit | ex P} → sig P.

Notation computableᵤ := computable_unit.
