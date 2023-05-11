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

(** A predicate "computes" if a value in it can be computed 
    using of a proof of its inhabitation has termination
    certificate *)

Definition compute {X} (P : X → Prop) := ex P → sig P.
Definition compute_unit {X} (P : X → Prop) := {_ : unit | ex P} → sig P.

Notation computeᵤ := compute_unit.
