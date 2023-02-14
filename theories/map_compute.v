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

From Coq Require Import Utf8.

From MuRec Require Import sigma relations index vec computable_def.

Section hvec_map_compute.

  (** Any X-indexed family of computable Y-predicates can be lifted on vectors,
      ie partial vector map *)

  Variable (C X Y : Type)
           (F : C → X → Y → Prop).

  Section vec_map_compute_props.

    Variable x : X.

    Local Fact hvmc_PO1 i : F ⟨⟩.[i] x ⟨⟩.[i].
    Proof. destruct (idx_inv i). Qed.

    Variables (c : C) (y : Y) (a : nat) (Ca : vec C a) (Ya : vec Y a)
              (Fc : F c x y)
              (FCa : ∀ i, F Ca.[i] x Ya.[i]).

    Local Fact hvmc_PO2 i : F (c ∷ Ca).[i] x (y ∷ Ya).[i].
    Proof. now destruct (idx_inv i); cbn. Qed.

  End vec_map_compute_props.

  Arguments hvmc_PO1 {_}.
  Arguments hvmc_PO2 {_ _ _ _ _ _}.

  Fixpoint hvec_map_compute {b} {v : vec C b} (hv : hvec (λ c, forall y, ex (F c y) → sig (F c y)) v) :
         ∀y, (∀i, ex (F v.[i] y)) → { w | ∀i, F v.[i] y w.[i] } :=
    match hv with
    | hvec_nil =>        λ _ _,  ⟪⟨⟩, hvmc_PO1⟫
    | hvec_cons xF hv => λ y hy, let (x,Fx) := xF y (hy 𝕆) in
                                 let (w,Fw) := hvec_map_compute hv y (λ i, hy (𝕊 _)) in
                                 ⟪x ∷ w, hvmc_PO2 Fx Fw⟫
    end.

End hvec_map_compute.

Arguments hvec_map_compute {C X Y F b v}.

