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

Section map_compute.

  (** Any X-indexed family of computable Y-predicates can be lifted on vectors,
      ie partial vector map *)

  Variable (X Y : Type)
           (F : X → Y → Prop).

  (* Sharing the computation of the invisible witnesses *)
  Lemma vec_distrib_ex {a} (x : X) (Xₐ : vec X a) :
      (∃ Yₐ', ∀ i, F (x ∷ Xₐ).[i] Yₐ'.[i])
    → (∃ y : Y, F x y) ∧ (∃ Yₐ, ∀ i, F Xₐ.[i] Yₐ.[i]).
  Proof.
    destruct 1 as (Ya' & FYa'); destruct (vec_inv Ya') as [y Ya]; split.
    + exists y; exact (FYa' 𝕆).
    + exists Ya; exact (λ i, FYa' (𝕊 i)).
  Qed.

  Section vec_map_compute_props.

    Local Fact vmc_PO1 i : F ⟨⟩.[i] ⟨⟩.[i].
    Proof. destruct (idx_inv i). Qed.

    Variables (a : nat) (x : X) (y : Y)
              (Fy : F x y)
              (Xa : vec X a)
              (Ya : vec Y a)
              (FYa : ∀ i, F Xa.[i] Ya.[i]).

    Local Fact vmc_PO2 i : F (x ∷ Xa).[i] (y ∷ Ya).[i].
    Proof. now destruct (idx_inv i); cbn. Qed.

  End vec_map_compute_props.

  Arguments vmc_PO2 {_ _ _} _ {_ _} _.

  Fixpoint vec_map_compute a (Xa : vec X a) { struct Xa } : 
       (∀i, computable (F Xa.[i])) → computable (λ Ya, ∀i, F Xa.[i] Ya.[i]) :=
    match Xa with
    | ⟨⟩     => λ _ _,    ⟪⟨⟩, vmc_PO1⟫
    | x ∷ Xa => λ HxXa e, let (ey, eY)  := vec_distrib_ex x Xa e in
                          let (y,Fy)    := HxXa 𝕆 ey in
                          let (Ya, FYa) := vec_map_compute _ Xa (λ i, HxXa (𝕊 i)) eY in
                          ⟪y ∷ Ya, vmc_PO2 Fy FYa⟫
    end.

End map_compute.

Arguments vec_map_compute {X Y} F {a Xa}.
