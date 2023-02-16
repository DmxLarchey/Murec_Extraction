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

Section vec_dmap.

  Variables (X Y : Type)
            (F : X → Y → Prop)
            (f : ∀ x, computable (F x)).

  Section vec_map_compute_props.

    Local Fact vdm_PO1 i : F ⟨⟩.[i] ⟨⟩.[i].
    Proof. destruct (idx_inv i). Qed.

    Variables (x : X) (n : nat) (v : vec X n) (y : Y) (w : vec Y n)
              (Fx : F x y)
              (Fv : ∀ i, F v.[i] w.[i]).

    Local Fact vdm_PO2 i : F (x ∷ v).[i] (y ∷ w).[i].
    Proof. now destruct (idx_inv i); cbn. Qed.

  End vec_map_compute_props.

  Arguments vdm_PO2 {_ _ _ _ _}.

  Definition vec_map_compute {n} (v : vec X n) : computable (λ w, ∀i, F v.[i] w.[i]) :=
    let fix loop {n} (v : vec X n) : (∀i, ex (F v.[i])) → _ :=
      match v with
      | ⟨⟩    => λ _,   ⟪⟨⟩, vdm_PO1⟫
      | x ∷ v => λ hxv, let (y,hy) := f x (hxv 𝕆) in
                        let (w,hw) := loop v (λ i, hxv (𝕊 i)) in
                        ⟪y ∷ w, vdm_PO2 hy hw⟫
      end in
    λ hv, loop v (λ i, let (w,hw) := hv in ⟪w.[i],hw i⟫ₚ).

End vec_dmap.

Arguments vec_map_compute {_ _ _} _ {n} v.

