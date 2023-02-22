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

From MuRec Require Import sigma relations index vec computable_def.

Section vec_map_compute.

  Variables (X Y : Type)
            (F : X → Y → Prop)
            (f : ∀ x, computableᵤ (F x)).

  Section vec_map_compute_props.

    Local Fact vmc_PO1 i : F ⟨⟩.[i] ⟨⟩.[i].
    Proof. destruct (idx_inv i). Qed.

    Variables (n : nat)
              (x : X) (v : vec X n)
              (y : Y) (w : vec Y n)
              (Fxy : F x y)
              (Fvw : ∀ i, F v.[i] w.[i]).

    Local Fact vmc_PO2 i : F (x ∷ v).[i] (y ∷ w).[i].
    Proof. now destruct (idx_inv i); cbn. Qed.

  End vec_map_compute_props.

  Arguments vmc_PO2 {_ _ _ _ _}.

  Definition vec_map_compute : ∀{n} (v : vec X n), computable (λ w, ∀i, F v.[i] w.[i]) :=
    let fix loop {n} (v : vec X n) : (∀i, ex (F v.[i])) → _ :=
      match v with
      | ⟨⟩    => λ _,   ⟪⟨⟩, vmc_PO1⟫
      | x ∷ v => λ Fxv, let (y, x_y) := f x ⌊Fxv 𝕆⌋ᵤ in
                        let (w, v_w) := loop v (λ i, Fxv (𝕊 i)) in
                        ⟪y ∷ w, vmc_PO2 x_y v_w⟫
      end in
    λ n v Fv, loop v (let (w, Fvw) := Fv in λ i, ⟪w.[i], Fvw i⟫ₚ).

End vec_map_compute.

Arguments vec_map_compute {_ _ _} _ {n} v.

