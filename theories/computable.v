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

From MuRec Require Import sigma schemes index vec recalg recalg_semantics.
From MuRec Require Export computable_def map_compute prim_rec_compute umin_compute.

Definition Zr_compute V1 : computable (Zr V1) := λ _, ⟪0,eq_refl⟫.
Definition Sc_compute : ∀V1, computable (Sc V1) := vec_S_inv (λ x _ _, ⟪S x, eq_refl⟫).
Definition Id_compute {a} (i : idx a) Va : computable (Id i Va) := λ _, ⟪Va.[i], eq_refl⟫.

Section Cn_compute.

  Variables (compute : ∀{a} (Sa : recalg a) Va, computable (⟦Sa⟧ Va))
            (a b : nat) (Sb : recalg b) (Sab : vec (recalg a) b).

  Section Cn_props.

    Variables (Va : vec nat a) (cVa : ∃y, Cn ⟦Sb⟧ (vec_map ra_sem Sab) Va y).

    Local Fact Cn_p1 : ∃Vb, ∀i, ⟦Sab.[i]⟧ Va Vb.[i].
    Proof.
      destruct cVa as (y & Wb & H1 & H2).
      exists Wb; intro i; specialize (H2 i).
      now rewrite vec_prj_map in H2.
    Qed.

    Variables (Vb : vec nat b) (cVb : ∀i, ⟦Sab.[i]⟧ Va Vb.[i]).

    Fact Cn_p2 : ∃y, ⟦Sb⟧ Vb y.
    Proof.
      destruct cVa as (y & Wb & H1 & H2).
      exists y.
      replace Vb with Wb; trivial.
      apply vec_prj_ext; intros i.
      specialize (H2 i); specialize (cVb i).
      rewrite vec_prj_map in H2.
      revert H2 cVb; apply ra_sem_fun.
    Qed.

    Variables (y : nat) (Hy : ⟦Sb⟧ Vb y).

    Fact Cn_p3 : ⟦ra_comp Sb Sab⟧ Va y.
    Proof.
      exists Vb; refine (conj Hy _).
      intro; now rewrite vec_prj_map.
    Qed.

  End Cn_props.

  Arguments Cn_p1 {_}.
  Arguments Cn_p2 {_} _ {_}.
  Arguments Cn_p3 {_ _} _ {_}.

  Definition Cn_compute : ∀Va, computable (Cn ⟦Sb⟧ (vec_map ra_sem Sab) Va) :=
    λ Va cVa,
      let (Vb,cVb) := vec_map_compute (λ p : { Sa | ex (⟦Sa⟧ Va) }, compute (π₁ p) Va (π₂ p)) Sab (Cn_p1 cVa) in
      let (y,cy)   := compute Sb Vb (Cn_p2 cVa cVb)
      in  ⟪y,Cn_p3 cVb cy⟫.

End Cn_compute.

Arguments Cn_compute compute {a b} Sb Sab.

Section Pr_compute.

  Variables (compute : ∀{a} (Sa : recalg a) Va, computable (⟦Sa⟧ Va))
            (a : nat) (Sa : recalg a) (Sa'' : recalg (2+a)).

  Definition Pr_compute : ∀Va', computable (Pr ⟦Sa⟧ ⟦Sa''⟧ Va') :=
    vec_S_inv (λ z Va,
      prim_rec_compute (ra_sem_fun _)
                       (λ p, compute Sa (π₁ p) (π₂ p))
                       (λ _ _ _, ra_sem_fun _ _)
                       (λ V n x, compute Sa'' (n ∷ π₁ x ∷ V) (π₂ x))
                       Va
                       z
    ).

End Pr_compute.

Arguments Pr_compute compute {a} Sa Sa''.

Section Mn_compute.

  Variables (compute : ∀{a} (Sa : recalg a) Va, computable (⟦Sa⟧ Va))
            (a : nat) (Sa' : recalg (1+a)).

  Definition Mn_compute Va : computable (Mn ⟦Sa'⟧ Va) :=
    umin₀_compute (λ _, ra_sem_fun _ _)
                  (λ p, compute Sa' (π₁ p ∷ Va) (π₂ p)).

End Mn_compute.

Arguments Mn_compute compute {a} Sa'.
