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

  Variables (a b : nat) 
            (Sb : recalg b)
            (cSb : ∀Vb, computable (⟦Sb⟧ Vb))
            (Sab : vec (recalg a) b)
            (cSab : ∀Va, (∀i, ∃ y, ⟦Sab.[i]⟧ Va y) → {w | ∀ i, ⟦Sab.[i]⟧ Va w.[i] }).

  Section Cn_props.

    Variables (Va : vec nat a) (cVa : ex (Cn ⟦Sb⟧ (vec_map ra_sem Sab) Va)).

    Local Fact Cn_p1 : ∀i, ∃y, ⟦Sab.[i]⟧ Va y.
    Proof.
      destruct cVa as (y & Wb & H1 & H2).
      intros i; exists Wb.[i].
      specialize (H2 i).
      now rewrite vec_prj_map in H2.
    Qed.

    Variables (Vb : vec nat b) (HVb : ∀i, ⟦Sab.[i]⟧ Va Vb.[i]).

    Fact Cn_p2 : ∃y, ⟦Sb⟧ Vb y.
    Proof.
      destruct cVa as (y & Wb & H1 & H2).
      exists y.
      replace Vb with Wb; trivial.
      apply vec_prj_ext; intros i.
      specialize (H2 i); specialize (HVb i).
      rewrite vec_prj_map in H2.
      revert H2 HVb; apply ra_sem_fun.
    Qed.

    Variables (y : nat) (Hy : ⟦Sb⟧ Vb y).

    Fact Cn_p3 : ⟦ra_comp Sb Sab⟧ Va y.
    Proof.
      exists Vb; refine (conj Hy _).
      intro; now rewrite vec_prj_map.
    Qed.

  End Cn_props.

  Arguments Cn_p1 {_}.
  Arguments Cn_p2 {_} _ {_} _.
  Arguments Cn_p3 {_} {_} _ {_}.

  Definition Cn_compute : ∀Va, computable (Cn ⟦Sb⟧ (vec_map ra_sem Sab) Va) :=
    λ Va cVa, let (w,hw) := cSab Va (Cn_p1 cVa) in 
              let (y,hy) := cSb w (Cn_p2 cVa hw) in
              ⟪y, Cn_p3 hw hy⟫.

End Cn_compute.

Arguments Cn_compute {a b Sb} _ {Sab} _.

Section Pr_compute.

  Variables (a : nat) 
            (Sa : recalg a)       (cSa : ∀Va, computable (⟦Sa⟧ Va))
            (Sa'' : recalg (2+a)) (cSa'' : ∀Va'', computable (⟦Sa''⟧ Va'')).

  Definition Pr_compute : ∀Va', computable (Pr ⟦Sa⟧ ⟦Sa''⟧ Va') :=
    vec_S_inv (λ z Va,
      prim_rec_compute (ra_sem_fun _)
                       (λ V cV, cSa V cV)
                       (λ _ _ _, ra_sem_fun _ _)
                       (λ V n x cVnx, cSa'' (n ∷ x ∷ V) cVnx)
                       Va
                       z
    ).

End Pr_compute.

Arguments Pr_compute {a} {Sa} cSa {Sa''} cSa''.

Section Mn_compute.

  Variables (a : nat) (Sa' : recalg (1+a)) (cSa' : ∀Va', computable (⟦Sa'⟧ Va')).

  Definition Mn_compute Va : computable (Mn ⟦Sa'⟧ Va) :=
    umin₀_compute (λ _, ra_sem_fun _ _)
                  (λ n cn, cSa' (n ∷ Va) cn).

End Mn_compute.

Arguments Mn_compute {a} {Sa'} cSa'.
