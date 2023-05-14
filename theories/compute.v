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

From MuRec Require Import sigma schemes index vec recalg recalg_semantics.
From MuRec Require Export compute_def map_compute prim_rec_compute umin_compute.

Definition Zr_compute V1 : compute (Zr V1) := λ _, ⟪0, eq_refl⟫.
Definition Sc_compute : ∀V1, compute (Sc V1) := vec_S_inv (λ x _ _, ⟪S x, eq_refl⟫).
Definition Id_compute {a} (i : idx a) Va : compute (Id i Va) := λ _, ⟪Va.[i], eq_refl⟫.

Section Cn_compute.

  Variables (a b : nat)
            (Sb : recalg b)
            (cSb : ∀Vb, compute (⟦Sb⟧ Vb))
            (Sab : vec (recalg a) b)
            (cSab : ∀Va, compute (λ Vb, ∀i, ⟦Sab.[i]⟧ Va Vb.[i])).

  Section Cn_props.

    Variables (Va : vec nat a) (dVa : ex (Cn ⟦Sb⟧ (vec_map ra_sem Sab) Va)).

    Local Fact Cn_p1 : ∃Vb, ∀i, ⟦Sab.[i]⟧ Va Vb.[i].
    Proof.
      destruct dVa as (y & Vb & H1 & H2).
      exists Vb; intros i.
      specialize (H2 i).
      now rewrite vec_prj_map in H2.
    Qed.

    Variables (Vb : vec nat b) (Va_Vb : ∀i, ⟦Sab.[i]⟧ Va Vb.[i]).

    Fact Cn_p2 : ∃y, ⟦Sb⟧ Vb y.
    Proof.
      destruct dVa as (y & Wb & H1 & H2).
      exists y.
      replace Vb with Wb; trivial.
      apply vec_prj_ext; intros i.
      specialize (H2 i); specialize (Va_Vb i).
      rewrite vec_prj_map in H2.
      revert H2 Va_Vb; apply ra_sem_fun.
    Qed.

    Variables (y : nat) (Vb_y : ⟦Sb⟧ Vb y).

    Fact Cn_p3 : ⟦ra_comp Sb Sab⟧ Va y.
    Proof.
      exists Vb; refine (conj Vb_y _).
      intro; now rewrite vec_prj_map.
    Qed.

  End Cn_props.

  Arguments Cn_p1 {_}.
  Arguments Cn_p2 {_} _ {_} _.
  Arguments Cn_p3 {_} {_} _ {_}.

  Definition Cn_compute : ∀Va, compute (Cn ⟦Sb⟧ (vec_map ra_sem Sab) Va) :=
    λ Va dVa, let (Vb, Va_Vb) := cSab Va (Cn_p1 dVa) in
              let (y, Vb_y)   := cSb Vb (Cn_p2 dVa Va_Vb) in
              ⟪y, Cn_p3 Va_Vb Vb_y⟫.

End Cn_compute.

Arguments Cn_compute {a b Sb} _ {Sab} _.

Section Pr_compute.

  Variables (a : nat)
            (Sa : recalg a)       (cSa : ∀Va, compute (⟦Sa⟧ Va))
            (Sa'' : recalg (2+a)) (cSa'' : ∀Va'', compute (⟦Sa''⟧ Va'')).

  Definition Pr_compute : ∀Va', compute (Pr ⟦Sa⟧ ⟦Sa''⟧ Va') :=
    vec_S_inv (λ z Va,
      prim_rec_compute (ra_sem_fun _)
                       (λ V dV, cSa V dV)
                       (λ _ _ _, ra_sem_fun _ _)
                       (λ V n x cVnx, cSa'' (n ∷ x ∷ V) cVnx)
                       Va
                       z
    ).

End Pr_compute.

Arguments Pr_compute {a} {Sa} cSa {Sa''} cSa''.

Section Mn_compute.

  Variables (a : nat) (Sa' : recalg (1+a)) (cSa' : ∀Va', compute (⟦Sa'⟧ Va')).

  Definition Mn_compute Va : compute (Mn ⟦Sa'⟧ Va) :=
    umin₀_compute (λ _, ra_sem_fun _ _)
                  (λ n dn, cSa' (n ∷ Va) dn).

End Mn_compute.

Arguments Mn_compute {a} {Sa'} cSa'.
