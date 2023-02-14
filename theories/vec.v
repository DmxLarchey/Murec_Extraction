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

From MuRec Require Import index.

Reserved Notation "v .[ i ]" (at level 1, format "v .[ i ]").
Reserved Notation "x '∷' v" (at level 60, right associativity, format "x  ∷  v").
Reserved Notation "⟨ ⟩" (at level 0, format "⟨ ⟩").

Section vec_basics.

  Variable X : Type.

  Inductive vec : nat → Type :=
    | vec_nil  : vec 0
    | vec_cons {n} : X → vec n → vec (S n).

  Notation "⟨ ⟩" := vec_nil.
  Infix "∷" := vec_cons.

  Inductive vec_shape_O : vec 0 → Type :=
    | vec_shape_O_intro : vec_shape_O ⟨⟩.

  Inductive vec_shape_S n : vec (S n) → Type :=
    | vec_shape_S_intro x v : vec_shape_S n (x ∷ v).

  Definition vec_inv {n} v :
    match n return vec n -> Type with
    | 0   => vec_shape_O
    | S n => vec_shape_S n
    end v.
  Proof. destruct v; constructor. Qed.

  Section vec_O_inv.

    Let vec_O_inv_t {n} : vec n → Type :=
      match n with
      | 0 => λ v, ∀P, P ⟨⟩ → P v
      | _ => λ _, Empty_set → unit
      end.

    Variables (P : vec 0 → Type)
              (HP : P ⟨⟩).

    Definition vec_O_inv v : P v :=
      match v return vec_O_inv_t v with
      | ⟨⟩ => λ P HP, HP
      | _  => λ C, match C with end
      end P HP.

  End vec_O_inv.

  Section vec_S_inv.

    Let vec_S_inv_t {n} : vec n → Type :=
      match n with
      | 0 => λ _, Empty_set → unit
      | _ => λ v, ∀P, (∀x w, P (x ∷ w)) → P v
      end.

    Variables (n : nat)
              (P : vec (S n) → Type)
              (HP : ∀x v, P (x ∷ v)).

    Definition vec_S_inv v : P v :=
      match v return vec_S_inv_t v with
      | ⟨⟩    => λ C, match C with end
      | y ∷ u => λ P HP, HP y u
      end P HP.

  End vec_S_inv.

  Arguments vec_S_inv {_ _}.

  (* Beware that with that definition, vec_{head,tail} are not recognized
     as sub-terms of v. This could be needed in case of Fixpoints on
     inductive types nesting vec. The cause of this is the dependent pattern-matching
     returning vec_S_inv_t in vec_S_inv. The more standard definition of
     vec_head (resp. vec_tail) does not have this issue because the return type
     is eg is_succ n → X which becomes non-dependent when (n := S _). *)

  Definition vec_head {n} : vec (S n) → X := vec_S_inv (λ x _,x).
  Definition vec_tail {n} : vec (S n) → vec n := vec_S_inv (λ _ v,v).

  Goal ∀n (v : vec (S n)), v = vec_head v ∷ vec_tail v.
  Proof. intros n v; now destruct (vec_inv v). Qed.

  (* This definition is compatible with the recalg_rect Fixpoint, meaning
     that (vec_prj v i) is recognized as a sub-term of v in that Fixpoint *)

  Fixpoint vec_prj {n} (u : vec n) : idx n → X :=
    match u in vec m return idx m → X with
    | ⟨⟩    => λ i, match idx_inv i with end
    | x ∷ v => λ i,
      match i in idx m return vec (pred m) → X with
      | 𝕆   => λ _, x
      | 𝕊 j => λ v, v.[j]
      end v
    end
  where "v .[ i ]" := (vec_prj v i).

  Local Example vec_prj_conv_eq_0 n x (v : vec n) : (x ∷ v).[𝕆] = x.
  Proof. reflexivity. Qed.

  Local Example vec_prj_conv_eq_S n x (v : vec n) i : (x ∷ v).[𝕊 i] = v.[i].
  Proof. reflexivity. Qed.

  Fact vec_prj_ext {n} (v w : vec n) : (∀i, v.[i] = w.[i]) → v = w.
  Proof.
    revert w; induction v as [ | n x v IHv ]; intros w H.
    + now destruct (vec_inv w).
    + destruct (vec_inv w) as [y w]; f_equal.
      * apply (H 𝕆).
      * apply IHv.
        intro; apply (H (𝕊 _)).
  Qed.

End vec_basics.

Arguments vec_nil {_}.
Arguments vec_cons {_ _}.
Arguments vec_inv {_ _}.
Arguments vec_prj {_ _}.
Arguments vec_head {_ _} _ /.
Arguments vec_tail {_ _} _ /.

Arguments vec_O_inv {_ _}.
Arguments vec_S_inv {_ _ _}.

Notation "⟨ ⟩" := vec_nil.
Infix "∷" := vec_cons.
Notation "v .[ i ]" := (vec_prj v i).

Section vec_map.

  Context {A B: Type} (f : A → B).

  Fixpoint vec_map {n} (v : vec A n) : vec B n :=
    match v with
    | ⟨⟩    => ⟨⟩
    | a ∷ v => f a ∷ vec_map v
    end.

  Fact vec_prj_map n (v : vec A n) : ∀i, (vec_map v).[i] = f v.[i].
  Proof. induction v; intro i; destruct (idx_inv i); cbn; trivial. Qed.

End vec_map.

Notation "⟨ x ⟩" :=  (x ∷ ⟨⟩) (at level 0, format "⟨ x ⟩").
Notation "⟨ x ; y ; .. ; z ⟩" :=  (x ∷ (y ∷ .. (z ∷ ⟨⟩) ..)) (at level 0, format "⟨ x ; y ; .. ; z ⟩").

Section hvec.

  Variables (X : Type) (P : X → Type).

  Inductive hvec : forall {n}, vec X n → Type :=
    | hvec_nil : hvec ⟨⟩
    | hvec_cons {n x v} : P x → @hvec n v → hvec (x ∷ v).

  Definition vec_hmap (f : forall x, P x) : ∀ {n} v, @hvec n v :=
    fix loop {n} v :=
      match v with
      | ⟨⟩    => hvec_nil
      | x ∷ v => hvec_cons (f x) (loop v)
      end.

End hvec.

Arguments hvec {_} P {_}.
Arguments hvec_nil {_ _}.
Arguments hvec_cons {_ _ _ _ _}.
Arguments vec_hmap {X P} _ {n} _.
