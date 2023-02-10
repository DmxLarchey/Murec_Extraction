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

Section functional_relations_properties.

  Variables (X Y : Type).

  Definition functional₀ (P : Y → Prop) := ∀ y₁ y₂, P y₁ → P y₂ → y₁ = y₂.
  Definition functional₁ (R : X → Y → Prop) := ∀x, functional₀ (R x).

End functional_relations_properties.

Arguments functional₀ {_} _ /.
Arguments functional₁ {_ _} _/.

Notation functional := functional₁.

Definition rel_subst {X Y} (P : X → Prop) (R : X → Y → Prop) y := ∃x, P x ∧ R x y.
Notation "R '⋄' P" := (rel_subst P R) (at level 1, no associativity, format "R  ⋄  P").

Fact rel_subst_fun {X Y} (P : X → Prop) (R : X → Y → Prop) :
      functional₀ P → functional R → functional₀ (R ⋄ P).
Proof.
  intros HP HR y1 y2 (x1 & H1 & H2) (x2 & H3 & H4).
  revert H2 H4.
  rewrite (HP _ _ H1 H3).
  apply HR.
Qed.

Section included.

  Variables (X Y : Type).

  Definition included₀ (P Q : Prop) := P → Q.
  Definition included₁ (P Q : Y → Prop) := ∀y, P y → Q y.
  Definition included₂ (P Q : X → Y → Prop) := ∀x y, P x y → Q x y.

End included.

Arguments included₀ _ _ /.
Arguments included₁ {_} _ _ /.
Arguments included₂ {_ _} _ _ /.

Infix "⊆₀" := included₀ (at level 70, no associativity).
Infix "⊆₁" := included₁ (at level 70, no associativity).
Infix "⊆₂" := included₂ (at level 70, no associativity).

Fact included₁_refl {X} (P : X → Prop) : P ⊆₁ P.
Proof. now intro. Qed.

(* Left-recursive notation for tuples of proofs of propositions for logical conjunctions 
   the ₚ suffix is here to remind that tuple are proof of [P]roposition and distinguish 
   with the tuple notation for vectors *)
Notation "⟨ a , b , .. , c ⟩ₚ" := (conj .. (conj a b) .. c) (at level 0, format "⟨ a , b , .. , c ⟩ₚ").

Definition and₁ {X : Type} (P Q : X → Prop) := λ x, P x ∧ Q x.

Infix "∧₁" := and₁ (at level 68, right associativity).

Section facts.
  Context {X : Type}.
  Variables (P Q : X → Prop).

  Fact and₁_intro Q' : (P ⊆₁ Q) → (P ⊆₁ Q') → (P ⊆₁ Q ∧₁ Q').
  Proof. intros ? ? ? ?. red. intuition. Qed.

  Fact and₁_monotonic P' Q' : (P ⊆₁ P') → (Q ⊆₁ Q') → (P ∧₁ Q ⊆₁ P' ∧₁ Q').
  Proof. cbv; intros pp qq x; specialize (pp x); specialize (qq x); intuition. Qed.

End facts.
