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

(* Notation for proofs of the propositional Σ-type "∃x, P x", ie "ex P", for P : X → Prop *)

Notation "⟪ x , h ⟫ₚ" := (ex_intro _ x h) (at level 0, format "⟪ x ,  h ⟫ₚ").

(* Notations for terms of the Σ-type "{ x : X | P x }", ie "sig P", for P : X → Prop *)

Notation "⟪ x , h ⟫" := (exist _ x h) (at level 0, format "⟪ x ,  h ⟫").
Notation π₁ := proj1_sig.
Notation π₂ := proj2_sig.

Notation "'⌊' P '⌋ᵤ'" := (exist _ tt P) (at level 1, format "⌊ P ⌋ᵤ").
Notation πᵤ := proj2_sig.

Definition reify {X Y} {P : X → Y → Prop} : (∀ x, { y | P x y }) → { f : X → Y | ∀ x, P x (f x) } :=
  λ df, exist (λ f, ∀ x, P x (f x)) (λ x, π₁ (df x)) (λ x, π₂ (df x)).

Definition ex_monotonic {X: Set} {P Q : X → Prop} : (∀x, P x → Q x) → ex P → ex Q :=
  λ f xp, let (x, p) := xp in ex_intro _ x (f x p).

Definition sig_monotonic {X: Set} {P Q : X → Prop} : (∀x, P x → Q x) → sig P → sig Q :=
  λ f xp, let (x, p) := xp in exist _ x (f x p).

(* Functional composition is very convenient for chaining the strengthening of
   a precondition P, an algorithm of type ex P → sig Q and the weakening
   of its postcondition Q, in combination with ex_monotonic and sig_monotonic. *)

Definition comp {X Y Z : Type} (g : Y → Z) (f : X → Y) : X → Z := λ x, g (f x).
Notation "g '∘' f" := (comp g f) (at level 11, left associativity, format "g  ∘  f").
