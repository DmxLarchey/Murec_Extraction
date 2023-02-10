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

From MuRec Require Import relations arith_mini.

Section btwn.

  Variable P : nat → Prop.

  (* Weak between formulated in FO arithmetic *)
  Local Definition wbtwn n m := ∀ i, n ≤ i → i < m → P i.

  (* Simulated constructors for weak between *)
  Local Fact wbtwn_refl n : wbtwn n n.
  Proof. intros ? H₁ H₂; destruct (lt_irrefl (le_lt_trans H₁ H₂)). Qed.

  Local Fact wbtwn_next {n m} : wbtwn n m → P m → wbtwn n (S m).
  Proof.
    intros Bnm Hm i H₁ H₂.
    destruct (le_S_n H₂); trivial.
    apply Bnm; trivial.
    now apply le_n_S.
  Qed.

  (* Between formulated in FO arithmetic *)
  Definition btwn n m := n ≤ m ∧ wbtwn n m.

  (* Simulated constructors for between *)
  Fact btwn_refl n : btwn n n.
  Proof. split; [apply le_n | apply wbtwn_refl]. Qed.

  Fact btwn_next n m : btwn n m → P m → btwn n (S m).
  Proof. intros [b w] p; split; [apply le_S, b | apply (wbtwn_next w p)]. Qed.

End btwn.

Arguments btwn_refl {P n}.
Arguments btwn_next {P n m}.

(* Monotonicity *)
Local Fact wbtwn_monotonic (P Q : nat → Prop) : P ⊆₁ Q → wbtwn P ⊆₂ wbtwn Q.
Proof. now intros M ? ? Hnm ? ? ?; apply M, Hnm. Qed.

Fact btwn_monotonic (P Q : nat → Prop) : P ⊆₁ Q → btwn P ⊆₂ btwn Q.
Proof.
  intros ? ? ? [? H]; split; trivial.
  revert H; now apply wbtwn_monotonic.
Qed.

Fact btwn_monotonic₁ {P Q : nat → Prop} s : P ⊆₁ Q → btwn P s ⊆₁ btwn Q s.
Proof. exact (λ i_pq, btwn_monotonic P Q i_pq s). Qed.

(* Choice property for between *)
Fact btwn_eq_or_holds {P a n m} : btwn P a n → btwn P a m → n = m ∨ P n ∨ P m.
Proof.
  intros [an wn] [am wm].
  destruct (lt_eq_lt_dec n m).
  + right; left; now apply wm.
  + now left.
  + right; right; now apply wn.
Qed.

(* A useful interval reverse induction principle for nat,
   suitable for btwn, see below *)
Local Definition nat_interval_rev_ind {P : nat → Prop} :
  ∀{a b}, a ≤ b → (∀n, a <= n → n < b → P (S n) → P n) → P b → P a :=
  fix loop {a b} (Hab : a <= b) :=
    match Hab with
      | le_n     => λ _  Pa,  Pa
      | le_S Hab => λ HP PSb, loop Hab (λ n Ha Hb, HP _ Ha (le_n_S (lt_le_weak Hb)))
                                       (HP _ Hab le_n PSb)
    end.

(* (Reverse) induction principle for between *)
Corollary btwn_ind (P : nat → Prop) a b : btwn (λ n, P (S n) → P n) a b → P b → P a.
Proof. intros [Hab HP]; exact (nat_interval_rev_ind Hab HP). Qed.



