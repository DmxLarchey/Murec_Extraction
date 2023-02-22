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

From MuRec Require Import sigma relations arith_mini between.

Section linear_search.

  (* P and Q are two predicates on nat which are
     incompatible (over Dtest). For instance if
     b : nat → bool, then we could choose

            P n := b n = true
        and Q n := b n = false

     but we intentionnally do NOT require totality
     of P and Q here.

     We only require totality over Dtest, see "test" below *)

  Variables (Dtest P Q : nat → Prop)
            (PQ_abs : ∀{n}, Dtest n → P n → Q n → False).

  (* 𝔻ls : nat → Prop reads as "𝔻(omain of) l(inear) s(earch)"

     The predicate 𝔻ls n characterizes inductively the n such
     that for some m above n, P m holds, and Dtest holds on [n,m] *)

  Inductive 𝔻ls n : Prop :=
  | 𝔻ls_stop : (Dtest ∧₁ P) n → 𝔻ls n
  | 𝔻ls_next : Dtest n → 𝔻ls (S n) → 𝔻ls n.

  Arguments 𝔻ls_stop {_}.
  Arguments 𝔻ls_next {_}.

  Definition 𝔻ls_π₁ {n} (d : 𝔻ls n) : Dtest n :=
    match d with
    | 𝔻ls_stop ⟨t,_⟩ₚ => t
    | 𝔻ls_next  t _   => t
    end.

  (* This projection 𝔻ls_π₂ : ∀n, 𝔻ls n → Q n → 𝔻ls (S n)
     is used *critically* for termination in the Coq

       Fixpoint loop _ (d : 𝔻 _) ... { struct d } :=
             ... loop (𝔻ls_π₂ d q) ...

     below. Indeed, 𝔻ls_π₂ d q : 𝔻ls (S n) is a sub-term
     of d : 𝔻ls n. Hence it satisfies the guardedness condition
     of the termination checker.

     We insist that the exact term here is *essential* because the
     guardedness condition is *not* compositional. *)

  Definition 𝔻ls_π₂ {n} (d : 𝔻ls n) : Q n → 𝔻ls (S n) :=
    match d with
    (* An (empty) match on _ : False is a sub-term (of anything) *)
    | 𝔻ls_stop ⟨t,p⟩ₚ => λ q, match PQ_abs t p q with end
    (* dₛ : 𝔻ls (S n) is a sub-term of 𝔻ls_next _ dₛ : 𝔻ls n *)
    | 𝔻ls_next _ dₛ   => λ _, dₛ
    end.

  (* The existence of n such that ℙre_ls s n is
     the pre-condition for a terminating
     linear search starting at s *)
  Definition ℙre_ls s := (Dtest ∧₁ P) ∧₁ btwn Dtest s.

  (* The value n such that ℙost_ls s n characterizes,
     as a post-condition, the output value of linear
     search starting at s *)
  Definition ℙost_ls s := (Dtest ∧₁ P) ∧₁ btwn (Dtest ∧₁ Q) s.

  (* The pre-condition is enough the show that s belongs
     to the inductive domain predicate, ensurring termination
     on input s of the fixpoint loop below *)
  Lemma ℙre_ls_𝔻ls {s} : (∃n, ℙre_ls s n) → 𝔻ls s.
  Proof.
    intros (n & tp & b).
    generalize (𝔻ls_stop tp). apply btwn_ind.
    revert b. apply btwn_monotonic.
    exact @𝔻ls_next.
  Qed.

  (* test is specified by ∀n, Dtest n → {P n} + {Q n}
     so it is possible that neither P nor Q hold outside of Dtest *)
  Variable test : ∀n, Dtest n → {P n} + {Q n}.

  (* loop_ℕ : ∀n, 𝔻ls n → nat

     with inductive domain predicate d : 𝔻ls n
     implements linear search and computes the first m
     such that P m, starting the search at n,
     but without proving this post-condition.

     Notice that it is a "recursive terminal" function. *)

  Local Fixpoint loop_ℕ n (d : 𝔻ls n) : nat :=
    match test n (𝔻ls_π₁ d) with
    | left p  => n
    | right q => loop_ℕ (S n) (𝔻ls_π₂ d q)
    end.

  (* In order to have a meaningful post-condition,
     we now fix a starting point of linear search *)
  Variable s : nat.

  (* loop : ∀n, 𝔻ls n → btwn (Dtest ∧₁ Q) s n → {x | ℙost_ls s x}

     with inductive domain predicate d : 𝔻ls n
     and invariants b : btwn (Dtest ∧₁ Q) s
     implements linear search and computes the least m greater or equal
     to s such that P m, starting the search at n.

     It is still written as a "recursive terminal" function, including
     with respect to the computation of the proof of the post-condition. *)

  Let Fixpoint loop n (d : 𝔻ls n) (b : btwn (Dtest ∧₁ Q) s n) : sig (ℙost_ls s) :=
    let t := 𝔻ls_π₁ d in
    match test n t with
    | left p  => ⟪n, ⟨t,p, b⟩ₚ⟫
    | right q => loop (S n) (𝔻ls_π₂ d q) (btwn_next b ⟨t,q⟩ₚ)
    end.

  (* Wrapping up to get fully spec'd linear search algorithm,
     specifications expressed the language of FO arithmetic.
     From the (non-informative) existence of a value n above s
     which satisfies
                P n ∧ Dtest s ∧ ... ∧ Dtest n
     we compute a value m, above s and minimal in the sense that,
          P m ∧ Dtest s ∧ ... ∧ Dtest m ∧ Q s ∧ ... ∧ Q (m-1)
     Indeed, remember that P and Q are incompatible on Dtest.

     Notice, that it is perfectly possible that after m, neither
     P nor Q hold, because Dtest wouldn't be satisfied. *)

  Definition linear_search : (∃ n, ℙre_ls s n) → { m | ℙost_ls s m } :=
    λ e, loop s (ℙre_ls_𝔻ls e) btwn_refl.

End linear_search.

Arguments linear_search {_ _ _}.

