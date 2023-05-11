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

From MuRec Require Import sigma relations arith_mini between schemes compute_def linear_search.

Section umin_compute.

  Variable (F : nat → nat → Prop)
           (Ffun : functional F)
           (f : ∀n, computeᵤ (F n)).

  Arguments Ffun {_ _ _}.

  (* Instanciation of Dtest, P, Q and PQ_abs *)
  Let Dtest := def_at F.
  Let P := ze_at F.
  Let Q := pos_at F.
  Local Fact PQ_abs : ∀n, Dtest n → P n → Q n → False.
  Proof. intros n _ p (y & q). now generalize (Ffun p q). Qed.

  (* Instanciation of 𝔻ls, ℙre_ls, ℙost_ls and ℙre_𝔻ls using Dtest, P and Q *)
  Let 𝔻 :=  𝔻ls Dtest P.
  Let 𝔻_π₁ := λ {n} (d : 𝔻 n), 𝔻ls_π₁ Dtest P d.
  Let 𝔻_π₂ := λ {n} (d : 𝔻 n) q, 𝔻ls_π₂ Dtest P Q PQ_abs d q.
  Let ℙre := ℙre_ls Dtest P.
  Let ℙost := ℙost_ls Dtest P Q.
  Let ℙre_𝔻 {s} : ex (ℙre s) → 𝔻 s := ℙre_ls_𝔻ls Dtest P.

  Variable (s : nat).

  (* -------------------------------------------------------------------------- *)
  (* Gentle derivation of the desired algorithm from linear_search.v *)

  (* Instanciation of test *)
  Let test n (t : Dtest n) : {P n} + {Q n} :=
    let (k, Hk) := f n ⌊t⌋ᵤ in
    match k return F _ k → _ with
    | 0   => λ e, left e
    | S k => λ e, right ⟪k,e⟫ₚ
    end Hk.

  (* Copied from linear_search.v *)
  Local Fixpoint loop_orig n (d : 𝔻 n) (b : btwn (Dtest ∧₁ Q) s n) : sig (ℙost s) :=
    let t := 𝔻_π₁ d in
    match test n t with
    | left p  => ⟪n, ⟨t,p, b⟩ₚ⟫
    | right q => loop_orig (S n) (𝔻_π₂ d q) (btwn_next b ⟨t,q⟩ₚ)
    end.

  (* Inlining the current instance of test inside loop_orig *)
  Local Fixpoint loop_inline n (d : 𝔻 n) (b : btwn (Dtest ∧₁ Q) s n) : sig (ℙost s) :=
    let t := 𝔻_π₁ d in
    let (k, Hk) := f n ⌊t⌋ᵤ in
    let te := match k return F _ k → _ with
              | 0   => λ e, left e
              | S k => λ e, right ⟪_,e⟫ₚ
              end Hk in
    match te with
    | left p  => ⟪n,⟨t,p, b⟩ₚ⟫
    | right q => loop_inline (S n) (𝔻_π₂ d q) (btwn_next b ⟨t,q⟩ₚ)
    end.

  (* Easy program transformation: the intermediate te is bypassed *)
  Local Fixpoint loop_opt n (d : 𝔻 n) (b : btwn (Dtest ∧₁ Q) s n) : sig (ℙost s) :=
    let t := 𝔻_π₁ d in
    let (k, Hk) := f n ⌊t⌋ᵤ in
    match k return F _ k → _ with
    | 0   => λ e, ⟪n, ⟨t,e, b⟩ₚ⟫
    | S k => λ e, loop_opt (S n) (𝔻_π₂ d ⟪_,e⟫ₚ) (btwn_next b ⟨t, ⟪_,e⟫ₚ⟩ₚ)
    end Hk.

  Definition ℙost_ls s := (Dtest ∧₁ P) ∧₁ btwn (Dtest ∧₁ Q) s.

  (* The last step allows us to bypass t as well without loss of information
     when P ⊆₁ Dtest and Q ⊆₁ Dtest: instead of computing a proof of
     ℙost s, that is  (Dtest ∧₁ P) ∧₁ btwn (Dtest ∧₁ Q) s, we can then compute
     a proof of the equivalent but simpler formula  P ∧₁ btwn Q s.
     In the above loop, we just return e instead of ⟨t,e⟩ₚ, for k = 0,
     and use ⟪_,e⟫ₚ instead of ⟨t, ⟪_,e⟫ₚ⟩ₚ for k a successor; therefore,
     "let t :=..." becomes useless.

     This simplified version of the post-condition happens to be identical to
     umin F s, which is at the same time the pre and the post-condition of the
     intended algorithm (umin_compute), by the very definition of compute.
  *)

  (* The Let before the Fixpoint below forces the inlining of loop inside
     linear_search *)
  Let Fixpoint loop n (d : 𝔻 n) (b : btwn (pos_at F) s n) : sig (umin F s) :=
    let (k,Hk) := f n ⌊𝔻_π₁ d⌋ᵤ in
    match k return F _ k → _ with
    | 0   => λ e, ⟪n, ⟨e,b⟩ₚ⟫
    | S _ => λ e, loop (S n) (𝔻_π₂ d ⟪_,e⟫ₚ) (btwn_next b ⟪_,e⟫ₚ)
    end Hk.

  (* End of the gentle derivation of the desired algorithm from linear_search.v *)
  (* -------------------------------------------------------------------------- *)

  (* Copied from linear_search.v, with ℙost replaced by umin F *)
  Let linear_search : ex (ℙre s) → sig (umin F s) :=
    λ e, loop s (ℙre_𝔻 e) btwn_refl.

  (* umin F is stronger than (actually equivalent to) the pre-condition
     allowing us to compute the initial termination certificate. *)
  Local Fact umin_ℙre : umin F s ⊆₁ ℙre s.
    (* ze_at F ∧₁ btwn (pos_at F) s ⊆₁ (def_at F ∧₁ ze_at F) ∧₁ btwn (def_at F) s *)
  Proof.
    (* structural rules *)
    apply and₁_monotonic; [ apply and₁_intro; [ | apply included₁_refl] | apply btwn_monotonic₁].
    - apply ze_at_def_at.
    - apply pos_at_def_at.
  Qed.

  Definition umin_compute : compute (umin F s) :=
    linear_search  ∘  ex_monotonic umin_ℙre.

End umin_compute.

Arguments umin_compute {F} Ffun Fcomp n : rename.

Section umin₀_compute.

  Variable (F : nat → nat → Prop)
           (Ffun : functional F)
           (f : ∀n, computeᵤ (F n)).

  Definition umin₀_compute : compute (umin₀ F) :=
    sig_monotonic umin_umin₀  ∘  umin_compute Ffun f 0  ∘  ex_monotonic umin₀_umin.

End umin₀_compute.

Arguments umin₀_compute {F} Ffun Fcomp n : rename.



