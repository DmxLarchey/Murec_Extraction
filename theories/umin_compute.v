Require Import Utf8.

From MuRec Require Import sigma relations arith_mini between schemes computable_def linear_search.

Section umin_compute.

  Variable (F : nat → nat → Prop)
           (Ffun : functional F)
           (f : ∀n, computable (F n)).

  Arguments Ffun {_ _ _}.

  (* Instanciation of Dtest, P, Q and PQ_abs *)
  Let Dtest := def_at F.
  Let P := ze_at F.
  Let Q := pos_at F.
  Local Fact PQ_abs : ∀n, Dtest n → P n → Q n → False.
  Proof. intros n _ p (y & q). now generalize (Ffun p q). Qed.

  (* Instanciation of 𝔻ls, ℙre_ls, ℙost_ls and ℙre_𝔻ls using Dtest, P and Q *)
  Let 𝔻 := 𝔻ls Dtest P.
  Let 𝔻_π₁ := λ {n} (d : 𝔻 n), 𝔻ls_π₁ Dtest P d.
  Let 𝔻_π₂ := λ {n} (d : 𝔻 n) q, 𝔻ls_π₂ Dtest P Q PQ_abs d q.
  Let ℙre := ℙre_ls Dtest P.
  Let ℙost := ℙost_ls Dtest P Q.
  Let ℙre_𝔻 {s} : ex (ℙre s) → 𝔻 s := ℙre_ls_𝔻ls Dtest P.

  Variable (s : nat).

  (* ---------------------------------------------------------------------- *)
  (* The algorithm below can be derived from the one in linear_search.v.
     umin F s, that is ze_at F ∧₁ btwn (pos_at F) s, is at the same time the
     pre and the post-condition of the intended algorithm (umin_compute), by
     the definition of computable.
     It is also an opportunistic version of ℙost.
     See umin_compute_details.v for details. *)
  (* ---------------------------------------------------------------------- *)

  (* The Let before the Fixpoint below forces the inlining of loop inside 
     linear_search *)
  Let Fixpoint loop n (d : 𝔻 n) (b : btwn (pos_at F) s n) : sig (umin F s) :=
    let (k,Hk) := f n (𝔻_π₁ d) in
    match k return F _ k → _ with
    | 0   => λ e, ⟪n, ⟨e,b⟩ₚ⟫
    | S _ => λ e, loop (S n) (𝔻_π₂ d ⟪_,e⟫ₚ) (btwn_next b ⟪_,e⟫ₚ)
    end Hk.

  (* Copied from linear_search.v, with ℙost replaced by umin F *)
  Let linear_search : ex (ℙre s) → sig (umin F s) :=
    λ e, loop s (ℙre_𝔻 e) btwn_refl.

  (* umin F is stronger than (actually equivalent to) the pre-condition
     allowing us to compute the initial termination certificate. *)
  Local Fact umin_ℙre :  umin F s ⊆₁ ℙre s.
    (* ze_at F ∧₁ btwn (pos_at F) s ⊆₁ (def_at F ∧₁ ze_at F) ∧₁ btwn (def_at F) s *)
  Proof.
    (* structural rules *)
    apply and₁_monotonic; [ apply and₁_intro; [ | apply included₁_refl] | apply btwn_monotonic₁].
    - apply ze_at_def_at.
    - apply pos_at_def_at.
  Qed.

  Definition umin_compute : computable (umin F s) :=
    linear_search  ∘  ex_monotonic umin_ℙre.

End umin_compute.

Arguments umin_compute {F} Ffun Fcomp n : rename.

Section umin₀_compute.

  Variable (F : nat → nat → Prop)
           (Ffun : functional F)
           (f : ∀n, computable (F n)).

  Definition umin₀_compute : computable (umin₀ F) :=
    sig_monotonic umin_umin₀  ∘  umin_compute Ffun f 0  ∘  ex_monotonic umin₀_umin.

End umin₀_compute.

Arguments umin₀_compute {F} Ffun Fcomp n : rename.



