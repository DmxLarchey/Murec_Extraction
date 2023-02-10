Require Import Utf8.

Section arith_lib.

  (* A stripped down to the minimum arithmetic library for le/≤
     and lt/<, with mostly straightforward proofs

     Remember that n ≤ _ : nat → Prop is characterized inductively
     with the two rules
                                    n ≤ m
        ------- le_n n    and     --------- le_S n m
         n ≤ n                     n ≤ S m

     and that "n < m" is defined as "S n ≤ m" *)

  Fact le_n_Sn n : n ≤ S n.
  Proof. do 2 constructor. Qed.

  Fact le_0_n {n} : 0 ≤ n.
  Proof. now induction n; constructor. Qed.

  Fact le_n_S {n m} : n ≤ m → S n ≤ S m.
  Proof. now induction 1; constructor. Qed.

  Fact lt_n_S {n m} : n < m → S n < S m.
  Proof. apply le_n_S. Qed.

  Fact lt_0_Sn {n} : 0 < S n.
  Proof. apply le_n_S, le_0_n. Qed.

  Fact le_trans {n m p} : n ≤ m → m ≤ p → n ≤ p.
  Proof. now induction 2; [ | constructor 2 ]. Qed.

  Fact le_lt_trans {n m p} : n ≤ m → m < p → n < p.
  Proof. intros H; apply le_trans, le_n_S, H. Qed.

  Fact lt_le_weak {n m} : n < m → n ≤ m.
  Proof. apply le_trans, le_n_Sn. Qed.

  (* Small inversion to implement inversion
     lemmas le_S_n and le_n_0 below *)

  Local Fact le_inv {n m} :
       n ≤ m
     → match n, m with
         | 0  , _   => True
         |   _, 0   => False
         | S n, S m => n ≤ m
       end.
  Proof.
    destruct 1; destruct n.
    + exact I.
    + apply le_n.
    + exact I.
    + now apply lt_le_weak.
  Qed.

  Lemma le_S_n n m : S n ≤ S m → n ≤ m.
  Proof. apply @le_inv. Qed.

  Lemma le_n_0 n : n ≤ 0 → n = 0.
  Proof. intros H; apply le_inv in H; now destruct n. Qed.

  Corollary lt_n_0 n : ¬ n < 0.
  Proof. intros H; exact (le_inv H). Qed.

  (* anti-symmetry is the somewhat involved proof,
     by induction on n and then inversion on ≤
     predicates *)

  Lemma le_antisym n m : n ≤ m → m ≤ n → n = m.
  Proof.
    revert m; induction n as [ | n IHn ].
    + intros ? _ Hm; now apply le_n_0 in Hm.
    + intros [ | m ] H₁ H₂.
      * now apply lt_n_0 in H₁.
      * now f_equal; apply IHn; apply le_S_n.
  Qed.

  Fact succ_neq n : S n ≠ n.
  Proof. now induction n; [ | injection 1 ]. Qed.

  (* Follows from anti-symmetry of le *)

  Corollary lt_irrefl {n} : ¬ n < n.
  Proof. intro; apply (succ_neq n), le_antisym; trivial; apply le_n_Sn. Qed.

  (* Decision procedure *)

  Inductive lt_eq_lt n m : Type :=
    | lt_eq_lt_lt : n < m → lt_eq_lt n m
    | lt_eq_lt_eq : n = m → lt_eq_lt n m
    | lt_eq_lt_gt : m < n → lt_eq_lt n m.

  Arguments lt_eq_lt_lt {_ _}.
  Arguments lt_eq_lt_eq {_ _}.
  Arguments lt_eq_lt_gt {_ _}.

  Fixpoint lt_eq_lt_dec n m : lt_eq_lt n m :=
    match n, m with
      | 0  , 0   => lt_eq_lt_eq eq_refl
      | 0  , S _ => lt_eq_lt_lt lt_0_Sn
      | S _, 0   => lt_eq_lt_gt lt_0_Sn
      | S n, S m =>
      match lt_eq_lt_dec n m with
        | lt_eq_lt_lt H => lt_eq_lt_lt (lt_n_S H)
        | lt_eq_lt_eq H => lt_eq_lt_eq (f_equal _ H)
        | lt_eq_lt_gt H => lt_eq_lt_gt (lt_n_S H)
      end
    end.

  (* Additional useful predicates *)
  Definition zer n :=  0 = n.
  Definition pos n :=  ∃k, S k = n.

End arith_lib.

Arguments le_n {_}.
Arguments le_S {_ _}.
Arguments le_n_S {_ _}.
Arguments le_S_n {_ _}.
Arguments le_trans {_ _ _}.
Arguments le_lt_trans {_ _ _}.
Arguments lt_le_weak {_ _}.
Arguments le_antisym {_ _}.
