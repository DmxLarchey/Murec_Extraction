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

From Coq Require Import Utf8 Extraction.

From MuRec Require Import sigma relations arith_mini between index vec.

Reserved Notation " '⟦' f '⟧' " (at level 1, format "⟦ f ⟧").
Reserved Notation " '⟦' f '⟧ₒ' " (at level 1, format "⟦ f ⟧ₒ").

(* The higher-order scheme of primitive recursion *)

Section primitive_recursion.

  Context   {Xa Y : Type}
            (F : Xa → Y → Prop)
            (G : Xa → nat → Y → Y → Prop).

  Definition prim_rec x₀ :=
    fix loop n :=
      match n with
      | 0   => F x₀
      | S n => (G x₀ n) ⋄ (loop n)
      end.

  Hypothesis Ffun : functional F.
  Hypothesis Gfun : ∀ x₀ n, functional (G x₀ n).

  Fact prim_rec_fun x₀ : functional (prim_rec x₀).
  Proof.
    intros n; induction n; cbn.
    + apply Ffun.
    + now apply rel_subst_fun.
  Qed.

End primitive_recursion.

Arguments prim_rec_fun {Xa Y F G} Ffun Gfun {_ _ _ _}.

(* The scheme of unbounded minimization *)

Section unbounded_minimisation.

  Variable (F : nat → nat → Prop).

  Definition umin s y := F y 0 ∧ btwn (λ n, ∃k, F n (S k)) s y.
  Definition umin₀ y :=  F y 0 ∧ ∀n, n < y → ∃k, F n (S k).

  Fact umin_umin₀ y : umin 0 y → umin₀ y.
  Proof.
    intros (H1 & H2 & H3); split.
    + exact H1.
    + intro; apply H3, le_0_n.
  Qed.

  Fact umin₀_umin y : umin₀ y → umin 0 y.
  Proof.
    intros (H1 & H2); repeat split.
     + exact H1.
     + apply le_0_n.
     + intros ? ?; apply H2.
  Qed.

  Hypothesis Ffun : functional F.

  Arguments Ffun {_ _ _}.

  Fact umin_fun : functional umin.
  Proof.
    intros s y₁ y₂ [z1 py₁] [z2 py₂].
    destruct (btwn_eq_or_holds py₁ py₂) as [ [] | [ [? FS] | [? FS] ] ].
    - reflexivity.
    - discriminate (Ffun z1 FS).
    - discriminate (Ffun z2 FS).
  Qed.

  Fact umin₀_fun : functional₀ umin₀.
  Proof.
    intros y1 y2 H1 H2.
    apply (umin_fun 0); now apply umin₀_umin.
  Qed.

End unbounded_minimisation.

Arguments umin_umin₀ {F}.
Arguments umin₀_umin {F}.

(* The syntax of µ-algorithms *)

Unset Elimination Schemes.

Inductive recalg  : nat → Type :=
  | ra_zero       : recalg 0
  | ra_succ       : recalg 1
  | ra_proj {a}   : idx a → recalg a
  | ra_comp {a b} : recalg b → vec (recalg a) b → recalg a
  | ra_prec {a}   : recalg a → recalg (S (S a)) → recalg (S a)
  | ra_umin {a}   : recalg (S a) → recalg a
  .

Set Elimination Schemes.

(* The relational semantics of µ-algorithms *)

Section relational_semantics.

  Notation IO a := (vec nat a → nat → Prop).

  Definition Zr       : IO 0 := λ _ y, y = 0.
  Definition Sc       : IO 1 := λ V1 y, y = 1 + vec_head V1.
  Definition Id {a} i : IO a := λ Va y, y = Va.[i].

  Definition Cn {a b} (φb : IO b) (ψab : vec (IO a) b) : IO a :=
    λ Va y, ∃Vb, φb Vb y ∧ ∀ i, ψab.[i] Va Vb.[i].

  Definition Pr {a} (φa : IO a) (ψa'' : IO (2+a)) : IO (1+a) :=
    vec_S_inv (λ n Va, prim_rec φa (λ Wa m y, ψa'' (m ∷ y ∷ Wa)) Va n).

  Definition Mn {a} (φa' : IO (1+a)) : IO a :=
    λ Va, umin₀ (λ y, φa' (y ∷ Va)).

  Fixpoint ra_sem {a} (Sa : recalg a) : IO a :=
    match Sa with
    | ra_zero         => Zr
    | ra_succ         => Sc
    | ra_proj i       => Id i
    | ra_comp Sb Sab  => Cn ⟦Sb⟧ (vec_map (λ f, ⟦f⟧) Sab)
    | ra_prec Sa Sa'' => Pr ⟦Sa⟧ ⟦Sa''⟧
    | ra_umin Sa'     => Mn ⟦Sa'⟧
    end
  where "⟦ Sa ⟧" := (ra_sem Sa).

  Local Fact Zr_fun : functional Zr.           Proof. now intros ? ? ? ? ->. Qed.
  Local Fact Sc_fun : functional Sc.           Proof. now intros ? ? ? ? ->. Qed.

  Local Fact Id_fun {a} (i : idx a) : functional (Id i).
  Proof. now cbn; unfold Id; intros; subst. Qed.

  Local Fact Cn_fun {a b} {φb : IO b} {ψab : vec (IO a) b} :
            functional φb
          → (∀i, functional ψab.[i])
          → functional (Cn φb ψab).
  Proof.
    intros φb_fun ψab_fun Va y₁ y₂ [ Vb₁ [ Hy1 ? ] ] [ Vb₂ [ Hy2 ? ] ].
    replace Vb₁ with Vb₂ in Hy1.
    + now apply φb_fun with (1 := Hy1).
    + apply vec_prj_ext; intros i.
      now apply (ψab_fun i Va).
  Qed.

  Local Fact Pr_fun {a} {φa : IO a} {φa'' : IO (2+a)} :
            functional φa
          → functional φa''
          → functional (Pr φa φa'').
  Proof.
    intros ? ? v ? ?.
    destruct (vec_inv v).
    apply prim_rec_fun; trivial.
    intros ? ? ?; trivial.
  Qed.

  Local Fact Mn_fun {a} {φa' : IO (1+a)} :
            functional φa'
          → functional (Mn φa').
  Proof.
    intros ? ? ? ?; apply umin₀_fun.
    intros ?; trivial.
  Qed.

  Theorem ra_sem_fun : ∀{a} (Sa : recalg a), functional ⟦Sa⟧.
  Proof.
    refine (fix ra_sem_fun a Sa { struct Sa } := _).
    destruct Sa; cbn [ra_sem];
      [ apply Zr_fun | apply Sc_fun | apply Id_fun | apply Cn_fun | apply Pr_fun | apply Mn_fun];
      try apply ra_sem_fun.
    intro; rewrite vec_prj_map; apply ra_sem_fun.
  Qed.

End relational_semantics.

Notation "⟦ Sa ⟧" := (ra_sem Sa).

(* The computational contents of µ-algorithms *)

Definition compute {X} (P : X → Prop) := ex P → sig P.

(* Iteration of computation on a vector *)

Section vec_map_compute.

  Variables (X Y : Type)
            (F : X → Y → Prop)
            (f : ∀ p : { x | ex (F x) }, sig (F (π₁ p))).

  Section vec_map_compute_props.

    Local Fact vmc_PO1 i : F ⟨⟩.[i] ⟨⟩.[i].
    Proof. destruct (idx_inv i). Qed.

    Variables (n : nat)
              (x : X) (v : vec X n)
              (y : Y) (w : vec Y n)
              (Fxy : F x y)
              (Fvw : ∀ i, F v.[i] w.[i]).

    Local Fact vmc_PO2 i : F (x ∷ v).[i] (y ∷ w).[i].
    Proof. now destruct (idx_inv i); cbn. Qed.

  End vec_map_compute_props.

  Arguments vmc_PO2 {_ _ _ _ _}.

  Definition vec_map_compute : ∀{n} (v : vec X n), compute (λ w, ∀i, F v.[i] w.[i]) :=
    let fix loop {n} (v : vec X n) : (∀i, ex (F v.[i])) → _ :=
      match v with
      | ⟨⟩    => λ _,   ⟪⟨⟩, vmc_PO1⟫
      | x ∷ v => λ Fxv, let (y, x_y) := f ⟪x,Fxv 𝕆⟫ in
                        let (w, v_w) := loop v (λ i, Fxv (𝕊 i)) in
                        ⟪y ∷ w, vmc_PO2 x_y v_w⟫
      end in
    λ n v Fv, loop v (let (w, Fvw) := Fv in λ i, ⟪w.[i], Fvw i⟫ₚ).

End vec_map_compute.

Arguments vec_map_compute {_ _} _ _ {n} v.

(* Computation of primitive recursion *)

Section prim_rec_compute.

  Variables (X Y : Type)
            (F : X → Y → Prop)
            (Ffun : functional F)
            (Fcomp : ∀ p : { x | ex (F x) }, sig (F (π₁ p)))
            (G : X → nat → Y → Y → Prop)
            (Gfun : ∀ x n, functional (G x n))
            (Gcomp : ∀ x n (p : { y | ex (G x n y) }), sig (G x n (π₁ p)))
            (x : X).

  Section prim_rec_compute_props.

    Variables (n : nat) (d : ∃y, prim_rec F G x (S n) y).

    Local Fact prc_TC1 : ∃y, prim_rec F G x n y.
    Proof.
      destruct d as (? & yn₁ & ? & ?).
      now exists yn₁.
    Qed.

    Variables (yn : Y) (Hyn : prim_rec F G x n yn).

    Local Fact prc_TC2 : ∃y, G x n yn y.
    Proof.
      destruct d as (yn₁' & yn₁ & Hyn₁ & Hyn₁').
      exists yn₁'.
      now rewrite <- (prim_rec_fun Ffun Gfun Hyn₁ Hyn).
    Qed.

    Variables (yn' : Y) (Hyn' : G x n yn yn').

    Local Fact prc_PO1 : prim_rec F G x (S n) yn'.
    Proof. now exists yn. Qed.

  End prim_rec_compute_props.

  Arguments prc_TC1 {_} _.
  Arguments prc_TC2 {_} _ {_} _.
  Arguments prc_PO1 {_ _} _ {_} _.

  Fixpoint prim_rec_compute m : compute (prim_rec F G x m) :=
    match m with
      | 0   => λ d, Fcomp ⟪x,d⟫
      | S n => λ d, let (yn , y_yn)   := prim_rec_compute n (prc_TC1 d) in
                    let (yn', yn_yn') := Gcomp x n ⟪yn,prc_TC2 d y_yn⟫ in
                    ⟪yn', prc_PO1 y_yn yn_yn'⟫
    end.

End prim_rec_compute.

Arguments prim_rec_compute {X Y F} Ffun Fcomp {G} Gfun Gcomp x m.

(* Computation of unbounded minimization *)

Section umin_compute.

  Variable (F : nat → nat → Prop)
           (Ffun : functional F)
           (f : ∀ p : { n | ex (F n) }, sig (F (π₁ p))).
  Arguments Ffun {_ _ _}.

  Let T n := ∃k, F n k.
  Let P n := F n 0.
  Let Q n := ∃k, F n (S k).

  Local Fact PQ_abs : ∀{n}, T n → P n → Q n → False.
  Proof. intros n _ p (y & q). now generalize (Ffun p q). Qed.

  Inductive 𝔻umin n : Prop :=
  | 𝔻umin_stop : T n → P n → 𝔻umin n
  | 𝔻umin_next : T n → 𝔻umin (S n) → 𝔻umin n.

  Arguments 𝔻umin_stop {_}.
  Arguments 𝔻umin_next {_}.

  Definition 𝔻umin_π₁ {n} (d : 𝔻umin n) : T n :=
    match d with
    | 𝔻umin_stop t _ => t
    | 𝔻umin_next t _ => t
    end.

  Definition 𝔻umin_π₂ {n} (d : 𝔻umin n) : Q n → 𝔻umin (S n) :=
    match d with
    | 𝔻umin_stop t p  => λ q, match PQ_abs t p q with end
    | 𝔻umin_next _ dₛ => λ _, dₛ
    end.

  Definition ℙre_umin s := (T ∧₁ P) ∧₁ btwn T s.
  Definition ℙost_umin s := (T ∧₁ P) ∧₁ btwn (T ∧₁ Q) s.

  Lemma ℙre_umin_𝔻umin {s} : (∃n, ℙre_umin s n) → 𝔻umin s.
  Proof.
    intros (n & (t & p) & b).
    generalize (𝔻umin_stop t p). apply btwn_ind.
    revert b. apply btwn_monotonic.
    exact @𝔻umin_next.
  Qed.

  Variable s : nat.

  Let Fixpoint loop n (d : 𝔻umin n) (b : btwn Q s n) : sig (umin F s) :=
    let (k,Hk) := f ⟪n,𝔻umin_π₁ d⟫ in
    match k return F _ k → _ with
    | 0   => λ e, ⟪n, ⟨e,b⟩ₚ⟫
    | S _ => λ e, loop (S n) (𝔻umin_π₂ d ⟪_,e⟫ₚ) (btwn_next b ⟪_,e⟫ₚ)
    end Hk.

  Let linear_search : ex (ℙre_umin s) → sig (umin F s) :=
    λ e, loop s (ℙre_umin_𝔻umin e) btwn_refl.

  Local Fact umin_ℙre_umin :  umin F s ⊆₁ ℙre_umin s.
  Proof.
    (* structural rules *)
    apply and₁_monotonic; [ apply and₁_intro; [ | apply included₁_refl] | apply btwn_monotonic₁].
    - now exists 0.
    - intros ? (k & ?); now exists (S k).
  Qed.

  Definition umin_compute : compute (umin F s) :=
    linear_search  ∘  ex_monotonic umin_ℙre_umin.

End umin_compute.

Arguments umin_compute {F} Ffun Fcomp n : rename.

(* Computation of unbounded minimization, starting from 0 *)

Section umin₀_compute.

  Variable (F : nat → nat → Prop)
           (Ffun : functional F)
           (f : ∀ p : { n | ex (F n) }, sig (F (π₁ p))).

  Definition umin₀_compute : compute (umin₀ F) :=
    sig_monotonic umin_umin₀  ∘  umin_compute Ffun f 0  ∘  ex_monotonic umin₀_umin.

End umin₀_compute.

Arguments umin₀_compute {F} Ffun Fcomp n : rename.

(* Computation of the schemes of µ-algorithms *)

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
                       (λ p, cSa (π₁ p) (π₂ p))
                       (λ _ _ _, ra_sem_fun _ _)
                       (λ V n x, cSa'' (n ∷ π₁ x ∷ V) (π₂ x))
                       Va
                       z
    ).

End Pr_compute.

Arguments Pr_compute {a} {Sa} cSa {Sa''} cSa''.

Section Mn_compute.

  Variables (a : nat) (Sa' : recalg (1+a)) (cSa' : ∀Va', compute (⟦Sa'⟧ Va')).

  Definition Mn_compute Va : compute (Mn ⟦Sa'⟧ Va) :=
    umin₀_compute (λ _, ra_sem_fun _ _)
                  (λ p, cSa' (π₁ p ∷ Va) (π₂ p)).

End Mn_compute.

Arguments Mn_compute {a} {Sa'} cSa'.

Fixpoint ra_compute {k} (Sk : recalg k) { struct Sk } : ∀Vk : vec nat k, compute (⟦Sk⟧ Vk) :=
  match Sk with
  | ra_zero         => Zr_compute
  | ra_succ         => Sc_compute
  | ra_proj i       => Id_compute i
  | ra_comp Sb Sab  => Cn_compute ⟦Sb⟧ₒ (λ Va dVa, vec_map_compute (λ x, ⟦x⟧ Va) (λ p, ⟦π₁ p⟧ₒ Va (π₂ p)) Sab dVa)
  | ra_prec Sb Sb'' => Pr_compute ⟦Sb⟧ₒ ⟦Sb''⟧ₒ
  | ra_umin Sb'     => Mn_compute ⟦Sb'⟧ₒ
  end
where "⟦ f ⟧ₒ" := (ra_compute f).

Arguments ra_compute {k} Sk Vk.

Check @ra_compute.
Print Assumptions ra_compute.

Definition coq_is_total a (Sa : recalg a) : (∀Va, ∃y, ⟦Sa⟧ Va y) → { f | ∀Va, ⟦Sa⟧ Va (f Va) } :=
  λ cSa, reify (λ Va, ra_compute Sa Va (cSa Va)).

Check coq_is_total.
Print Assumptions coq_is_total.

Extraction Inline vec_S_inv.
Extraction Inline sig_monotonic comp reify.
Extraction Inline umin₀_compute.
Extraction Inline Id_compute Zr_compute Sc_compute Pr_compute Mn_compute Cn_compute.

Extract Inductive idx => "nat" [ "O" "S" ].

Extract Inductive vec => "list" [ "[]" "(::)" ].

Extraction Implicit idx_fst [n].
Extraction Implicit idx_nxt [n].

Extraction Implicit vec         [1].
Extraction Implicit vec_cons    [n].
Extraction Implicit vec_prj     [n].

Extraction Implicit recalg      [1].
Extraction Implicit ra_proj     [a].
Extraction Implicit ra_comp     [a b].
Extraction Implicit ra_prec     [a].
Extraction Implicit ra_umin     [a].

Extraction Implicit vec_map_compute [n].
Extraction Implicit Id_compute [a].

Extraction Implicit ra_compute [k].
Extraction Implicit coq_is_total [a].

Recursive Extraction ra_compute.






