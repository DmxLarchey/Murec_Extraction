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

(** Textbook reference:
    [BBJ2002]: Computability and Logic
               Boolos, G.S. and Burgess, J.P. and Jeffrey, R.C.
               4th Edition, Cambridge University Press, 2002.
*)

From Coq Require Import Utf8.

From MuRec Require Import relations arith_mini between.

Section primitive_recursion.

  (** The fixpoint computing primitive recursion following [BBJ2002] pp 67
      where H := prim_rec, F and G represent respectively the (to be proved
      functional) relations h, f and g, ie. for ⇀ denoting partial functions
      we have the following encoding of types

        f : Xa ⇀ Y             ~~>  F : Xa → Y → Prop
        g : Xa ⨯ nat ⨯ Y ⇀ Y   ~~>  G : Xa → nat → Y → Y → Prop
        h : Xa ⨯ nat ⇀ Y       ~~>  H : Xa → nat → Y → Prop

      and the following encoding for the recursive equations

         h (x₀, 0)   = f(x₀)              ~~>  H x₀ 0 = F x₀
         h (x₀, S n) = g(x₀, n, h(x₀,n))  ~~>  H x₀ (S n) = (G x₀ n) ⋄ (H x₀ n)

      Notice that in [BBJ2002], Xa := nat^a and Y := nat but the definition
      can be made more polymorphic.

      In [BBJ2002] the primitive recursive scheme is written as follows,
      with x in place of x₀ and y in place of n:
         h(x₀, 0) = f(x),  h(x₀, n') = g(x₀, n, h(x₀,n))    (Pr)

     *)

  Context   {Xa Y : Type}
            (F : Xa → Y → Prop)
            (G : Xa → nat → Y → Y → Prop).

  Definition prim_rec x₀ := nat_rect (λ _, Y → Prop) (F x₀) (λ n p, (G x₀ n) ⋄ p).

  Definition prim_rec_alt x₀ :=
    fix loop n :=
      match n with
      | 0   => F x₀
      | S n => (G x₀ n) ⋄ (loop n)
      end.

  Goal prim_rec = prim_rec_alt.
  Proof. reflexivity. Qed.

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

Section unbounded_minimisation.

  (** In [BBJ2002] pp 70 unbounded minimization is written as follows:

                          / y         if f(x₁,...,xₙ, y) = 0, and for all t < y,
      Mn[f](x₁,...,xₙ) = {               f(x₁,...,xₙ, t) is defined and ≠ 0
                          \ undefined if there is no such y.

      This definition is adapted here as follows:
      - at this stage, x₁,...,xₙ are ignored;
      - we consider unbounded minimization from a starting number denoted by s
        ([BBJ2002] corresponds to the special case where s = 0);
        the reason is that, even if the semantics of (AST of) mu-recursive algorithms,
        consideres only s = 0, the intended minimization algorithm is actually able to
        start at any s, a fact to be used when reasoning about this algorithm.

      Altogether, we state that F is 0 at y and strictly positive (ie a successor)
      from s (included) to y (excluded).
   *)

  Variable (F : nat → nat → Prop).

  Definition ze_at y  :=     F y 0.
  Definition def_at t := ∃k, F t k.
  Definition pos_at t := ∃k, F t (S k).

  Fact ze_at_def_at : ze_at ⊆₁ def_at.
  Proof. now intros n ?; exists 0. Qed.
  Fact pos_at_def_at : pos_at ⊆₁ def_at.
  Proof. now intros n (k & ?); exists (S k). Qed.

  Definition umin s y := ze_at y ∧ btwn pos_at s y.
  Definition umin₀ y := ze_at y ∧ ∀n, n < y → pos_at n.

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

