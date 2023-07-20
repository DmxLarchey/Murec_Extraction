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

From MuRec Require Import sigma relations schemes compute_def.

Section prec_compute.

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

End prec_compute.

Arguments prim_rec_compute {X Y F} Ffun Fcomp {G} Gfun Gcomp x m.
