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

From MuRec Require Import sigma relations index vec computable_def.

Section vec_dmap.

  Variables (X Y : Type)
            (F : X → Y → Prop)
            (f : ∀ x, ex (F x) → sig (F x)).

  Section vec_map_compute_props.

    Local Fact vdm_PO1 i : F ⟨⟩.[i] ⟨⟩.[i].
    Proof. destruct (idx_inv i). Qed.

    Variables (x : X) (n : nat) (v : vec X n) (y : Y) (w : vec Y n)
              (Fx : F x y)
              (Fv : ∀ i, F v.[i] w.[i]).

    Local Fact vdm_PO2 i : F (x ∷ v).[i] (y ∷ w).[i].
    Proof. now destruct (idx_inv i); cbn. Qed.

  End vec_map_compute_props.

  Arguments vdm_PO2 {_ _ _ _ _}.

  Fixpoint vec_dmap {n} (v : vec X n) : (∀i, ex (F v.[i])) → { w | ∀i, F v.[i] w.[i] } :=
    match v with 
    | ⟨⟩    => λ _,   ⟪⟨⟩, vdm_PO1⟫
    | x ∷ v => λ hxv, let (y,hy) := f x (hxv 𝕆) in 
                      let (w,hw) := vec_dmap v (λ i, hxv (𝕊 i)) in 
                      ⟪y ∷ w, vdm_PO2 hy hw⟫
    end.

(*
  Definition vec_dmap {n} {v : vec X n} : (exists w, ∀i, F v.[i] w.[i]) → { w | ∀i, F v.[i] w.[i] }.
  Proof.
    intros H; apply vec_dmap_rec.
    destruct H as (w & Hw); intros i; now exists w.[i].
  Qed.
*)

End vec_dmap.

Check vec_dmap.
Arguments vec_dmap {_ _ _} _ {n} v.


Section hvec_map_compute.

  (** Any X-indexed family of computable Y-predicates can be lifted on vectors,
      ie partial vector map *)

  Variable (C X Y : Type)
           (F : C → X → Y → Prop).

  Section vec_map_compute_props.

    Variable x : X.

    Local Fact hvmc_PO1 i : F ⟨⟩.[i] x ⟨⟩.[i].
    Proof. destruct (idx_inv i). Qed.

    Variables (c : C) (y : Y) (a : nat) (Ca : vec C a) (Ya : vec Y a)
              (Fc : F c x y)
              (FCa : ∀ i, F Ca.[i] x Ya.[i]).

    Local Fact hvmc_PO2 i : F (c ∷ Ca).[i] x (y ∷ Ya).[i].
    Proof. now destruct (idx_inv i); cbn. Qed.

  End vec_map_compute_props.

  Arguments hvmc_PO1 {_}.
  Arguments hvmc_PO2 {_ _ _ _ _ _}.

  Fixpoint hvec_map_compute {b} {v : vec C b} (hv : hvec (λ c, forall y, ex (F c y) → sig (F c y)) v) :
         ∀y, (∀i, ex (F v.[i] y)) → { w | ∀i, F v.[i] y w.[i] } :=
    match hv with
    | hvec_nil =>        λ _ _,  ⟪⟨⟩, hvmc_PO1⟫
    | hvec_cons xF hv => λ y hy, let (x,Fx) := xF y (hy 𝕆) in
                                 let (w,Fw) := hvec_map_compute hv y (λ i, hy (𝕊 _)) in
                                 ⟪x ∷ w, hvmc_PO2 Fx Fw⟫
    end.

End hvec_map_compute.

Arguments hvec_map_compute {C X Y F b v}.

