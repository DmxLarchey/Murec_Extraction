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

From Coq Require Import Utf8 Extraction.

From MuRec Require Import sigma relations arith_mini index vec
                          recalg recalg_semantics computable.

Section recalg_coq.

  (* ⟦Sa⟧ : vec nat a → nat → Prop defined in "recalg_semantics.v"
     denotes the (partial) functional relation (graph)
     associated/interpreting the µ-recursive source code of the
     algorithm Sa *)

  (* We show that the graph ⟦Sa⟧ is computable for any Sa : recalg a,
     ie it can be reified into a Coq term

         ∀Va : vec nat a, ex (⟦Sa⟧ Va) → sig (⟦Sa⟧ Va)

     Moreover, the extracted code is the Ocaml interpreter of
     the μ-recursive algorithm that Sa describes
    *)

  (** The fixpoint below compiles the μ-recursive algorithm Sa
      into Coq code that mimics the algorithm Sa. This is an
      interpreter for μ-recursive algorithms.

      It needs a termination certificate in the form
      of a proof that the predicate ⟦Sa⟧ Va is inhabited
      by an output value.

      This gives a VERY short proof of the *totality* of Coq !!!

      By "totality" here, we mean eg that given a binary relation
      R : nat → nat → Prop which is

        a) described by a µ-recursive algorithm
        b) and *provably total* in Coq

      one can compute a Coq term f : nat → nat which
      realises that relation, ie ∀x, R x (f x).
   *)

   (** Beware that Cn_compute, Pr_compute and Mn_compute receive the
       fixpoint ra_compute itself as first argument hence the guard-checker
       will perform an analysis of their code to verify that they
       only call the fixpoint on sub-terms of the argument Sa *)

   (*  We renamed "a" into "k" to avoid name clash on Sa between
       ra_compute and Cn_compute at Extraction, which generates
       a fresh new name like "sa0", not so nice at display *)
  Fixpoint ra_compute k (Sk : recalg k) : ∀Vk : vec nat k, computable (⟦Sk⟧ Vk) :=
    match Sk with
    | ra_zero         => Zr_compute
    | ra_succ         => Sc_compute
    | ra_proj i       => Id_compute i
    | ra_comp Sb Skb  => Cn_compute ra_compute Sb Skb
    | ra_prec Sb Sb'' => Pr_compute ra_compute Sb Sb''
    | ra_umin Sb'     => Mn_compute ra_compute Sb'
    end.

End recalg_coq.

Arguments ra_compute {k} Sk Vk.

(** As a corollary, we get this short proof of the result of ITP 2017

    If Sa : recalg a is an algorithm defining a provably total
    (recursive) functional relation, then there is a Coq term
    f : vec nat a → nat realizing that relation.

    Here we get the result with a much shorter and more direct proof.
    Moreover the extracted term corresponds to the OCaml implementation
    of the algorithm described in Sa. *)

Definition coq_is_total a (Sa : recalg a) : (∀Va, ∃y, ⟦Sa⟧ Va y) → { f | ∀Va, ⟦Sa⟧ Va (f Va) } :=
  λ cSa, reify (λ Va, ra_compute Sa Va (cSa Va)).

Check @ra_compute.
Print Assumptions ra_compute.

Check coq_is_total.
Print Assumptions coq_is_total.

Extraction Inline vec_S_inv.
Extraction Inline sig_monotonic comp reify.
Extraction Inline umin₀_compute.
Extraction Inline Id_compute Zr_compute Sc_compute Pr_compute Mn_compute Cn_compute.

(* indices extracted as (unbounded) nat *)
Extract Inductive idx => "nat" [ "O" "S" ].

(* vectors extracted as Ocaml lists *)
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

Extraction Implicit vec_map_compute [a].
Extraction Implicit Id_compute [a].

Extraction Implicit ra_compute [k].
Extraction Implicit coq_is_total [a].

Recursive Extraction ra_compute.
Extraction "ra.ml" ra_compute coq_is_total.


