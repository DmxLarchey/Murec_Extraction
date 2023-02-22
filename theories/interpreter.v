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

From MuRec Require Import sigma relations arith_mini index vec
                          recalg recalg_semantics computable.

Reserved Notation " '⟦' f '⟧ₒ' " (at level 1, format "⟦ f ⟧ₒ").

Section recalg_coq.

  (* ra_sem Sa = ⟦Sa⟧ : vec nat a → nat → Prop is defined
     as a structural Fixpoint on Sa in "recalg_semantics.v"
     and denotes the (partial) functional relation (graph)
     associated/interpreting the µ-recursive source code
     of the algorithm Sa as a combination of µ-recursive
     schemes *)

  (* We show that the graph ⟦Sa⟧ is computable for any
     Sa : recalg a, ie it can be reified into a Coq term

         ∀Va : vec nat a, ex (⟦Sa⟧ Va) → sig (⟦Sa⟧ Va)

     Moreover, the extracted code is the Ocaml interpreter of
     the μ-recursive algorithm that Sa describes *)

  (** Beware that Cn_compute, Pr_compute and Mn_compute receive the
      fixpoint ra_compute itself as first argument hence the guard-checker
      will perform an analysis of their code to verify that they
      only call the fixpoint on sub-terms of the argument Sa.

      Notice that this nesting *already exists* in the Fixpoint
      definition of ra_sem Sa = ⟦Sa⟧ in the call, that is
      vec_map (λ f, ⟦f⟧) Sab which is identical
      to vec_map ra_sem Sab.

      Notice that the branch "murec_artifact_hvec" shows that
      it is possible to write ra_compute much like ra_sem,
      except that vec_map needs to be upgraded to vec_hmap
      outputting an heterogeneous vector instead of a vector. *)

  (*  We renamed "a" into "k" to avoid name clash on Sa between
      ra_compute and Cn_compute at Extraction, which generates
      a fresh new name like "sa0", not so nice at display *)

   (** Beware that only vec_map_compute receives the
       fixpoint ra_compute itself as first argument hence
       the guard-checker will perform an analysis of its code
       to verify that it calls the fixpoint on sub-terms
       of the argument Skb *)

   (*  We renamed "a" into "k" to avoid name clash on Sa between
       ra_compute and Cn_compute at Extraction, which generates
       a fresh new name like "sa0", not so nice at display *)

  Fixpoint ra_compute {k} (Sk : recalg k) { struct Sk } : ∀Vk : vec nat k, computable (⟦Sk⟧ Vk) :=
    match Sk with
    | ra_zero         => Zr_compute
    | ra_succ         => Sc_compute
    | ra_proj i       => Id_compute i
    | ra_comp Sb Sab  => Cn_compute ⟦Sb⟧ₒ (λ Va cVa, vec_map_compute (λ Sa cSa, ⟦Sa⟧ₒ Va (πᵤ cSa)) Sab cVa)
    | ra_prec Sb Sb'' => Pr_compute ⟦Sb⟧ₒ ⟦Sb''⟧ₒ
    | ra_umin Sb'     => Mn_compute ⟦Sb'⟧ₒ
    end
  where "⟦ f ⟧ₒ" := (ra_compute f).

End recalg_coq.

Arguments ra_compute {k} Sk Vk.

Check @ra_compute.
Print Assumptions ra_compute.

(** As a corollary, we get this alternate proof of the result of ITP 2017

    If Sa : recalg a is an algorithm defining a provably total
    (recursive) functional relation, then there is a Coq term
    f : vec nat a → nat realizing that relation.

    Here we get the result with a much shorter and more direct proof.
    Moreover the extracted term corresponds to the OCaml implementation
    of the algorithm described in Sa.

    In the ITP 17 paper, that result is obtained using a variant of
    Kleene's normal form theorem, approximating µ-recursive functions
    by bounding their computation with an extra "fuel" argument, making
    them primitive recursive thus terminating. Then Constructive Epsilon
    is applied to compute the necessary fuel simultaneously with the
    output value, by a (dumb) exhaustive trial/error loop. *)

Definition coq_is_total a (Sa : recalg a) : (∀Va, ∃y, ⟦Sa⟧ Va y) → { f | ∀Va, ⟦Sa⟧ Va (f Va) } :=
  λ cSa, reify (λ Va, ra_compute Sa Va (cSa Va)).

Check coq_is_total.
Print Assumptions coq_is_total.

(** Now we configure Extraction for exclude arguments that do not
    participate in the computation and hence, enhance readabitity.
    We inline some auxiliary functions and we extract idx to nat
    and vectors to lists. *)

Extraction Inline vec_S_inv.
Extraction Inline sig_monotonic comp reify.
Extraction Inline umin₀_compute.
Extraction Inline Id_compute Zr_compute Sc_compute Pr_compute Mn_compute Cn_compute.

(* unit is extracted as unit () *)
Extract Inductive unit => "unit" [ "()" ].

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

Extraction Implicit vec_map_compute [n].
Extraction Implicit Id_compute [a].

Extraction Implicit ra_compute [k].
Extraction Implicit coq_is_total [a].

Recursive Extraction ra_compute.
Extraction "ra.ml" ra_compute.

Extraction Language Haskell.
Extraction "ra.hs" ra_compute.


