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

From MuRec Require Import index vec.

(* The syntax of µ-recursive algorithms *)

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

Section recalg_rect.

  (** This gives a general recursor for recalg but it is not used in this code,
      because we inline the below fixpoint systematically *)

  Variables (P : ∀{a}, recalg a → Type)
            (P_zero : P ra_zero)
            (P_succ : P ra_succ)
            (P_proj : ∀ {a} i, P (@ra_proj a i))
            (P_comp : ∀ {a b Sb}, P Sb → ∀ {Sab}, (∀ i, P Sab.[i]) → P (@ra_comp a b Sb Sab))
            (P_prec : ∀ {a Sa}, P Sa → ∀ {Sa''}, P Sa'' → P (@ra_prec a Sa Sa''))
            (P_umin : ∀ {a Sa'}, P Sa' → P (@ra_umin a Sa')).

  Local Fixpoint recalg_rect {a} (Sa : recalg a) : P Sa :=
    match Sa with
    | ra_zero         => P_zero
    | ra_succ         => P_succ
    | ra_proj i       => P_proj i
    | ra_comp Sb Sab  => P_comp (recalg_rect Sb) (λ i, recalg_rect Sab.[i])
    | ra_prec Sb Sb'' => P_prec (recalg_rect Sb) (recalg_rect Sb'')
    | ra_umin Sb'     => P_umin (recalg_rect Sb')
    end.

End recalg_rect.
