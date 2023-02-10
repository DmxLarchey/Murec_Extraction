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

(** Textbook reference:
    [BBJ2002]: Computability and Logic
               Boolos, G.S. and Burgess, J.P. and Jeffrey, R.C.
               4th Edition, Cambridge University Press, 2002.
*)

From Coq Require Import Utf8.

From MuRec Require Import relations schemes
                          index vec
                          recalg.

Reserved Notation " '⟦' f '⟧' " (at level 1, format "⟦ f ⟧").

Section relational_semantics.

  (* The relational semantics as graphs of µ-recursive algorithms.
     These definitions follow [BBJ2002]. See schemes.v for more details
      on prim_rec and u_min
   *)

  (* We denote "IO a" for the type of Input/Output relations representing
     the graphs of µ-recursive algorithms of arity a.
     Their inhabitants are denoted by φa and b-vectors of such inhabitants
     are denoted by ψab. *)
  Notation IO a := (vec nat a → nat → Prop).

  (* In [BBJ2002] pp 64:
       - Zr is denoted "z" (the constant zero function, arity 0)
       - Sc is denoted "s" (the successor function, arity 1)
       - Id a i is denoted "id_i^a" (the ith identity or projection at arity a)
   *)

  Definition Zr       : IO 0 := λ _ y, y = 0.
  Definition Sc       : IO 1 := λ V1 y, y = 1 + vec_head V1.
  Definition Id {a} i : IO a := λ Va y, y = Va.[i].

  (* Composition, denoted Cn in [BBJ2002]. *)
  (* Quoting [BBJ2002] pp 64:
     h(x₁,..., xₙ) = f(g₁(x₁,..., xₙ), ...gₘ(x₁,..., xₙ))    (Cn)
     In our conventions, the arities n and m of [BBJ2002] are respectively
     represented by a and b. *)
  Definition Cn {a b} (φb : IO b) (ψab : vec (IO a) b) : IO a :=
    λ Va y, ∃Vb, φb Vb y ∧ ∀ i, ψab.[i] Va Vb.[i].

  (* Think of vec_S_inv (λ x v, ...) w as a way to write
         match w with
           x ∷ v => ...
         end
     but on a w of type vec _ (S _) *)

  (* Definition of Primitive recursion. But see also schemes.v for the definition of prim_rec *)

  Definition Pr {a} (φa : IO a) (ψa'' : IO (2+a)) : IO (1+a) :=
    vec_S_inv (λ n Va, prim_rec φa (λ Wa m y, ψa'' (m ∷ y ∷ Wa)) Va n).

  (* We check the consistency with the reference definition pp 67 of [BBJ2002] also denoted
     Pr there.  *)

  Goal ∀ a φa ψa'' Va y, @Pr a φa ψa'' (0 ∷ Va) y = φa Va y.
  Proof. reflexivity. Qed.

  Goal ∀ a φa ψa'' n Va y, @Pr a φa ψa'' (S n ∷ Va) y = ∃o, Pr φa ψa'' (n ∷ Va) o ∧ ψa'' (n ∷ o ∷ Va) y.
  Proof. reflexivity. Qed.

  (* pp 70 of [BBJ2002] denoted Mn there. But see also schemes.v for the definition of u_minₐ *)
  Definition Mn {a} (φa' : IO (1+a)) : IO a :=
    λ Va, umin₀ (λ y, φa' (y ∷ Va)).

  Goal ∀ a φa' Va y, @Mn a φa' Va y = (φa' (y ∷ Va) 0 ∧ ∀n, n < y → ∃k, φa' (n ∷ Va) (1+k)).
  Proof. reflexivity. Qed.

  (** we define the semantics of a recursive algorithm of arity k
      which is a relation vec nat k → nat → Prop, obviously functional (see below)
      We interpret the constants ra_* with the corresponding s_* operator on relations
   **)

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

  (* We show that the interpretation ⟦Sa⟧ is a functional graph.
     We proceed compositionally so we first show that very scheme
     preserves functionality *)

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

  (** The implementation of vec_prj {n} v p denoted v.[p] below
      must be chosen carefully here so that Coq's guard-checker
      accepts this fixpoint *)

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
