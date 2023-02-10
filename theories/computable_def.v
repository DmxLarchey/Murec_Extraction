Require Import Utf8.

(** A predicate is computable if a value
    can be computed out of a proof of inhabitation *)

Definition computable {X} (P : X → Prop) := ex P → sig P.
