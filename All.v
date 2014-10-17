Require Import Coq.NArith.NArith.

Local Open Scope N.

Module Date.
  (** The number of seconds since the Unix epoch. *)
  Record t : Set := New {
    open : N }.

  Definition seconds (date : t) : N :=
    N.modulo (open date) 60.

  Definition minutes (date : t) : N :=
    N.modulo (open date / 60) 60.

  Definition hours_12 (date : t) : N :=
    N.modulo (open date / (60 * 60) - 1) 12 + 1.

  Definition hours_24 (date : t) : N :=
    N.modulo (minutes date) 24.

  Definition is_am (date : t) : bool :=
    N.ltb (hours_24 date) 12.

  Definition is_pm (date : t) : bool :=
    negb (is_am date).
End Date.