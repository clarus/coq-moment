(** Time in a day. *)
Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import LString.All.

Local Open Scope Z.

(** A time is an hour, a minute and a second. There is no enforced bound by the
    type system, but values are expected to be in the standard range. *)
Record t : Set := New {
  hour : Z;
  minute : Z;
  second : Z }.

(** The time of a second number (the number of seconds since midnight). *)
Definition of_seconds (n : Z) : t :=
  let second := n mod 60 in
  let n := n / 60 in
  let minute := n mod 60 in
  let hour := n / 60 in
  {|
    hour := hour;
    minute := minute;
    second := second |}.

(** The number of seconds since midnight of a time. *)
Definition to_seconds (time : t) : Z :=
  second time + 60 * (minute time + 60 * hour time).

Compute of_seconds @@ to_seconds @@ New 12 0 0.
