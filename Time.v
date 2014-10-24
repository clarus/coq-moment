(** Time in a day. *)
Require Import Coq.Lists.List.
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

(** Pretty-printing. *)
Module PrettyPrint.
  (** Pretty-print the hour number. *)
  Definition hour (time : t) : LString.t :=
    LString.of_Z 10 2 @@ hour time.

  (** Pretty-print the hour number with space padding. *)
  Definition space_padded_hour (time : t) : LString.t :=
    (if Z.leb 10 (Time.hour time) then LString.s "" else LString.s " ") ++
    LString.of_Z 10 2 @@ Time.hour time.

  (** Pretty-print the hour number with zero padding. *)
  Definition zero_padded_hour (time : t) : LString.t :=
    (if Z.leb 10 (Time.hour time) then LString.s "" else LString.s "0") ++
    LString.of_Z 10 2 @@ Time.hour time.

  (** Pretty-print the minute number. *)
  Definition minute (time : t) : LString.t :=
    LString.of_Z 10 2 @@ minute time.

  (** Pretty-print the minute number with space padding. *)
  Definition space_padded_minute (time : t) : LString.t :=
    (if Z.leb 10 (Time.minute time) then LString.s "" else LString.s " ") ++
    LString.of_Z 10 2 @@ Time.minute time.

  (** Pretty-print the minute number with zero padding. *)
  Definition zero_padded_minute (time : t) : LString.t :=
    (if Z.leb 10 (Time.minute time) then LString.s "" else LString.s "0") ++
    LString.of_Z 10 2 @@ Time.minute time.

  (** Pretty-print the second number. *)
  Definition second (time : t) : LString.t :=
    LString.of_Z 10 2 @@ second time.

  (** Pretty-print the second number with space padding. *)
  Definition space_padded_second (time : t) : LString.t :=
    (if Z.leb 10 (Time.second time) then LString.s "" else LString.s " ") ++
    LString.of_Z 10 2 @@ Time.second time.

  (** Pretty-print the second number with zero padding. *)
  Definition zero_padded_second (time : t) : LString.t :=
    (if Z.leb 10 (Time.second time) then LString.s "" else LString.s "0") ++
    LString.of_Z 10 2 @@ Time.second time.
End PrettyPrint.
