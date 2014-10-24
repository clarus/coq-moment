(** Moment: a date and a time. *)
Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import LString.All.
Require "Date".
Require "Time".

Local Open Scope Z.

(** A moment is a date and a time. *)
Record t : Set := New {
  date : Date.t;
  time : Time.t }.

Definition seconds_per_day := 60 * 60 * 24.

(** The moment given by a number of seconds since the Unix epoch. *)
Definition of_epoch (n : Z) : t := {|
  date := Date.of_epoch (n / seconds_per_day);
  time := Time.of_seconds (n mod seconds_per_day) |}.

(** The number of seconds since the Unix epoch. *)
Definition to_epoch (moment : t) : Z :=
  seconds_per_day * Date.to_epoch (date moment) + Time.to_seconds (time moment).

(* Fri, 31 Dec 1999 23:59:59 GMT *)

Module Test.
  Definition now : t := {|
    date := {| Date.year := 2014; Date.month := 10; Date.day := 22 |};
    time := {| Time.hour := 10; Time.minute := 26; Time.second := 22 |} |}.

  Compute of_epoch @@ to_epoch now.
End Test.
