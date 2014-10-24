(** Moment: a date and a time. *)
Require Import Coq.Lists.List.
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

(** Pretty-printing. *)
Module PrettyPrint.
  (** The moment in the RFC 1123 format. *)
  Definition rfc1123 (moment : t) : LString.t :=
    Date.PrettyPrint.short_week_day true (date moment) ++ LString.s ", " ++
    Date.PrettyPrint.zero_padded_day (date moment) ++ LString.s " " ++
    Date.PrettyPrint.short_month (date moment) ++ LString.s " " ++
    Date.PrettyPrint.year (date moment) ++ LString.s " " ++
    Time.PrettyPrint.zero_padded_hour (time moment) ++ LString.s ":" ++
    Time.PrettyPrint.zero_padded_minute (time moment) ++ LString.s ":" ++
    Time.PrettyPrint.zero_padded_second (time moment) ++ LString.s " " ++
    LString.s "GMT".

Require Import Coq.Strings.String.
Local Open Scope string.
Compute LString.to_string @@ rfc1123 {|
  date := Date.New 1994 11 6;
  time := Time.New 8 49 37 |}.
End PrettyPrint.

Module Test.
  Definition now : t := {|
    date := {| Date.year := 2014; Date.month := 10; Date.day := 22 |};
    time := {| Time.hour := 10; Time.minute := 26; Time.second := 22 |} |}.

  Compute of_epoch @@ to_epoch now.
End Test.
