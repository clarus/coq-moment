(** Moment: a date and a time. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Date.
Require Time.

Import ListNotations.
Local Open Scope char.
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
Module Print.
  (** The moment in the RFC 1123 format, like `Sun, 06 Nov 1994 08:49:37 GMT`. *)
  Definition rfc1123 (moment : t) : LString.t :=
    Date.Print.short_week_day true (date moment) ++ LString.s ", " ++
    Date.Print.day (Some "0") (date moment) ++ LString.s " " ++
    Date.Print.short_month (date moment) ++ LString.s " " ++
    Date.Print.year 4 (Some "0") (date moment) ++ LString.s " " ++
    Time.Print.time (time moment) ++
    LString.s " GMT".
End Print.

(** Tests for this file. *)
Module Test.
  Definition test_of_epoch :
    List.map of_epoch [0; 1414165237; 1414165239] = [
      New (Date.New 1970 1 1) (Time.New 0 0 0);
      New (Date.New 2014 10 24) (Time.New 15 40 37);
      New (Date.New 2014 10 24) (Time.New 15 40 39)] :=
    eq_refl.

  Definition test_to_epoch :
    List.map to_epoch [
      New (Date.New 1970 1 1) (Time.New 0 0 0);
      New (Date.New 2014 10 24) (Time.New 15 40 37);
      New (Date.New 2014 10 24) (Time.New 15 40 39)] =
      [0; 1414165237; 1414165239] :=
    eq_refl.

  Module Print.
    Require Import Coq.Strings.String.
    Local Open Scope string.

    Definition test_rfc1123 :
      List.map Print.rfc1123 [
        New (Date.New 1970 1 1) (Time.New 0 0 0);
        New (Date.New 1994 11 6) (Time.New 8 49 37);
        New (Date.New 2014 10 24) (Time.New 15 40 37)] = List.map LString.s [
        "Thu, 01 Jan 1970 00:00:00 GMT";
        "Sun, 06 Nov 1994 08:49:37 GMT";
        "Fri, 24 Oct 2014 15:40:37 GMT"] :=
      eq_refl.
  End Print.
End Test.
