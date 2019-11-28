(** Moment: a date and a time. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import ErrorHandlers.All.
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

  (** The moment in the RFC 3339 format, like `2002-10-02T15:00:00Z`. *)
  Definition rfc3339 (moment : t) : LString.t :=
    Date.Print.date (date moment) ++ LString.s "T" ++
    Time.Print.time (time moment) ++ LString.s "Z".
End Print.

(** Parsing. *)
Module Parse.
  (** Parse a moment in RFC 3339 format, like 2002-10-02T15:00:00Z. We ignore
      the optional decimal part of the seconds. *)
  Definition rfc3339 (s : LString.t) : option (t * LString.t) :=
    Option.bind (Date.Parse.date s) (fun date_s =>
    let (date, s) := date_s in
    Option.bind (Util.eat_character "T" s) (fun s =>
    Option.bind (Time.Parse.time s) (fun time_s =>
    let (time, s) := time_s in
    Option.bind (Time.Parse.time_zone_offset s) (fun time_zone_offset_s =>
    let (time_zone_offset, s) := time_zone_offset_s in
    let moment := {| date := date; time := time |} in
    Some (of_epoch (to_epoch moment + Time.to_seconds time_zone_offset), s)
    )))).
End Parse.

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

    Definition test_rfc3339 :
      List.map Print.rfc3339 [
        New (Date.New 1970 1 1) (Time.New 0 0 0);
        New (Date.New 1994 11 6) (Time.New 8 49 37);
        New (Date.New 2014 10 24) (Time.New 15 40 37)] = List.map LString.s [
        "1970-01-01T00:00:00Z";
        "1994-11-06T08:49:37Z";
        "2014-10-24T15:40:37Z"] :=
      eq_refl.
  End Print.

  Module Parse.
    Local Open Scope string.

    Definition test_rfc3339 :
      List.map Parse.rfc3339 (List.map LString.s [
        "2017-02-21T15:09:03Z...";
        "2017-02-21T15:09:03+00:00";
        "2017-02-21T15:09:03-00:00";
        "2017-02-21T15:09:03+01:00";
        "2017-02-21T15:09:03-12:00";
        "2017-02-21T15:09:03-16:00";
        "2017-0221T15:09:03-16:00"
      ]) = [
        Some (New (Date.New 2017 2 21) (Time.New 15 9 3), LString.s "...");
        Some (New (Date.New 2017 2 21) (Time.New 15 9 3), LString.s "");
        Some (New (Date.New 2017 2 21) (Time.New 15 9 3), LString.s "");
        Some (New (Date.New 2017 2 21) (Time.New 16 9 3), LString.s "");
        Some (New (Date.New 2017 2 21) (Time.New 3 9 3), LString.s "");
        Some (New (Date.New 2017 2 20) (Time.New 23 9 3), LString.s "");
        None
      ] :=
      eq_refl.
  End Parse.
End Test.
