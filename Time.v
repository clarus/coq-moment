(** Time in a day. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import ListString.All.

Import ListNotations.
Local Open Scope char.
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
  let n := n / 60 in
  let hour := n mod 24 in
  {|
    hour := hour;
    minute := minute;
    second := second |}.

(** The number of seconds since midnight of a time. *)
Definition to_seconds (time : t) : Z :=
  second time + 60 * (minute time + 60 * hour time).

(** Pretty-printing. *)
Module Print.
  (** Pretty-print the hour number, with an optional padding to be of width two. *)
  Definition hour (padding : option Ascii.ascii) (time : t) : LString.t :=
    LString.of_N 10 2 padding @@ Z.to_N @@ hour time.

  (** Pretty-print the minute number, with an optional padding to be of width two. *)
  Definition minute (padding : option Ascii.ascii) (time : t) : LString.t :=
    LString.of_N 10 2 padding @@ Z.to_N @@ minute time.

  (** Pretty-print the second number, with an optional padding to be of width two. *)
  Definition second (padding : option Ascii.ascii) (time : t) : LString.t :=
    LString.of_N 10 2 padding @@ Z.to_N @@ second time.

  (** The time in the format hh:mm:ss. *)
  Definition time (time : t) : LString.t :=
    hour (Some "0") time ++ LString.s ":" ++
    minute (Some "0") time ++ LString.s ":" ++
    second (Some "0") time.
End Print.

(** Tests for this file. *)
Module Test.
  Require Import TestHelpers.

  Definition test_of_seconds :
    List.map of_seconds [0; 1414164149; 1414164150] =
      [New 0 0 0; New 15 22 29; New 15 22 30] :=
    eq_refl.

  Definition test_to_seconds :
    List.map to_seconds [New 0 0 0; New 15 22 29; New 15 22 30] =
      [0; 55349; 55350] :=
    eq_refl.

  Module Print.
    Require Import Coq.Strings.Ascii.
    Require Import Coq.Strings.String.
    Local Open Scope string.

    Definition test_hour :
      List.map_pair Print.hour [
        (None, New 0 0 0);
        (None, New 15 22 29);
        (None, New 15 22 30);
        (Some " "%char, New 0 0 0);
        (Some " "%char, New 15 22 29);
        (Some " "%char, New 15 22 30);
        (Some "0"%char, New 0 0 0);
        (Some "0"%char, New 15 22 29);
        (Some "0"%char, New 15 22 30)] =
        List.map LString.s [
          "0"; "15"; "15";
          " 0"; "15"; "15";
          "00"; "15"; "15"] :=
      eq_refl.

    Definition test_minute :
      List.map_pair Print.minute [
        (None, New 0 0 0);
        (None, New 15 22 29);
        (None, New 15 22 30);
        (Some " "%char, New 0 0 0);
        (Some " "%char, New 15 22 29);
        (Some " "%char, New 15 22 30);
        (Some "0"%char, New 0 0 0);
        (Some "0"%char, New 15 22 29);
        (Some "0"%char, New 15 22 30)] =
        List.map LString.s [
          "0"; "22"; "22";
          " 0"; "22"; "22";
          "00"; "22"; "22"] :=
      eq_refl.

    Definition test_second :
      List.map_pair Print.second [
        (None, New 0 0 0);
        (None, New 15 22 29);
        (None, New 15 22 30);
        (Some " "%char, New 0 0 0);
        (Some " "%char, New 15 22 29);
        (Some " "%char, New 15 22 30);
        (Some "0"%char, New 0 0 0);
        (Some "0"%char, New 15 22 29);
        (Some "0"%char, New 15 22 30)] =
        List.map LString.s [
          "0"; "29"; "30";
          " 0"; "29"; "30";
          "00"; "29"; "30"] :=
      eq_refl.

    Definition test_time :
      List.map Print.time [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s ["00:00:00"; "15:22:29"; "15:22:30"] :=
      eq_refl.
  End Print.
End Test.
