(** Time in a day. *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import ListString.All.

Import ListNotations.
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
End Print.

(** Tests for this file. *)
Module Test.
  Definition test_of_seconds :
    List.map of_seconds [0; 1414164149; 1414164150] =
      [New 0 0 0; New 15 22 29; New 15 22 30] :=
    eq_refl.

  Definition test_to_seconds :
    List.map to_seconds [New 0 0 0; New 15 22 29; New 15 22 30] =
      [0; 55349; 55350] :=
    eq_refl.

  Module Print.
    Require Import Coq.Strings.String.
    Local Open Scope string.

    Definition test_hour :
      List.map Print.hour
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s ["0"; "15"; "15"] :=
      eq_refl.

    Definition test_space_padded_hour :
      List.map Print.space_padded_hour
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s [" 0"; "15"; "15"] :=
      eq_refl.

    Definition test_zero_padded_hour :
      List.map Print.zero_padded_hour
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s ["00"; "15"; "15"] :=
      eq_refl.

    Definition test_minute :
      List.map Print.minute
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s ["0"; "22"; "22"] :=
      eq_refl.

    Definition test_space_padded_minute :
      List.map Print.space_padded_minute
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s [" 0"; "22"; "22"] :=
      eq_refl.

    Definition test_zero_padded_minute :
      List.map Print.zero_padded_minute
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s ["00"; "22"; "22"] :=
      eq_refl.

    Definition test_second :
      List.map Print.second
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s ["0"; "29"; "30"] :=
      eq_refl.

    Definition test_space_padded_second :
      List.map Print.space_padded_second
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s [" 0"; "29"; "30"] :=
      eq_refl.

    Definition test_zero_padded_second :
      List.map Print.zero_padded_second
        [New 0 0 0; New 15 22 29; New 15 22 30] =
        List.map LString.s ["00"; "29"; "30"] :=
      eq_refl.
  End Print.
End Test.
