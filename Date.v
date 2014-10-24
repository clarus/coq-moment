(** Date: day in a calendar. *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import LString.All.

Import ListNotations.
Local Open Scope Z.

(** A date is a year, a month and a day. There is no enforced bound by the type
    system for the month and the day number, but values are expected to be in
    the standard range. The month and day number start at one. A date can be of
    Julian or Gregorian calendar, depending on the context. *)
Record t : Set := New {
  year : Z;
  month : Z;
  day : Z }.

(** Compare two dates. *)
Definition compare (date1 date2 : t) : comparison :=
  match Z.compare (year date1) (year date2) with
  | Eq =>
    match Z.compare (month date1) (month date2) with
    | Eq => Z.compare (day date1) (day date2)
    | c => c
    end
  | c => c
  end.

(** The date of a Julian day, in a Julian or Gregorian calendar. *)
Definition of_Julian_day (is_Gregorian : bool) (n : Z) : t :=
  let a := n + 32044 in
  let b :=
    if is_Gregorian then
      (4 * a + 3) / 146097
    else
      0 in
  let c :=
    if is_Gregorian then
      a - (b * 146097) / 4
    else
      n + 32082 in
  let d := (4 * c + 3) / 1461 in
  let e := c - (1461 * d) / 4 in
  let m := (5 * e + 2) / 153 in
  {|
    day := e - (153 * m + 2) / 5 + 1;
    month := m + 3 - 12 * (m / 10);
    year := b * 100 + d - 4800 + m / 10 |}.

(** The Julian day of a date, considering the date as Julian or Gregorian. *)
Definition to_Julian_day (is_Gregorian : bool) (date : t) : Z :=
  let a := (14 - month date) / 12 in
  let y := year date + 4800 - a in
  let m := month date + 12 * a - 3 in
  if is_Gregorian then
    day date + (153 * m + 2) / 5 + y * 365 + y / 4 - y / 100 + y / 400 - 32045
  else
    day date + (153 * m + 2) / 5 + y * 365 + y / 4 - 32083.

(** The Unix epoch (in the Gregorian calendar). *)
Definition epoch : t := {|
  year := 1970;
  month := 1;
  day := 1 |}.

(** The Gregorian date of a Unix day. *)
Definition of_epoch (n : Z) : t :=
  of_Julian_day true (n + to_Julian_day true epoch).

(** The Unix day of a Gregorian date. *)
Definition to_epoch (date : t) : Z :=
  to_Julian_day true date - to_Julian_day true epoch.


(** Days of the week. *)
Module WeekDay.
  (** The finite set of days of the week. *)
  Inductive t : Set :=
  | Sunday | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday.

  (** 0 for Sunday, 1 for Monday, ... *)
  Definition of_Z (n : Z) : t :=
    match n mod 7 with
    | 0 => Sunday
    | 1 => Monday
    | 2 => Tuesday
    | 3 => Wednesday
    | 4 => Thursday
    | 5 => Friday
    | 6 => Saturday
    | _ => Sunday (* This case should not happen. *)
    end.

  (** The day of the week of a date. *)
  Definition of_date (is_Gregorian : bool) (date : Date.t) : t :=
    let a := (14 - month date) / 12 in
    let y := year date - a in
    let m := month date + 12 * a - 2 in
    if is_Gregorian then
      of_Z ((day date + y + y / 4 - y / 100 + y / 400 + (31 * m) / 12) mod 7)
    else
      of_Z ((5 + day date + y + y / 4 + (31 * m) / 12) mod 7).

  (** Pretty-printing. *)
  Module PrettyPrint.
    (** The full name of a day of the week (Monday, Tuesday, ...). *)
    Definition full (day : t) : LString.t :=
      LString.s match day with
      | Sunday => "Sunday"
      | Monday => "Monday"
      | Tuesday => "Tuesday"
      | Wednesday => "Wednesday"
      | Thursday => "Thursday"
      | Friday => "Friday"
      | Saturday => "Saturday"
      end.

    (** The short name of a day of the week (Mon, Tue, ...). *)
    Definition short (day : t) : LString.t :=
      LString.s match day with
      | Sunday => "Sun"
      | Monday => "Mon"
      | Tuesday => "Tue"
      | Wednesday => "Wed"
      | Thursday => "Thu"
      | Friday => "Fri"
      | Saturday => "Sat"
      end.
  End PrettyPrint.
End WeekDay.

(** The month. *)
Module Month.
  (** The finite set of months. *)
  Inductive t : Set :=
  | January | February | March | April | May | June | July
  | August | September | October | November | December.

  (** 1 for January, 2 for February, ... *)
  Definition of_Z (n : Z) : t :=
    match (n - 1) mod 12 + 1 with
    | 1 => January
    | 2 => February
    | 3 => March
    | 4 => April
    | 5 => May
    | 6 => June
    | 7 => July
    | 8 => August
    | 9 => September
    | 10 => October
    | 11 => November
    | 12 => December
    | _ => January (* This case should not happen. *)
    end.

  (** The month of a date. *)
  Definition of_date (date : Date.t) : t :=
    of_Z @@ month date.

  (** Pretty-printing. *)
  Module PrettyPrint.
    (** The full name of a month (January, February, ...). *)
    Definition full (month : t) : LString.t :=
      LString.s match month with
      | January => "January"
      | February => "February"
      | March => "March"
      | April => "April"
      | May => "May"
      | June => "June"
      | July => "July"
      | August => "August"
      | September => "September"
      | October => "October"
      | November => "November"
      | December => "December"
      end.

    (** The short name of a month (Jan, Feb, ...). *)
    Definition short (month : t) : LString.t :=
      LString.s match month with
      | January => "Jan"
      | February => "Feb"
      | March => "Mar"
      | April => "Apr"
      | May => "May"
      | June => "Jun"
      | July => "Jul"
      | August => "Aug"
      | September => "Sep"
      | October => "Oct"
      | November => "Nov"
      | December => "Dec"
      end.
  End PrettyPrint.
End Month.

(** Pretty-printing. *)
Module PrettyPrint.
  (** The year. *)
  Definition year (date : t) : LString.t :=
    LString.of_Z 10 10 @@ year date.

  (** The month number. *)
  Definition month (date : t) : LString.t :=
    LString.of_Z 10 2 @@ month date.

  (** The month number with space padding. *)
  Definition space_padded_month (date : t) : LString.t :=
    (if Z.leb 10 (Date.month date) then LString.s "" else LString.s " ") ++
    LString.of_Z 10 2 @@ Date.month date.

  (** The month number with zero padding. *)
  Definition zero_padded_month (date : t) : LString.t :=
    (if Z.leb 10 (Date.month date) then LString.s "" else LString.s "0") ++
    LString.of_Z 10 2 @@ Date.month date.

  (** The day number. *)
  Definition day (date : t) : LString.t :=
    LString.of_Z 10 2 @@ day date.

  (** The day number with space padding. *)
  Definition space_padded_day (date : t) : LString.t :=
    (if Z.leb 10 (Date.day date) then LString.s "" else LString.s " ") ++
    LString.of_Z 10 2 @@ Date.day date.

  (** The day number with zero padding. *)
  Definition zero_padded_day (date : t) : LString.t :=
    (if Z.leb 10 (Date.day date) then LString.s "" else LString.s "0") ++
    LString.of_Z 10 2 @@ Date.day date.

  (** The full name of a day of the week (Monday, Tuesday, ...). *)
  Definition full_week_day (is_Gregorian : bool) (date : t) : LString.t :=
    WeekDay.PrettyPrint.full @@ WeekDay.of_date is_Gregorian date.

  (** The short name of a day of the week (Mon, Tue, ...). *)
  Definition short_week_day (is_Gregorian : bool) (date : t) : LString.t :=
    WeekDay.PrettyPrint.short @@ WeekDay.of_date is_Gregorian date.

  (** The full name of a month (January, February, ...). *)
  Definition full_month (date : t) : LString.t :=
    Month.PrettyPrint.full @@ Month.of_date date.

  (** The short name of a month (Jan, Feb, ...). *)
  Definition short_month (date : t) : LString.t :=
    Month.PrettyPrint.short @@ Month.of_date date.
End PrettyPrint.

(** Tests for this file. *)
Module Test.
  Require Import "TestHelpers".

  Definition test_compare :
    List.map_pair compare [
      (New 2014 10 10, New 2014 10 10);
      (New 2014 10 10, New 2012 10 30);
      (New 2014 10 10, New 2014 10 11)] =
      [Eq; Gt; Lt] :=
    eq_refl.

  Definition test_of_Julian_day :
    List.map_pair of_Julian_day [
      (true, 2456952);
      (true, to_Julian_day true @@ New 2003 02 02);
      (false, to_Julian_day false @@ New 2003 02 02)] = [
      New 2014 10 21;
      New 2003 02 02;
      New 2003 02 02] :=
    eq_refl.

  Definition test_to_Julian_day :
    List.map_pair to_Julian_day [
      (true, New 2014 10 21);
      (true, of_Julian_day true (-1));
      (false, of_Julian_day false (-1))] = [
      2456952;
      -1;
      -1] :=
    eq_refl.

  Definition test_of_epoch :
    List.map of_epoch [0; 16365] = [New 1970 1 1; New 2014 10 22] := eq_refl.

  Definition test_to_epoch :
    List.map to_epoch [New 1970 1 1; New 2014 10 22] = [0; 16365] := eq_refl.

  Module WeekDay.
    Definition test_of_Z :
      List.map WeekDay.of_Z [0; 7; 3] =
        [WeekDay.Sunday; WeekDay.Sunday; WeekDay.Wednesday] :=
      eq_refl.

    Definition test_of_date :
      List.map_pair WeekDay.of_date [
        (true, New 2014 10 24);
        (true, New 2014 10 25);
        (false, New 0 1 1)] = [
        WeekDay.Friday;
        WeekDay.Saturday;
        WeekDay.Thursday] :=
      eq_refl.

    Module PrettyPrint.
      Require Import Coq.Strings.String.
      Local Open Scope string.

      Definition test_full :
        List.map WeekDay.PrettyPrint.full
          [WeekDay.Sunday; WeekDay.Monday; WeekDay.Wednesday] =
          List.map LString.s ["Sunday"; "Monday"; "Wednesday"] :=
        eq_refl.

      Definition test_short :
        List.map WeekDay.PrettyPrint.short
          [WeekDay.Sunday; WeekDay.Monday; WeekDay.Wednesday] =
          List.map LString.s ["Sun"; "Mon"; "Wed"] :=
        eq_refl.
    End PrettyPrint.
  End WeekDay.

  Module Month.
    Definition test_of_Z :
      List.map Month.of_Z [1; 7; 3] =
        [Month.January; Month.July; Month.March] :=
      eq_refl.

    Definition test_of_date :
      List.map Month.of_date [
        New 2014 10 24;
        New 2014 10 25;
        New 0 1 1] = [
        Month.October;
        Month.October;
        Month.January] :=
      eq_refl.

    Module PrettyPrint.
      Require Import Coq.Strings.String.
      Local Open Scope string.

      Definition test_full :
        List.map Month.PrettyPrint.full
          [Month.October; Month.December; Month.March] =
          List.map LString.s ["October"; "December"; "March"] :=
        eq_refl.

      Definition test_short :
        List.map Month.PrettyPrint.short
          [Month.October; Month.December; Month.March] =
          List.map LString.s ["Oct"; "Dec"; "Mar"] :=
        eq_refl.
    End PrettyPrint.
  End Month.

  Module PrettyPrint.
    Require Import Coq.Strings.String.
    Local Open Scope string.

    Definition test_year :
      List.map PrettyPrint.year
        [New 2014 5 5 ; New 1 2 3; New (-0) 1 15; New (-1) 12 4] =
        List.map LString.s ["2014"; "1"; "0"; "-1"] :=
      eq_refl.

    Definition test_month :
      List.map PrettyPrint.month
        [New 2014 5 5 ; New 1 2 3; New (-0) 1 15; New (-1) 12 4] =
        List.map LString.s ["5"; "2"; "1"; "12"] :=
      eq_refl.

    Definition test_space_padded_month :
      List.map PrettyPrint.space_padded_month
        [New 2014 5 5 ; New 1 2 3; New (-0) 1 15; New (-1) 12 4] =
        List.map LString.s [" 5"; " 2"; " 1"; "12"] :=
      eq_refl.

    Definition test_zero_padded_month :
      List.map PrettyPrint.zero_padded_month
        [New 2014 5 5 ; New 1 2 3; New (-0) 1 15; New (-1) 12 4] =
        List.map LString.s ["05"; "02"; "01"; "12"] :=
      eq_refl.

    Definition test_day :
      List.map PrettyPrint.day
        [New 2014 5 5 ; New 1 2 3; New (-0) 1 15; New (-1) 12 4] =
        List.map LString.s ["5"; "3"; "15"; "4"] :=
      eq_refl.

    Definition test_space_padded_day :
      List.map PrettyPrint.space_padded_day
        [New 2014 5 5 ; New 1 2 3; New (-0) 1 15; New (-1) 12 4] =
        List.map LString.s [" 5"; " 3"; "15"; " 4"] :=
      eq_refl.

    Definition test_zero_padded_day :
      List.map PrettyPrint.zero_padded_day
        [New 2014 5 5 ; New 1 2 3; New (-0) 1 15; New (-1) 12 4] =
        List.map LString.s ["05"; "03"; "15"; "04"] :=
      eq_refl.

    Definition test_full_week_day :
      List.map_pair PrettyPrint.full_week_day [
        (true, New 2014 10 24);
        (true, New 2014 10 25);
        (false, New 0 1 1)] = List.map LString.s [
        "Friday";
        "Saturday";
        "Thursday"] :=
      eq_refl.

    Definition test_short_week_day :
      List.map_pair PrettyPrint.short_week_day [
        (true, New 2014 10 24);
        (true, New 2014 10 25);
        (false, New 0 1 1)] = List.map LString.s [
        "Fri";
        "Sat";
        "Thu"] :=
      eq_refl.

    Definition test_full_month :
      List.map PrettyPrint.full_month
        [New 2014 10 24; New 2014 10 25; New 0 1 1] =
        List.map LString.s ["October"; "October"; "January"] :=
      eq_refl.

    Definition test_short_month :
      List.map PrettyPrint.short_month
        [New 2014 10 24; New 2014 10 25; New 0 1 1] =
        List.map LString.s ["Oct"; "Oct"; "Jan"] :=
      eq_refl.
  End PrettyPrint.
End Test.