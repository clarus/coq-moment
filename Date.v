Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import LString.All.

Local Open Scope Z.

Record t : Set := New {
  year : Z;
  month : Z;
  day : Z }.

Definition compare (date1 date2 : t) : comparison :=
  match Z.compare (year date1) (year date2) with
  | Eq =>
    match Z.compare (month date1) (month date2) with
    | Eq => Z.compare (day date1) (day date2)
    | c => c
    end
  | c => c
  end.

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

Definition to_Julian_day (is_Gregorian : bool) (date : t) : Z :=
  let a := (14 - month date) / 12 in
  let y := year date + 4800 - a in
  let m := month date + 12 * a - 3 in
  if is_Gregorian then
    day date + (153 * m + 2) / 5 + y * 365 + y / 4 - y / 100 + y / 400 - 32045
  else
    day date + (153 * m + 2) / 5 + y * 365 + y / 4 - 32083.

Compute of_Julian_day true (to_Julian_day true (New 2014 10 22)).
Compute to_Julian_day false (New (-4712) 1 1).
Compute of_Julian_day true 2456952.

Definition epoch : t := {|
  year := 1970;
  month := 1;
  day := 1 |}.

Definition of_epoch (n : Z) : t :=
  of_Julian_day true (n + to_Julian_day true epoch).

Definition to_epoch (date : t) : Z :=
  to_Julian_day true date - to_Julian_day true epoch.

Compute of_epoch 16365.

Module WeekDay.
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

  Definition of_date (is_Gregorian : bool) (date : Date.t) : t :=
    let a := (14 - month date) / 12 in
    let y := year date - a in
    let m := month date + 12 * a - 2 in
    if is_Gregorian then
      of_Z ((day date + y + y / 4 - y / 100 + y / 400 + (31 * m) / 12) mod 7)
    else
      of_Z ((5 + day date + y + y / 4 + (31 * m) / 12) mod 7).

  Compute of_date true @@ Date.New 2014 10 22.

  Module PrettyPrint.
    Definition long (day : t) : LString.t :=
      LString.s match day with
      | Sunday => "Sunday"
      | Monday => "Monday"
      | Tuesday => "Tuesday"
      | Wednesday => "Wednesday"
      | Thursday => "Thursday"
      | Friday => "Friday"
      | Saturday => "Saturday"
      end.

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

Module Month.
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

  Definition of_date (date : Date.t) : t :=
    of_Z @@ month date.
End Month.

Module Test.
  (* TODO *)
End Test.