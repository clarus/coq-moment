Require Import Coq.ZArith.ZArith.

Local Open Scope Z.

Module Date.

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
    let b := if is_Gregorian then (4 * a + 3) / 146097 else 0 in
    let c := if is_Gregorian then a - (b * 146097) / 4 else n + 32082 in
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

  Definition epoch : t := {|
    year := 1970;
    month := 1;
    day := 1 |}.

  Definition of_epoch (n : Z) : t :=
    of_Julian_day true (n + to_Julian_day true epoch).

  Definition to_epoch (date : t) : Z :=
    to_Julian_day true date - to_Julian_day true epoch.

  Compute of_epoch 16365.
End Date.

Module Time.
  Record t : Set := New {
    hour : Z;
    minute : Z;
    second : Z }.

  Definition of_seconds (n : Z) : t :=
    let second := Z.modulo n 60 in
    let n := n / 60 in
    let minute := Z.modulo n 60 in
    let hour := n / 60 in
    {|
      hour := hour;
      minute := minute;
      second := second |}.

  Definition to_seconds (time : t) : Z :=
    second time + 60 * (minute time + 60 * hour time).

  Compute of_seconds (to_seconds (New 12 0 0)).
End Time.

Module Moment.
  Record t : Set := New {
    date : Date.t;
    time : Time.t }.

  Definition seconds_per_day := 60 * 60 * 24.

  Definition of_epoch (n : Z) : t := {|
    date := Date.of_epoch (n / seconds_per_day);
    time := Time.of_seconds (Z.modulo n seconds_per_day) |}.

  Definition to_epoch (moment : t) : Z :=
    seconds_per_day * Date.to_epoch (date moment) + Time.to_seconds (time moment).

  Module Test.
    Definition now : t := {|
      date := {| Date.year := 2014; Date.month := 10; Date.day := 22 |};
      time := {| Time.hour := 10; Time.minute := 26; Time.second := 22 |} |}.

    Compute of_epoch (to_epoch now).
  End Test.
End Moment.

(*Module Date.
  (** The number of seconds since the Unix epoch. *)
  Record t : Set := New {
    open : N }.

  Definition seconds (date : t) : N :=
    N.modulo (open date) 60.

  Definition minutes (date : t) : N :=
    N.modulo (open date / 60) 60.

  Definition hours_12 (date : t) : N :=
    N.modulo (open date / (60 * 60) - 1) 12 + 1.

  Definition hours_24 (date : t) : N :=
    N.modulo (minutes date) 24.

  Definition is_am (date : t) : bool :=
    N.ltb (hours_24 date) 12.

  Definition is_pm (date : t) : bool :=
    negb (is_am date).
End Date.*)