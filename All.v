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

  Definition of_julian_day (is_gregorian : bool) (n : Z) : t :=
    let a := n + 32044 in
    let b := if is_gregorian then (4 * a + 3) / 146097 else 0 in
    let c := if is_gregorian then a - (b * 146097) / 4 else n + 32082 in
    let d := (4 * c + 3) / 1461 in
    let e := c - (1461 * d) / 4 in
    let m := (5 * e + 2) / 153 in
    {|
      day := e - (153 * m + 2) / 5 + 1;
      month := m + 3 - 12 * (m / 10);
      year := b * 100 + d - 4800 + m / 10 |}.

  Definition to_julian_day (is_gregorian : bool) (date : t) : Z :=
    let a := (14 - month date) / 12 in
    let y := year date + 4800 - a in
    let m := month date + 12 * a - 3 in
    if is_gregorian then
      day date + (153 * m + 2) / 5 + y * 365 + y / 4 - y / 100 + y / 400 - 32045
    else
      day date + (153 * m + 2) / 5 + y * 365 + y / 4 - 32083.

  Compute of_julian_day true (to_julian_day true (New 2014 10 22)).
  Compute to_julian_day false (New (-4712) 1 1).

  Definition epoch : t := {|
    year := 1970;
    month := 1;
    day := 1 |}.

  Definition of_epoch_day (n : Z) : t :=
    of_julian_day true (n + to_julian_day true epoch).

  Definition to_epoch_day (date : t) : Z :=
    to_julian_day true date - to_julian_day true epoch.

  Compute of_epoch_day 16365.
End Date.

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