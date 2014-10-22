Require Import Coq.ZArith.ZArith.
Require Import FunctionNinjas.All.
Require Import LString.All.

Local Open Scope Z.

Record t : Set := New {
  hour : Z;
  minute : Z;
  second : Z }.

Definition of_seconds (n : Z) : t :=
  let second := n mod 60 in
  let n := n / 60 in
  let minute := n mod 60 in
  let hour := n / 60 in
  {|
    hour := hour;
    minute := minute;
    second := second |}.

Definition to_seconds (time : t) : Z :=
  second time + 60 * (minute time + 60 * hour time).

Compute of_seconds @@ to_seconds @@ New 12 0 0.
