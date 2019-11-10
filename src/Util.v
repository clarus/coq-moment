Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ErrorHandlers.All.
Require Import ListString.All.

Import ListNotations.

Definition eat_character (character : Ascii.ascii) (s : LString.t) : option LString.t :=
  match s with
  | [] => None
  | character' :: s' =>
    if LString.Char.eqb character character' then
      Some s'
    else
      None
  end.

(** Split a string after [length] characters. *)
Fixpoint split (length : nat) (s : LString.t) : option (LString.t * LString.t) :=
  match length with
  | O => Some ([], s)
  | S length =>
    match s with
    | [] => None
    | c :: s =>
      Option.bind (split length s) (fun result =>
      let (s1, s2) := result in
      Some (c :: s1, s2))
    end
  end.

(** Parse an integer padded with a fixed number of digits. *)
Definition parse_padded_integer (digits : nat) (s : LString.t) : option (Z * LString.t) :=
  Option.bind (split digits s) (fun x =>
  let (year, s) := x in
  Option.bind (LString.to_N 10 year) (fun year =>
  Some (Z.of_N year, s))).
