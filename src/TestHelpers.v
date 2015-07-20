(** Some functions used to do the tests. *)
Require Import Coq.Lists.List.

Import ListNotations.

Module List.
  Fixpoint map_pair (A B C : Type) (f : A -> B -> C) (l : list (A * B))
    : list C :=
    match l with
    | [] => []
    | (x, y) :: l => f x y :: map_pair _ _ _ f l
    end.
  Arguments map_pair [A B C] _ _.

  Fixpoint map_triple (A B C D : Type) (f : A -> B -> C -> D)
    (l : list (A * B * C)) : list D :=
    match l with
    | [] => []
    | (x, y, z) :: l => f x y z :: map_triple _ _ _ _ f l
    end.
  Arguments map_triple [A B C D] _ _.
End List.