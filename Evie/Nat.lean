namespace Evie.Nat

def range (m: Nat) (n: Nat) : List Nat :=
  let go (iter: Nat) (xs: List Nat) : List Nat :=
    (iter + m) :: xs
  (n - m).foldRev go []
