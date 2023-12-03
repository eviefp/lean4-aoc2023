namespace Evie.List

def product (l1: List α) (l2: List β) : List (α × β) :=
  let go (acc: List (α × β)) (a: α) : List (α × β) :=
    l2.foldl (fun xs b => (a, b) :: xs) acc
  l1.foldl go []
