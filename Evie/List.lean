import Evie.Prelude

namespace Evie.List
open Evie.Prelude

def product (l1: List α) (l2: List β) : List (α × β) :=
  let go (acc: List (α × β)) (a: α) : List (α × β) :=
    l2.foldl (fun xs b => (a, b) :: xs) acc
  l1.foldl go []

def catMaybes (l: List (Option α)): List α :=
  l.foldl
    (fun xs => Option.maybe (. :: xs) xs)
    []

def groupsOfTwo: List α -> List (α × α)
  | []      => []
  | x :: xs =>
    List.append
      (List.foldr (λ y l => (x, y) :: l) [] xs)
      $ groupsOfTwo xs
