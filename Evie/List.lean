import Evie.Prelude

namespace Evie.List
open Evie.Prelude

def replicate' (gen: α -> Option α) (count: Nat) (seed: α): List α :=
  if count = 0
  then [seed]
  else match gen seed with
    | .none => [seed]
    | .some next => seed :: replicate' gen (count - 1) next

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

/-- An auxiliary function for defining `permutations`. `permutationsAux2 t ts r ys f` is equal to
`(ys ++ ts, (insert_left ys t ts).map f ++ r)`, where `insert_left ys t ts` (not explicitly
defined) is the list of lists of the form `insert_nth n t (ys ++ ts)` for `0 ≤ n < length ys`.

    permutations_aux2 10 [4, 5, 6] [] [1, 2, 3] id =
      ([1, 2, 3, 4, 5, 6],
       [[10, 1, 2, 3, 4, 5, 6],
        [1, 10, 2, 3, 4, 5, 6],
        [1, 2, 10, 3, 4, 5, 6]]) -/
def permutationsAux2 (t : α) (ts : List α) (r : List β) : List α → (List α → β) → List α × List β
  | [], _ => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutationsAux2 t ts r ys (fun x: List α => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)

-- porting note: removed `[elab_as_elim]` per Mario C
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Status.20of.20data.2Elist.2Edefs.3F/near/313571979
/-- A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`. -/
def permutationsAux.rec {C : List α → List α → Sort v} (H0 : ∀ is, C [] is)
    (H1 : ∀ t ts is, C ts (t :: is) → C is [] → C (t :: ts) is) : ∀ l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
      H1 t ts is (permutationsAux.rec H0 H1 ts (t :: is)) (permutationsAux.rec H0 H1 is [])
  termination_by _ ts is => (List.length ts + List.length is, List.length ts)
  decreasing_by simp_wf; simp [Nat.succ_add]; decreasing_tactic

/-- An auxiliary function for defining `permutations`. `permutationsAux ts is` is the set of all
permutations of `is ++ ts` that do not fix `ts`. -/
def permutationsAux : List α → List α → List (List α) :=
  permutationsAux.rec (fun _ => []) fun t ts is IH1 IH2 =>
    List.foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)

/-- List of all permutations of `l`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]] -/
def permutations (l : List α) : List (List α) :=
  l :: permutationsAux l []

/-- `permutations'Aux t ts` inserts `t` into every position in `ts`, including the last.
This function is intended for use in specifications, so it is simpler than `permutationsAux2`,
which plays roughly the same role in `permutations`.

Note that `(permutationsAux2 t [] [] ts id).2` is similar to this function, but skips the last
position:

    permutations'Aux 10 [1, 2, 3] =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3], [1, 2, 3, 10]]
    (permutationsAux2 10 [] [] [1, 2, 3] id).2 =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3]] -/
@[simp]
def permutations'Aux (t : α) : List α → List (List α)
  | [] => [[t]]
  | y :: ys => (t :: y :: ys) :: (permutations'Aux t ys).map (List.cons y)

/-- List of all permutations of `l`. This version of `permutations` is less efficient but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `List.permutations_perm_permutations'`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]] -/
@[simp]
def permutations' : List α → List (List α)
  | [] => [[]]
  | t :: ts => (permutations' ts).bind <| permutations'Aux t
