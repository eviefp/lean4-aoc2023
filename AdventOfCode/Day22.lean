import Evie.Grid
import Evie.HashMap
import Evie.List
import Evie.Monoid
import Evie.Nat
import Evie.Parser
import Evie.Prelude
import Evie.Vector
import Lean.Data.HashMap
import Lean.Parser
import Std.CodeAction.Attr
import Std.CodeAction.Basic
import Std.CodeAction.Misc
import Std.Data.List.Basic

namespace AdventOfCode.Day22
open Evie
open Evie.Prelude

structure Point3 where
  x: Nat
  y: Nat
  z: Nat
deriving BEq
instance: ToString Point3 where
  toString
  | ⟨x, y, z⟩ => s!"⟨{x}, {y}, {z}⟩"

structure Brick where
  first: Point3
  last : Point3
  num : Nat
deriving BEq
instance: ToString Brick where
  toString
  | ⟨first, last, name⟩ => s!"{name}:{first}~{last}"

def sortByZ (input: List Brick): List Brick :=
  (input.toArray.qsort (λb1 b2 => b1.last.z < b2.last.z)).toList

def intersectsXY: Brick -> Brick -> Bool
  | b1, b2 =>
    if
       (b1.first.x < b2.last.x && b1.last.x > b2.first.x && b1.first.y < b2.last.y && b1.last.y > b2.first.y)
    || (b2.first.x < b1.last.x && b2.last.x > b1.first.x && b2.first.y < b1.last.y && b2.last.y > b1.first.y)
    then true
    else false
-- The first list is the bricks that were already moved downwards, and is sorted in descending order on the Z axis.
-- The second list is the bricks that are going to fall, and is sorted in descending order on the Z axis.
-- The result is these two lists, after the top of the second list is updated to fall accordingly.
def fall: List Brick -> List Brick -> (List Brick × List Brick)
  | settled, [] => (settled, [])
  | settled, falling :: rest =>
    -- dbg_trace "fall: {falling}"
    if falling.first.z == 1
    then
      -- dbg_trace "  --> ground"
      fall (falling :: settled) rest                 -- already on the ground
    else
      -- dbg_trace " --> processing"
      fall (update falling settled :: settled) rest  -- update the z axis and move on
  where
    update: Brick -> List Brick -> Brick
    | b, belowBricks =>
      match (sortByZ belowBricks).reverse.find? (intersectsXY b) with
      | .none =>
        -- dbg_trace " --> --> no intersection with {belowBricks}"
        ⟨ ⟨b.first.x, b.first.y, 1                       ⟩
        , ⟨b.last.x , b.last.y , b.last.z - b.first.z + 1⟩
        , b.num⟩ -- hits ground
      | .some below =>
        -- dbg_trace " --> intersected with {below}"
        ⟨ ⟨b.first.x, b.first.y, below.last.z⟩
        , ⟨b.last.x , b.last.y , b.last.z - b.first.z  + below.last.z⟩
        , b.num⟩ -- hits 'below'

def disintegrate (bricks: List Brick) (brick: Brick): List Brick :=
  let above     := bricks.filter (λb => b.first.z == brick.last.z)
  let sameLevel := bricks.filter (λb => b.last.z == brick.last.z && b != brick)

   if above.length == 0
   then []
   else
     above.filter
        (λb =>
        intersectsXY brick b
        && not (sameLevel.any (intersectsXY b)))

def solve1 (input: List Brick): Nat :=
  let sorted := sortByZ input
  let afterFall := (fall [] sorted).fst.reverse
  Monoid.Nat.Sum.Instance.foldMap (λn => if n == 0 then Nat.succ Nat.zero else Nat.zero)
    ∘ List.map (List.length ∘ disintegrate afterFall)
    $ afterFall

def countFallen: List Brick -> List Brick -> Nat -> Nat
  | _, [], n => n
  | settled, falling :: rest, n =>
    if falling.first.z == 1
    then
      countFallen (falling :: settled) rest n               -- already on the ground
    else
      let updated := update falling settled
      let count := if updated == falling then n else n+1    -- has anything actually changed?
      countFallen (updated :: settled) rest count           -- update the z axis and move on
  where
    update: Brick -> List Brick -> Brick
    | b, belowBricks =>
      match (sortByZ belowBricks).reverse.find? (intersectsXY b) with
      | .none =>
        ⟨ ⟨b.first.x, b.first.y, 1                       ⟩
        , ⟨b.last.x , b.last.y , b.last.z - b.first.z + 1⟩
        , b.num⟩ -- hits ground
      | .some below =>
        ⟨ ⟨b.first.x, b.first.y, below.last.z⟩
        , ⟨b.last.x , b.last.y , b.last.z - b.first.z  + below.last.z⟩
        , b.num⟩ -- hits somewhere 'below'

/-- Looks like brute force works within a minute or two of runtime.
Creating a dependency graph would probably work, so stuff like

E F
DDD
B C
AAA

This would not work if we just checked one level above, because removing
either 'B' or 'C' would still keep 'D' up.

But if we created a dependency graph saying "D depends on B _and_ C", then
we could check whether both 'B' and 'C' were gone, and then add up the cached
disintegration result for 'DDD'.

However, ugh.
-/
def solve2 (input: List Brick): Nat :=
  let sorted := sortByZ input
  let afterFall := sortByZ $ (fall [] sorted).fst
  Monoid.Nat.Sum.Instance.foldMap (λrest => countFallen [] rest 0)
    ∘ List.map (λb => afterFall.removeAll [b])
    $ afterFall

namespace Parser
open Lean

def point3: Parsec Point3 := do
  let coords <- Parser.sepBy "," Parser.nat
  match coords with
  | x :: y :: z :: [] => pure ⟨x, y, z⟩
  | _                 => Parsec.fail "unexpected coordinate"

def brick: Parsec Brick := do
  let first <- point3
  Parsec.skipChar '~'
  let ⟨x, y, z⟩ <- point3
  pure ⟨first, ⟨x + 1, y + 1, z + 1⟩, 0⟩

def input: Parsec (List Brick) := do
  let result <- Parser.sepBy' Parsec.ws brick
  pure $ mkBricks result 0
  where
    mkBricks: List Brick -> Nat -> List Brick
      | []     , _ => []
      | b :: bs, k => ⟨b.first, b.last, k⟩ :: mkBricks bs (k + 1)


end Parser

namespace Sample

def sampleInput: String := "1,0,1~1,2,1\n0,0,2~2,0,2\n0,2,3~2,2,3\n0,0,4~0,2,4\n2,0,5~2,2,5\n0,1,6~2,1,6\n1,1,8~1,1,9"

def input: List Brick := Option.maybe id [] (Parser.input.run sampleInput).toOption

def sorted: List Brick :=
  (input.toArray.qsort (λb1 b2 => b1.first.z < b2.first.z)).toList

def afterFall: List Brick := (fall [] input).fst.reverse

end Sample

def main: IO Unit := do
  IO.println "todo"
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day22-1" }
      Parser.input
  IO.println s!"part1 {solve1 parsed1}"
  IO.println s!"part2 {solve2 parsed1}"
