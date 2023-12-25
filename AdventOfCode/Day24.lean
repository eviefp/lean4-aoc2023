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

namespace AdventOfCode.Day24
open Evie
open Evie.Prelude

structure Point3 where
  x: Lean.Rat
  y: Lean.Rat
  z: Lean.Rat
instance: ToString Point3 where
  toString p := s!"⟨{p.x}, {p.y}, {p.z}⟩"

structure Vector3 where
  x: Int
  y: Int
  z: Int
instance: ToString Vector3 where
  toString v := s!"⟨{v.x}, {v.y}, {v.z}⟩"

structure Hailstone where
  position: Point3
  velocity: Vector3
instance: ToString Hailstone where
  toString h := s!"< {h.position} @ {h.velocity} >"

def intersectionXY: Hailstone -> Hailstone -> Option Point3
  | ⟨position₁, velocity₁⟩, ⟨position₂, velocity₂⟩ =>
    let first₁ := position₁
    let first₂ := nextPoint position₁ velocity₁
    let second₁ := position₂
    let second₂ := nextPoint position₂ velocity₂

    let denominator := ((first₁.x - first₂.x) * (second₁.y - second₂.y) - (first₁.y - first₂.y) * (second₁.x - second₂.x))

    if denominator == 0
    then .none
    else
        let px :=
        Lean.Rat.div
            ((first₁.x * first₂.y - first₁.y * first₂.x) * (second₁.x - second₂.x) - (first₁.x - first₂.x) * (second₁.x * second₂.y - second₁.y * second₂.x))
            denominator
        let py :=
        Lean.Rat.div
            ((first₁.x * first₂.y - first₁.y * first₂.x) * (second₁.y - second₂.y) - (first₁.y - first₂.y) * (second₁.x * second₂.y - second₁.y * second₂.x))
            denominator

        -- future check
        let px_first_increasing := first₂.x > first₁.x && px > first₁.x
        let px_first_decreasing := first₂.x < first₁.x && px < first₁.x
        let px_first := px_first_increasing || px_first_decreasing

        let px_second_increasing := second₂.x > second₁.x && px > second₁.x
        let px_second_decreasing := second₂.x < second₁.x && px <= second₁.x
        let px_second := px_second_increasing || px_second_decreasing

        let py_first_increasing := first₂.y > first₁.y && py > first₁.y
        let py_first_decreasing := first₂.y < first₁.y && py < first₁.y
        let py_first := py_first_increasing || py_first_decreasing

        let py_second_increasing := second₂.y > second₁.y && py > second₁.y
        let py_second_decreasing := second₂.y < second₁.y && py <= second₁.y
        let py_second := py_second_increasing || py_second_decreasing

        if px_first && px_second && py_first && py_second
        then .some ⟨px, py, 0⟩
        else .none

  where
    nextPoint: Point3 -> Vector3 -> Point3
    | ⟨x, y, z⟩, ⟨dx, dy, dz⟩ => ⟨x + dx, y + dy, z + dz⟩

def solve1 (min max: Int): List Hailstone -> Nat
  | h :: rest =>
    let hResult :=
      List.length
        ∘ List.filter isInBounds
        ∘ List.catMaybes
        $ List.zipWith intersectionXY (List.replicate rest.length h) rest
    hResult + solve1 min max rest
  | [] => 0
  where
    isInBounds: Point3 -> Bool
    | ⟨x, y, _⟩ =>
      if x >= min && x <= max && y >= min && y <= max
      then true
      else false

namespace Parser
open Lean

def point3: Parsec Point3 := do
  let x <- Parser.int
  Parsec.skipString ", "
  let y <- Parser.int
  Parsec.skipString ", "
  let z <- Parser.int
  pure ⟨x, y, z⟩

def vector3: Parsec Vector3 := do
  let x <- Parser.int
  Parsec.skipString ", "
  let y <- Parser.int
  Parsec.skipString ", "
  let z <- Parser.int
  pure ⟨x, y, z⟩

def hailstone: Parsec Hailstone := do
  let position <- point3
  Parsec.skipString " @ "
  let velocity <- vector3
  pure ⟨position, velocity⟩

def input: Parsec (List Hailstone) := Parser.sepBy' Parsec.ws hailstone

end Parser

namespace Sample

def sampleInput: String :=
"19, 13, 30 @ -2, 1, -2\n18, 19, 22 @ -1, -1, -2\n20, 25, 34 @ -2, -2, -4\n12, 31, 28 @ -1, -2, -1\n20, 19, 15 @ 1, -5, -3"

def input: List Hailstone := Option.maybe id [] (Parser.input.run sampleInput).toOption

-- #eval solve1 7 27 input

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day24-1" }
      Parser.input
  IO.println s!"part1 {solve1 200000000000000 400000000000000 parsed1}"
  IO.println s!"part2 solved in Haskell with z3 because no"
