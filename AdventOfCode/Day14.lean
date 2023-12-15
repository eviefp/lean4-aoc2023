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


namespace AdventOfCode.Day14
open Evie
open Evie.Prelude

inductive Cell where
  | Rock
  | Cube
  | Space
deriving BEq

instance: ToString Cell where
  toString
    | .Rock  => "O"
    | .Cube  => "#"
    | .Space => "."

def Cell.fromChar: Char -> Cell
  | 'O' => .Rock
  | '#' => .Cube
  | _   => .Space

abbrev Input := List String
abbrev Points x y := Lean.HashSet (Grid.Position x y)

def tilt
  (direction: Grid.Position x y -> Option (Grid.Position x y))
  (fold: (Nat × Nat → Points x y → Cell → Points x y) -> Points x y -> Grid x y Cell -> Points x y)
  (grid: Grid x y Cell):
  Grid x y Cell :=
  let rec isValid (hs: Points x y) (pos: Grid.Position x y): List (Grid.Position x y) -> (Grid.Position x y)
    | []         => pos
    | pos' :: xs =>
      match grid.get pos', hs.find? pos' with
      | .Cube, _      => pos
      | _    , some _ => pos
      | _    , _      => isValid hs pos' xs


  let go (idx: Nat × Nat) (hs: Points x y) (cell: Cell): Points x y :=
    match Grid.Position.mkPosition x y idx.fst idx.snd, cell with
    | _, .Cube | _, .Space => hs
    | .none    , _         => hs
    | .some pos, .Rock     =>
      hs.insert
        (isValid hs pos
          ∘ List.replicate' direction (max x y)
          $ pos)

  let reform (p: Points x y) (idx: Nat × Nat) (c: Cell): Cell :=
    match c, Grid.Position.mkPosition x y idx.fst idx.snd >>= p.find? with
      | .Cube, _   => .Cube
      | _, .some _ => .Rock
      | _, _       => .Space

  grid.mapWithPosition
    ∘ reform
    ∘ fold go Lean.HashSet.empty
    $ grid

def northLoad (grid: Grid x y Cell): Nat :=
  let go (idx: Nat × Nat) (sum: Nat) (c: Cell): Nat :=
    if c == Cell.Rock
    then sum + (y - idx.snd)
    else sum
  Grid.foldWithIdx go 0 grid

def solve1 (input: Input): Nat :=
  let y := input.length
  match input with
  | [] => 0
  | i :: _ =>
    let x := i.length
    let grid := Grid.fromList x y .Space
                  $ input.map (List.map Cell.fromChar ∘ String.toList)

    northLoad
      ∘ tilt Grid.Position.up Grid.foldlWithIdx
      $ grid

structure Accumulator (x y: Nat) where
  grid: Grid x y Cell
  results: List Nat
  cycle: List Nat
  cycleIndex: Nat
  beforeLength: Nat

def computeSolution (before: Nat) (cycle: List Nat): Nat :=
  let withoutCycle := 1000000000 - before - 1
  let index := Nat.mod withoutCycle cycle.length
  cycle.getD index 0

def solve2 (input: Input): Nat :=
  let y := input.length
  match input with
  | [] => 0
  | i :: _ =>
    let x := i.length
    let grid := Grid.fromList x y .Space
                  $ input.map (List.map Cell.fromChar ∘ String.toList)

    let result :=
      Nat.foldM
          (λ n acc => -- this monstrosity is just cycle detection
            if acc.cycleIndex > 0 && acc.cycle.length == acc.cycleIndex && n > 10 -- let's run at least 10 simulations
              then Except.error $ computeSolution acc.beforeLength acc.cycle
            else
              let newGrid :=
                tilt Grid.Position.right Grid.foldrWithIdx
                  ∘ tilt Grid.Position.down Grid.foldrWithIdx
                  ∘ tilt Grid.Position.left Grid.foldlWithIdx
                  ∘ tilt Grid.Position.up Grid.foldlWithIdx
                  $ acc.grid
              let load := northLoad newGrid
              if acc.cycleIndex == 0 -- not in a cycle, look for one
              then -- this might be wrong if we think we're in a cycle but the real cycle starts
                match acc.results.findIdx? (. == load) with
                | .none     => Except.ok (Accumulator.mk newGrid (load :: acc.results) [] 0 acc.beforeLength) -- no cycle here, carry on
                | .some idx =>
                  let cycle := List.reverse ∘ List.take (idx + 1) $ acc.results
                  let rest := acc.results.length - idx - 1
                  Except.ok (Accumulator.mk newGrid (load :: acc.results) cycle 1 rest) -- potential cycle, investigate
              else
                if acc.cycle.get? acc.cycleIndex == some load
                then Except.ok (Accumulator.mk newGrid (load :: acc.results) acc.cycle (acc.cycleIndex + 1) acc.beforeLength) -- cycle step
                else Except.ok (Accumulator.mk newGrid (load :: acc.results) [] 0 0) -- bad cycle
          )
          (Accumulator.mk grid [] [] 0 0)
          500
    match result with
      | Except.ok _    => 0
      | Except.error r => r

namespace Sample

def sampleInput1: List String :=
  [ "O....#...."
  , "O.OO#....#"
  , ".....##..."
  , "OO.#O....O"
  , ".O.....O#."
  , "O.#..O.#.#"
  , "..O..#O..O"
  , ".......O.."
  , "#....###.."
  , "#OO..#...."
  ]

-- #eval solve2 sampleInput1

end Sample

def main: IO Unit := do
  let lines <- Array.toList <$> IO.FS.lines { toString := "./data/day14-1" }
  IO.println s!"part1: {solve1 lines}"
  IO.println s!"part2: {solve2 lines}"
