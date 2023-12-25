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

namespace AdventOfCode.Day23
open Evie
open Evie.Prelude

inductive Tile where
  | Path
  | Forrest
  | NorthSlope
  | SouthSlope
  | EastSlope
  | WestSlope
deriving BEq

def SomeGrid (pair: Nat × Nat): Type := Grid pair.fst pair.snd Tile

def step (grid: Grid x y Tile): Grid.Position x y -> List (Grid.Position x y) -> List (List (Grid.Position x y))
  | pos, ps =>
    let variants := match grid.get pos with
                    | .Forrest    => []
                    | .Path       => pos.neighbors
                    | .NorthSlope => Option.toList pos.up
                    | .SouthSlope => Option.toList pos.down
                    | .EastSlope  => Option.toList pos.right
                    | .WestSlope  => Option.toList pos.left

    -- no repeats, no stepping in the forrest
    List.map (λp => [p])
    $ variants.filter
      (λ v => not $ ps.elem v || grid.get v == .Forrest)

def solve1 (input: Sigma SomeGrid): Nat :=
  let (xn, yn) := input.fst

  let start  := Grid.Position.mkPosition (input.fst.fst) (input.fst.snd) 1 0
  let target := Grid.Position.mkPosition (input.fst.fst) (input.fst.snd) (xn-2) (yn-1)

  match start, target with
  | .some s, .some t =>
    Grid.Position.longestPath s t (step input.snd) - 1
  | _, _ => 0

partial def go (grid: Grid x y Tile): Grid.Position x y -> List (Grid.Position x y) -> List (Grid.Position x y)
| pos, ps =>
  let res := pos.neighbors.filter
    (λ v => not $ ps.elem v || grid.get v == .Forrest)
  match res with
  | p' :: [] => p' :: go grid p' (pos :: ps)
  | _        => []

def step2 (grid: Grid x y Tile): Grid.Position x y -> List (Grid.Position x y) -> List (List (Grid.Position x y))
  | pos, ps =>
    let res := pos.neighbors.filter
      (λ v => not $ ps.elem v || grid.get v == .Forrest)
    match res with
    | p' :: [] => [ List.reverse $ p' :: go grid p' (pos :: ps) ]
    | ps'      => ps'.map (λl => [l])

def solve2 (input: Sigma SomeGrid): Nat :=
  let (xn, yn) := input.fst

  let start  := Grid.Position.mkPosition (input.fst.fst) (input.fst.snd) 1 0
  let target := Grid.Position.mkPosition (input.fst.fst) (input.fst.snd) (xn-2) (yn-1)

  match start, target with
  | .some s, .some t =>
    Grid.Position.longestPath s t (step2 input.snd) - 1
  | _, _ => 0

namespace Parser
open Lean

def tile: Parsec Tile :=
  Parser.sum
    [ Parsec.skipChar '.' *> pure .Path
    , Parsec.skipChar '#' *> pure .Forrest
    , Parsec.skipChar '^' *> pure .NorthSlope
    , Parsec.skipChar 'v' *> pure .SouthSlope
    , Parsec.skipChar '>' *> pure .EastSlope
    , Parsec.skipChar '<' *> pure .WestSlope
    ]

def grid: Parsec (List (List Tile)) :=
  Parser.sepBy' Parsec.ws $ Parser.many1 tile

def input: Parsec (Sigma SomeGrid) := do
  let g <- grid
  match g with
  | [] => Parsec.fail "empty first line"
  | head :: _ => do
    let x := head.length
    let y := g.length
    pure $ ⟨(x, y), Grid.fromList x y .Forrest g⟩

end Parser

namespace Sample

def sampleInput := "#.#####################\n#.......#########...###\n#######.#########.#.###\n###.....#.>.>.###.#.###\n###v#####.#v#.###.#.###\n###.>...#.#.#.....#...#\n###v###.#.#.#########.#\n###...#.#.#.......#...#\n#####.#.#.#######.#.###\n#.....#.#.#.......#...#\n#.#####.#.#.#########v#\n#.#...#...#...###...>.#\n#.#.#v#######v###.###v#\n#...#.>.#...>.>.#.###.#\n#####v#.#.###v#.#.###.#\n#.....#...#...#.#.#...#\n#.#########.###.#.#.###\n#...###...#...#...#.###\n###.###.#.###v#####v###\n#...#...#.#.>.>.#.>.###\n#.###.###.#.###.#.#v###\n#.....###...###...#...#\n#####################.#\n"

def input: Sigma SomeGrid :=
  Option.maybe
    id
    (Sigma.mk (0, 0) $ Grid.replicate 0 0 Tile.Forrest)
    (Parser.input.run sampleInput).toOption

-- #eval solve1 input
-- #eval solve2 input

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day23-1" }
      Parser.input
  IO.println s!"part1 {solve1 parsed1}"
  IO.println s!"part2 {solve2 parsed1}"
