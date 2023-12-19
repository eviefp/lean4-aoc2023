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

namespace AdventOfCode.Day18
open Evie
open Evie.Prelude

structure Point where
  x: Int
  y: Int
deriving BEq, Hashable

instance: ToString Point where
  toString p := s!"⟨{p.x}, {p.y}⟩"

inductive Direction where
  | R | L | U | D
instance: ToString Direction where
  toString
    | .R => "R"
    | .L => "L"
    | .U => "U"
    | .D => "D"

structure Step where
  direction: Direction
  steps: Nat
  color: String

def solve1: List Step -> Nat :=
  Int.natAbs
    ∘ computeArea 0 0
    ∘ (λpoints => List.zip points (points.drop 1))
    ∘ buildPoints ⟨0, 0⟩
  where
    buildPoints: Point -> List Step -> List Point
      | last, [] => [last]
      | point, s :: ss =>
        let nextPoint := match point, s with
            | ⟨x, y⟩, ⟨.L , steps, _⟩ => ⟨x - steps, y        ⟩
            | ⟨x, y⟩, ⟨.R , steps, _⟩ => ⟨x + steps, y        ⟩
            | ⟨x, y⟩, ⟨.U , steps, _⟩ => ⟨x        , y - steps⟩
            | ⟨x, y⟩, ⟨.D , steps, _⟩ => ⟨x        , y + steps⟩
        point :: buildPoints nextPoint ss

    computeArea: Int -> Int -> List (Point × Point) -> Int
      | interior, perimeter, [] => Int.natAbs interior + (Int.div perimeter 2 + 1)
      | interior, perimeter, (⟨x1, y1⟩, ⟨x2, y2⟩) :: ps =>
        if x1 == x2
        then computeArea interior (perimeter + Int.natAbs (y1 - y2)) ps
        else computeArea (interior + y1 * (x2 - x1)) (perimeter + Int.natAbs (x2-x1)) ps

def solve2: List Step -> Nat :=
  solve1 ∘ List.map process

  where
    toDirection: Char -> Direction
      | '0' => .R
      | '1' => .D
      | '2' => .L
      | _   => .U

    toSteps: List Char -> Nat -> Nat
      | [], _ => 0
      | d :: xs, k => (hexDigitToNat d * Nat.pow 16 k) + toSteps xs (k + 1)

    hexDigitToNat: Char -> Nat
      | 'a' => 10
      | 'b' => 11
      | 'c' => 12
      | 'd' => 13
      | 'e' => 14
      | 'f' => 15
      | x   => x.toString.toNat!

    process: Step -> Step :=
      λ step => ⟨toDirection step.color.back, toSteps (step.color.dropRight 1).toList.reverse 0, step.color⟩

namespace Parser
open Lean

def direction: Parsec Direction :=
  Parser.sum
    [ Parsec.skipChar 'R' *> pure .R
    , Parsec.skipChar 'L' *> pure .L
    , Parsec.skipChar 'U' *> pure .U
    , Parsec.skipChar 'D' *> pure .D
    ]

def step: Parsec Step := do
  let direction <- direction
  Parsec.ws
  let steps <- Parser.nat
  Parsec.ws
  Parsec.skipString "(#"
  let color <- Parsec.many1Chars $ Parsec.satisfy (. != ')')
  Parsec.skipChar ')'
  Parsec.ws
  pure $ ⟨direction, steps, color⟩

def input: Parsec (List Step) :=
  Parser.many1 step

end Parser

namespace Sample

def sampleInput: String := "R 6 (#70c710)\nD 5 (#0dc571)\nL 2 (#5713f0)\nD 2 (#d2c081)\nR 2 (#59c680)\nD 2 (#411b91)\nL 5 (#8ceee2)\nU 2 (#caa173)\nL 1 (#1b58a2)\nU 2 (#caa171)\nR 2 (#7807d2)\nU 3 (#a77fa3)\nL 2 (#015232)\nU 2 (#7a21e3)"

def input: List Step := Option.maybe id [] (Parser.input.run sampleInput).toOption

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day18-1" }
      Parser.input
  IO.println s!"part1 {solve1 parsed1}"
  IO.println s!"part2 {solve2 parsed1}"
