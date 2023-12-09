import Evie.HashMap
import Evie.Monoid
import Evie.List
import Evie.Parser
import Evie.Prelude
import Lean.Data.HashMap
import Lean.Parser
import Std.Data.Nat.Gcd
import Std.CodeAction

namespace AdventOfCode.Day9
open Evie
open Evie.Prelude

namespace Parser
open Lean

def line: Parsec (List Int) := do
  Parsec.ws
  let head <- Parser.int
  let tail <- Parser.many1 (Parsec.skipChar ' ' *> Parser.int)
  pure $ head :: tail

def input: Parsec (List (List Int)) :=
  Parser.many1 line

end Parser

def computeNextStep: List Int -> List Int
  | x :: y :: xs => (y - x) :: computeNextStep (y :: xs)
  | _ => []

def computeSeries (series: List Int): List (List Int) :=
  Nat.fold
    (λ _n acc => computeNextStep acc.head! :: acc)
    series.length -- there can't be more than .length steps
    [series]

def computeNextNumber: List (List Int) -> Int :=
  let rec last: List Int -> Int
    | x :: [] => x
    | _ :: xs => last xs
    | _       => 0

  Monoid.Int.Sum.Instance.foldMap last

def solve: List (List Int) -> Int :=
  Monoid.Int.Sum.Instance.foldMap (computeNextNumber ∘ computeSeries)

def sampleInput: String := "0 3 6 9 12 15\n1 3 6 10 15 21\n10 13 16 21 30 45"

def parsedInput: List (List Int) := (Parser.input.run sampleInput).toOption.get!

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day9-1" }
      Parser.input
  IO.println s!"part1: {solve parsed1}"

  let reversed := List.map List.reverse parsed1
  IO.println s!"part2: {solve reversed}"
