import Evie.HashMap
import Evie.Monoid
import Evie.List
import Evie.Nat
import Evie.Parser
import Evie.Prelude
import Evie.Vector
import Lean.Data.HashMap
import Lean.Parser
import Std.Data.List.Basic
import Std.CodeAction.Attr
import Std.CodeAction.Basic
import Std.CodeAction.Misc


namespace AdventOfCode.Day13
open Evie
open Evie.Prelude

abbrev Terrain := Nat

abbrev Pattern := List Terrain

abbrev MirroredPatterns := (List Terrain × List Terrain)

abbrev Input := List MirroredPatterns

partial def mkPairs (length: Nat) (x y: Nat): List (Nat × Nat) :=
    if x == 0 || y + 1 == length
      then [(x, y)]
    else
      (x, y) :: (mkPairs length (x - 1) (y + 1))

def Pattern.reflectionIndex (pat: Pattern): List Nat :=
  let length := pat.length
  let inDuplicates (pair: Nat × Nat): Bool :=
    Option.maybe id false $ Nat.beq <$> pat.get? pair.fst <*> pat.get? pair.snd
  Nat.fold
    (λ index acc =>
      if List.all (mkPairs length index (index + 1)) inDuplicates
        then (index + 1) :: acc
        else acc)
     pat.length
     []

def solveImpl (pat: MirroredPatterns): Nat :=
  let line := List.headD (Pattern.reflectionIndex pat.fst) 0
  let col  := List.headD (Pattern.reflectionIndex pat.snd) 0

  col + (line * 100)

def solve: Input -> Nat :=
  Monoid.Nat.Sum.Instance.foldMap solveImpl

def pattern (pat: Pattern) (oldResult: Nat) (toggle: Nat × Nat): Option Nat := do
  let modifiedPat := pat.modifyNth (λn => n ^^^ Nat.pow 2 toggle.fst) toggle.snd
  let results := Pattern.reflectionIndex modifiedPat
  results.find? (. != oldResult)

def patterns (pat: Pattern) (oldResult: Nat): Nat :=
  let maxX := Nat.succ $ Nat.log2 $ Monoid.Nat.Max.Instance.fold pat
  let maxY := pat.length
  let indices := List.product (Nat.range 0 maxX) (Nat.range 0 maxY)
  Option.maybe id 0 $ indices.firstM (pattern pat oldResult)

def solveImpl2 (pat: MirroredPatterns): Nat :=
  let oldLine := List.headD (Pattern.reflectionIndex pat.fst) 0
  let oldCol  := List.headD (Pattern.reflectionIndex pat.snd) 0

  let line := patterns pat.fst oldLine
  let col  := patterns pat.snd oldCol

  col + (line * 100)

def solve2: Input -> Nat :=
  Monoid.Nat.Sum.Instance.foldMap solveImpl2

namespace Parser
open Lean

def toDigit: Char -> Nat
  | '#' => 1
  | _   => 0

def toNumber (str: String): Nat :=
  let binary := str.toList.toArray.reverse.mapIdx (λ idx digit => (toDigit digit) * 2 ^ idx.val)
  Monoid.Nat.Sum.Instance.fold binary.toList

def transpose: List String -> List String :=
  List.map List.asString
    ∘ List.transpose
    ∘ List.map String.toList


def input: Parsec Input := do
  let line <- Parser.many1 (Parsec.many1Chars (Parsec.satisfy (not ∘ (BEq.beq '\n'))) <* Parsec.skipChar '\n')
  let lines <- Parser.many1 (Parsec.skipChar '\n' *> Parser.many1 (Parsec.many1Chars (Parsec.satisfy (not ∘ (BEq.beq '\n'))) <* Parsec.skipChar '\n'))
  let input := line :: lines
  pure
    ∘ List.map (λ ls => (ls.map toNumber, toNumber <$> transpose ls))
    $ input

end Parser

namespace Sample

/--
#.##..##.
..#.##.#.
##......#
##......#
..#.##.#.
..##..##.
#.#.##.#.

#...##..#
#....#..#
..##..###
#####.##.
#####.##.
..##..###
#....#..#
-/
def sampleInput: String := "#.##..##.\n..#.##.#.\n##......#\n##......#\n..#.##.#.\n..##..##.\n#.#.##.#.\n\n#...##..#\n#....#..#\n..##..###\n#####.##.\n#####.##.\n..##..###\n#....#..#\n"

def input: Input :=
  match Parser.input.run sampleInput with
    | .ok r => r
    | _     => []

-- def line1: MirroredPatterns := input[0]!
-- def line2: MirroredPatterns := input[1]!

-- #eval line1

-- #eval Pattern.reflectionIndex line1.fst
-- #eval Pattern.reflectionIndex line2.fst

-- #eval Pattern.reflectionIndex line1.snd
-- #eval Pattern.reflectionIndex line2.snd

-- #eval patterns line2.fst (some 4)

-- #eval solveImpl2 line2

-- #eval solve input
-- #eval solve2 input

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day13-1" }
      Parser.input
  IO.println s!"part1 {solve parsed1}"
  IO.println s!"part2 {solve2 parsed1}"
