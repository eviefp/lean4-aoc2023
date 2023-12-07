import Evie.FunctorOf
import Evie.Monoid
import Evie.String
import Evie.Traversable

namespace AdventOfCode.Day1

open Evie

def findDigit1 (str: String): Option Nat :=
  if str.front.isDigit then
     str.front.toString.toNat?
   else none

def findDigit2 (str: String): Option Nat :=
  if str.front.isDigit then
     str.front.toString.toNat?
  else if str.startsWith "zero" then some 0
  else if str.startsWith "one" then some 1
  else if str.startsWith "two" then some 2
  else if str.startsWith "three" then some 3
  else if str.startsWith "four" then some 4
  else if str.startsWith "five" then some 5
  else if str.startsWith "six" then some 6
  else if str.startsWith "seven" then some 7
  else if str.startsWith "eight" then some 8
  else if str.startsWith "nine" then some 9
  else none

def calculate (n1: Nat) (n2: Nat): Nat := n1 * 10 + n2

def solve (findDigit: String -> Option Nat) (input: String): Option Nat := do
  let slices :=
    FunctorOf.map2 findDigit
      ∘ FunctorOf.map1 String.slices
      $ input.splitOn "\n"

  let firstDigit := Monoid.First.Instance.fold <$> slices
  let lastDigit := Monoid.Last.Instance.fold <$> slices

  FunctorOf.map1 (List.foldl Nat.add 0)
    ∘ Traversable.List.Instance.sequenceA
    $ List.zipWith (Traversable.liftA2 calculate) firstDigit lastDigit

def main: IO Unit := do
  let result1 <-
    FunctorOf.map1 (solve findDigit1)
      $ IO.FS.readFile { toString := "./data/day1-1" }
  IO.println s!"part1: {result1}"

  let result2 <-
    FunctorOf.map1 (solve findDigit2)
      $ IO.FS.readFile { toString := "./data/day1-2" }
  IO.println s!"part2: {result2}"
