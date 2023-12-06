import Evie.Monoid

namespace AdventOfCode.Day6
open Evie

structure Run where
  time: Nat
  distance: Nat

def sampleInput1: List Run :=
  [ Run.mk  7   9
  , Run.mk 15  40
  , Run.mk 30 200
  ]

def puzzle1: List Run :=
  [ Run.mk 57  291
  , Run.mk 72 1172
  , Run.mk 69 1176
  , Run.mk 92 2026
  ]

def sampleInput2: Run where
  time := 71530
  distance := 940200

def puzzle2: Run where
  time := 57726992
  distance := 291117211762026

def computeStep (run: Run) (speed: Nat) (acc: Nat): Nat :=
  let distance := speed * (run.time - speed)
  if distance > run.distance
    then acc + 1
    else acc

-- The result is the number of possible solutions
def computeSolutions (record: Run): Nat :=
  Nat.fold (computeStep record) record.time 0

def solve: List Run -> Nat :=
  Monoid.Nat.Product.Instance.foldMap computeSolutions

def main: IO Unit := do
  IO.println s!"part1: {solve puzzle1}"

  IO.println s!"part2: {computeSolutions puzzle2}"
