import Evie.HashMap
import Evie.Monoid
import Evie.List
import Evie.Nat
import Evie.Parser
import Evie.Prelude
import Evie.Vector
import Lean.Data.HashMap
import Lean.Parser
import Std.Data.Nat.Gcd
import Std.CodeAction

namespace AdventOfCode.Day12
open Evie
open Evie.Prelude

inductive Spring where
  | Operational
  | Damaged
  | Unknown
deriving BEq, Hashable

instance: ToString Spring where
  toString
    | .Operational => "."
    | .Damaged     => "#"
    | .Unknown     => "?"

structure Input where
  record: List Spring
  series: List Nat
deriving Inhabited, BEq, Hashable

instance: ToString Input where
  toString i := String.join (i.record.map ToString.toString) ++ " " ++ i.series.toString

def countMaxDamaged: List Spring -> Nat :=
  List.length
    ∘ List.filter (not ∘ (BEq.beq Spring.Operational))

def numberOfVariants: List Spring -> List Nat -> Bool -> StateRefT (Lean.HashMap Input Nat) IO  Nat
  | Spring.Operational :: xs, 0 :: ys, true => numberOfVariants xs ys false -- skip the zero
  | Spring.Operational :: xs, ys, false => numberOfVariants xs ys false -- skipping along
  | Spring.Operational :: _, _, true => pure 0 -- if we were inside a group but got a wrong entry, stop
  | Spring.Damaged :: _, 0 :: _, _ => pure 0
  | Spring.Damaged :: xs, (k + 1) :: ys, _ => numberOfVariants xs (k :: ys) true -- we have to start/continue along
  | Spring.Unknown :: xs, [], false => numberOfVariants xs [] false -- fill in with operationals if we're done counting
  | Spring.Unknown :: xs, 0 :: ys, _ => numberOfVariants xs ys false -- just done with a group so go back to outside a group, must use operational
  | Spring.Unknown :: xs, (k + 1) :: ys, true => numberOfVariants xs (k :: ys) true -- inside an ongoing group, have to use broken
  | Spring.Unknown :: xs, (k + 1) :: ys, false => -- we diverge!
      let maxDamaged := countMaxDamaged xs
      let neededDamaged := Monoid.Nat.Sum.Instance.fold (k :: ys)
      if maxDamaged < neededDamaged
        then pure 0 -- impossible to fulfil, don't diverge
        else do
          let cached <- flip Lean.HashMap.find? ⟨Spring.Unknown :: xs, (k+1) :: ys⟩ <$> get
          match cached with
            | .some result => pure result
            | .none => do
                let operational <- numberOfVariants xs ((k + 1) :: ys) false
                let broken <- (numberOfVariants xs ((k) :: ys) true)
                modify (λhm => hm.insert ⟨Spring.Unknown :: xs, (k+1) :: ys⟩ (operational + broken))
                pure $ operational + broken
  | [], [0], _ => pure 1
  | [], [], _ => pure 1
  | _, _, _ => pure 0

def solve: List Input -> IO Nat :=
  Monoid.Nat.Sum.Instance.foldMapM
    (λ i =>
      let state := numberOfVariants i.record i.series false
      state.run' Lean.HashMap.empty
    )

def updateInput (input: Input): Input :=
  { record := List.intercalate [ Spring.Unknown ] $ List.replicate 5 input.record
  , series := List.join $ List.replicate 5 input.series
  }

namespace Parser
open Lean

def spring: Parsec Spring := do
  (Parsec.pchar '.' *> pure Spring.Operational)
    <|> (Parsec.pchar '#' *> pure Spring.Damaged)
    <|> (Parsec.pchar '?' *> pure Spring.Unknown)

def line: Parsec Input := do
  Parsec.ws
  let record <- Parser.many1 spring
  Parsec.skipChar ' '
  let seriesFirst <- Parser.nat
  let series <- Parser.many1 (Parsec.skipChar ',' *> Parser.nat)
  pure
    { record := record
    , series := seriesFirst :: series
    }

def input: Parsec (List Input) :=
  Parser.many1 line

end Parser

namespace Sample

def sampleInput1: String := "???.### 1,1,3\n.??..??...?##. 1,1,3\n?#?#?#?#?#?#?#? 1,3,1,6\n????.#...#... 4,1,1\n????.######..#####. 1,6,5\n?###???????? 3,2,1"

def input1: List Input := Option.getD (Except.toOption $ Parser.input.run sampleInput1) []

def countRawVariants: List Input -> Nat :=
  Monoid.Nat.Max.Instance.foldMap
    (  Nat.pow 2
        ∘ List.length
        ∘ List.filter (BEq.beq Spring.Unknown)
        ∘ Input.record
    )

def line: Input := input1[5]!

#eval solve input1

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day12-1" }
      Parser.input

  let result1 <- solve parsed1
  IO.println s!"part1 {result1}"

  let input2 := parsed1.map updateInput

  let result2 <- solve input2
  IO.println s!"part2 {result2}"
