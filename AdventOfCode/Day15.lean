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


namespace AdventOfCode.Day15
open Evie
open Evie.Prelude


def hash: String -> Nat :=
  List.foldl hashChar 0 ∘ String.toList
  where
    hashChar (acc: Nat) (ch: Char): Nat :=
      Nat.mod
        ((acc + ch.toNat) * 17)
        256

def solve1: List String -> Nat :=
  Monoid.Nat.Sum.Instance.foldMap hash

-- Part 2

abbrev FocalLength := Nat

inductive Operation where
  | Remove : Operation
  | Add    : FocalLength -> Operation

structure Step where
  target: String
  operation: Operation

structure Box where
  slots: Array (String × FocalLength)

def step: Array Box -> Step -> Array Box
  | boxes, ⟨target, .Remove⟩ => remove target boxes
  | boxes, ⟨target, .Add x⟩  => add target x boxes
  where
    remove (target: String) (boxes: Array Box): Array Box :=
      let idx := hash target
      boxes.modify
        idx
        (λ box =>
          Box.mk
           ∘ Array.eraseIdx box.slots
           ∘ Option.maybe id box.slots.size
           $ box.slots.findIdx?
             (λ (boxTarget, _) => target == boxTarget)
        )

    add (target: String) (fl: FocalLength) (boxes: Array Box): Array Box :=
      let idx := hash target
      boxes.modify
        idx
        (λ box =>
          match box.slots.findIdx? (λ (boxTarget, _) => target == boxTarget) with
          | .none => Box.mk $ box.slots.push (target, fl)
          | .some idx => Box.mk $ box.slots.modify idx (λ _ => (target, fl))
        )

def solve2: Array Step -> Nat :=
  Monoid.Nat.Sum.Instance.foldMap (uncurry focusingPower)
    ∘ Array.toList
    ∘ (λ a => a.mapIdx (λ f box => (f.val, box)))
    ∘ Array.foldl step initBoxes
  where
    focusingPower (boxId: Nat) (box: Box): Nat :=
      Array.foldl (λ acc (slotNumber, focalLength) => boxId.succ * slotNumber.succ * focalLength + acc) 0
        $ box.slots.mapIdx (λ f (_, fl) => (f.val, fl))

    initBoxes: Array Box := Array.mkArray 256 $ Box.mk #[]

namespace Parser
open Lean

def step1: Parsec String :=
  Parsec.many1Chars (Parsec.satisfy (. != ','))

def input1: Parsec (List String) := do
  let first <- step1
  let rest <- Parser.many1 (Parsec.skipChar ',' *> step1)
  pure $ first :: rest

def operation: Parsec Operation :=
  Parser.sum
    [ pure .Remove <* Parsec.pchar '-'
    , .Add <$> (Parsec.pchar '=' *> Parser.nat)
    ]

def step2: Parsec Step := do
  let target <- Parsec.many1Chars Parsec.asciiLetter
  let operation <- operation
  pure $ ⟨target, operation⟩

def input2: Parsec (Array Step) := do
  let first <- step2
  let rest <- Parsec.many1 (Parsec.skipChar ',' *> step2)
  pure $ Array.insertAt! rest 0 first

end Parser

namespace Sample

def sampleInput: String := "rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7"

def input1: List String := Option.maybe id [] (Parser.input1.run sampleInput).toOption

def input2: Array Step := Option.maybe id #[] (Parser.input2.run sampleInput).toOption

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day15-1" }
      Parser.input1
  IO.println s!"part1 {solve1 parsed1}"

  let parsed2 <-
    Parser.parseFile
      { toString := "./data/day15-1" }
      Parser.input2
  IO.println s!"part2 {solve2 parsed2}"
