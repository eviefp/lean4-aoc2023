import Evie.HashMap
import Evie.Monoid
import Evie.Parser
import Evie.Prelude
import Lean.Data.HashMap
import Lean.Parser
import Std.Data.Nat.Gcd

namespace AdventOfCode.Day8
open Evie
open Evie.Prelude

inductive Step where
  | L
  | R

instance: ToString Step where
  toString
    | Step.L => "L"
    | Step.R => "R"

structure Node where
  name: String
  left: String
  right: String

instance: ToString Node where
  toString n := s!"{n.name} = ({n.left}, {n.right})"

structure Input where
  steps: List Step
  map: Lean.HashMap String Node

instance: ToString Input where
  toString i :=
    String.intercalate "\n"
      ∘ flip List.concat i.steps.toString
      ∘ List.map ToString.toString
      ∘ Evie.HashMap.values
      $ i.map

instance: Inhabited Input where
  default := { steps := [], map := Lean.HashMap.empty }

namespace Parser
open Lean

def step: Parsec Step :=
  choice
    [ Parsec.skipChar 'L' *> pure Step.L
    , Parsec.skipChar 'R' *> pure Step.R
    ]

def node: Parsec Node := do
  Parsec.ws

  let name <- Parsec.many1Chars Parsec.asciiLetter
  Parsec.skipString " = ("
  let left <- Parsec.many1Chars Parsec.asciiLetter
  Parsec.skipString ", "
  let right <- Parsec.many1Chars Parsec.asciiLetter
  Parsec.skipChar ')'

  pure
    { name  := name
    , left  := left
    , right := right
    }

def input: Parsec Input := do
  let steps <- Parser.many1 step
  let nodes <- Parser.many1 node

  let nodesWithName := List.map (λ n => (n.name, n)) nodes

  pure
    { steps := steps
    , map   := Evie.HashMap.fromList nodesWithName
    }

end Parser

def nextStep (map: Lean.HashMap String Node) (node: String) (step: Step): String :=
  match map.find? node, step with
    | .none, _ => panic! "unknown node {start}"
    | .some node, Step.L => node.left
    | .some node, Step.R => node.right

def findStartPositions: List String -> List String :=
  List.filter (λ s => s.endsWith "A")

partial def findEndSteps (stopCondition: String -> Bool) (input: Input) (stepNum: Nat) (currentNode: String): Nat :=
  if stopCondition currentNode
    then stepNum
    else
      match input.steps.get? (stepNum.mod input.steps.length) with
        | .none => stepNum
        | .some step =>
            let nextNode := nextStep input.map currentNode step
            findEndSteps stopCondition input (stepNum + 1) nextNode

def findGhostSteps (stopCondition: String -> Bool) (input: Input) (startPositions: List String): Nat :=
  List.foldr Nat.lcm 1
    ∘ List.map (findEndSteps stopCondition input 0)
    $ startPositions

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day8-1" }
      Parser.input
  let result1 := findEndSteps (λ s => s == "ZZZ") parsed1 0 "AAA"
  IO.println s!"part1 {result1}"

  let result2 := findGhostSteps (λ s => s.endsWith "Z") parsed1 (findStartPositions ∘ Evie.HashMap.keys $ parsed1.map)
  IO.println s!"part2 {result2}"
