import Evie.Monoid
import Evie.Parser
import Lean.Parser

namespace AdventOfCode.Day2
open Evie

structure CubeSample where
  blue : Nat
  green : Nat
  red : Nat

def CubeSample.Monoid : Monoid.Monoid :=
  { Carrier := CubeSample
  , unit := { blue := 0, green := 0, red := 0 }
  , op := fun c1 c2 =>
            { blue := max c1.blue c2.blue
            , green := max c1.green c2.green
            , red := max c1.red c2.red
            }
  }

structure Game where
  id : Nat
  sets : List CubeSample

namespace Parser
open Lean

def cubeSamplePart : Parsec CubeSample := do
  let number <- Parser.nat
  _ <- Parsec.pchar ' '
  let color <- Parsec.many1Chars Parsec.asciiLetter

  let isDone <- Parsec.peek?
  match isDone with
    | ',' => Parsec.pstring ", "
    | _   => pure ""

  let sample <- match color with
    | "blue" => pure $ CubeSample.mk number 0 0
    | "green" => pure $ CubeSample.mk 0 number 0
    | "red" => pure $ CubeSample.mk 0 0 number
    | color => Parsec.fail s!"unexpected color: {color}"

def cubeSample : Parsec CubeSample := do
  let samples <- Array.toList <$> Parsec.many1 cubeSamplePart

  let isDone <- Parsec.peek?
  match isDone with
    | ';' => Parsec.pstring "; "
    | _   => pure ""

  pure $ CubeSample.Monoid.fold samples

def game: Parsec Game := do
  Parsec.ws
  _ <- Parsec.pstring "Game "
  let gameId <- Parser.nat
  _ <- Parsec.pstring ": "

  let gameSets <- Array.toList <$> Parsec.many1 cubeSample

  pure { id := gameId, sets := gameSets }

def day1 : Parsec (List Game) := Array.toList <$> Parsec.many1 game

end Parser

def solve1 : List Game -> Nat :=
  let predicate (game: Game) : Bool :=
    let gameSample := CubeSample.Monoid.fold game.sets

    if      gameSample.blue  > 14 then false
    else if gameSample.green > 13 then false
    else if gameSample.red   > 12 then false

    else true

  Monoid.Nat.Sum.Instance.fold
     ∘ List.map Game.id
     ∘ List.filter predicate

def solve2 : List Game -> Nat :=
  let toPowerLevel : CubeSample -> Nat := fun cube => cube.blue * cube.green * cube.red

  Monoid.Nat.Sum.Instance.foldMap toPowerLevel
    ∘ List.map CubeSample.Monoid.fold
    ∘ List.map Game.sets

def main : IO Unit := do
  let parsed1 <- Evie.Parser.parseFile { toString := "./data/day2-1" } Parser.day1

  let result1 := solve1 parsed1
  IO.println s!"part1: {result1}"

  let result2 := solve2 parsed1
  IO.println s!"part2: {result2}"
