import Evie.HashMap
import Evie.Monoid
import Evie.Nat
import Evie.Parser
import Evie.Prelude
import Lean.Parser

open Evie.Prelude

namespace AdventOfCode.Day4
open Evie

structure Card where
  id: Nat
  winning: List Nat
  actual: List Nat

instance: ToString Card where
  toString card := s!"Card {card.id}: {card.winning} | {card.actual}"

namespace Parser
open Lean

def line: Parsec Card := do
  Parsec.skipString "Card"
  Parsec.ws
  let id <- Parser.nat
  Parsec.skipChar ':'

  let winning <- Parser.many1 $ Parsec.ws *> Parser.nat
  Parsec.skipString " |"

  let actual <- Parser.many1 $ Parsec.ws *> Parser.nat
  Parser.parseOptionalChar '\n'

  pure
    { id := id
    , winning := winning
    , actual := actual
    }

def parse : Parsec (List Card) := Parser.many1 line

end Parser

def getWinners (card: Card): List Nat := card.actual.filter card.winning.elem

def solve1: List Card -> Nat :=
  Monoid.Nat.Sum.Instance.fold
    ∘ List.map ((2 ^ .) ∘ (. - 1))
    ∘ List.filter (. > 0)
    ∘ List.map (List.length ∘ getWinners)

def updateCardWinner (currentCards: Nat) (cardId: Nat): StateM (Lean.HashMap Nat Nat) Unit :=
  StateT.modify'
     ∘ Evie.HashMap.modify cardId
     $ Option.maybe (. + currentCards) (currentCards + 1)

def step2 (card: Card): StateM (Lean.HashMap Nat Nat) Nat := do
  let winners := List.length ∘ getWinners $ card
  let state <- StateT.get
  let currentCards := Option.maybe id 1 $ state.find? card.id
  let generatedCards := Nat.range (card.id + 1) (card.id + 1 + winners)

  generatedCards.forM $ updateCardWinner currentCards

  pure currentCards

def solve2: List Card -> StateM (Lean.HashMap Nat Nat) Nat :=
  Monoid.Nat.Sum.Instance.foldMapM step2

def main: IO Unit := do
  let parsed1 <- Evie.Parser.parseFile { toString := "./data/day4-1" } Parser.parse
  IO.println s!"part1: {solve1 parsed1}"

  let result2 := (solve2 parsed1).run Lean.HashMap.empty
  IO.println s!"part2: {result2.run.fst}"
