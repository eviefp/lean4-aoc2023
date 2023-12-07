import Evie.HashMap
import Evie.Monoid
import Evie.Parser
import Evie.Prelude
import Lean.Data.HashMap
import Lean.Parser

namespace AdventOfCode.Day7
open Evie
open Evie.Prelude

structure Game where
  cards: List Nat
  bid: Nat
-- instance: Inhabited Game where
--   default := { cards := [], bid := 0 }

namespace Card

def toString: Nat -> String
| 10 => "T"
| 11 => "J"
| 12 => "Q"
| 13 => "K"
| 14 => "A"
| n  => ToString.toString n

def fiveOfAKind:  Nat := 6
def fourOfAKind:  Nat := 5
def fullHouse:    Nat := 4
def threeOfAKind: Nat := 3
def twoPair:      Nat := 2
def pair:         Nat := 1
def highCard:     Nat := 0
def jack:         Nat := 11
def joker:        Nat := 1

def calculatePower (cards: List Nat): Nat :=
  let mkCardNumbers (n: Nat): Lean.HashMap Nat Nat -> Lean.HashMap Nat Nat :=
      Evie.HashMap.modify n (Option.maybe Nat.succ 1)
  let typeHash := cards.foldl (flip mkCardNumbers) Lean.HashMap.empty

  let jokers := typeHash.find? 1

  let orderedCardCount := flip Array.qsort (fun (m, _) (n, _) => m > n)
    ∘ Array.map (λ (card, count) => (count, card))
    $ typeHash.toArray

  match orderedCardCount.toList with
    -- number of cards          result         if we have joker     if we don't
    | (5, _) ::           [] => fiveOfAKind
    | (4, _) ::           _  => Option.maybe (λ _ => fiveOfAKind)  fourOfAKind  jokers
    | (3, _) :: (2, _) :: [] => Option.maybe (λ _ => fiveOfAKind)  fullHouse    jokers
    | (3, _) ::           _  => Option.maybe (λ _ => fourOfAKind)  threeOfAKind jokers
    | (2, _) :: (2, _) :: _  => Option.maybe (Nat.add 3)           twoPair      jokers -- one joker makes fullHouse, two make fourOfAKind
    | (2, _) :: (1, _) :: _  => Option.maybe (λ _ => threeOfAKind) pair         jokers
    | (1, _) ::           _  => Option.maybe (λ _ => pair)         highCard     jokers
    |                     _  => panic! "power: bad calculation"

-- Could simplify this if we replaced all J with 0 to signify their low power
def compare (c1: List Nat) (c2: List Nat): Bool :=
  let findFirstSmaller: Option Bool -> Nat × Nat -> Option Bool
    | some res, _=> res
    | none, (n1, n2) =>
            if n1 == n2
            then none
            else some $ n1 < n2

  let power1 := calculatePower c1
  let power2 := calculatePower c2

  if power1 == power2
    then
      Option.maybe id true
        ∘ List.foldl findFirstSmaller none
        $ List.zip c1 c2
    else power1 < power2

end Card

instance: ToString Game where
  toString g := s!"{String.join (g.cards.map Card.toString)}, {g.bid}";

namespace Parser
open Lean

def card (parseJ: Nat): Char -> List Nat -> List Nat
  | 'T', rest => 10                :: rest
  | 'J', rest => parseJ             :: rest
  | 'Q', rest => 12                :: rest
  | 'K', rest => 13                :: rest
  | 'A', rest => 14                :: rest
  | d  , rest => d.toString.toNat! :: rest

def cards (parseJ: Nat): Parsec (List Nat) := do
  Parsec.ws
  let str <- Parsec.many1Chars ∘ Parsec.satisfy $ not ∘ (. == ' ')
  pure $ str.foldr (card parseJ) []

def game (parseJ: Nat): Parsec Game := do
  Parsec.ws
  let c <- cards parseJ
  Parsec.skipChar ' '
  let bid <- Parser.nat
  pure $ { cards := c, bid := bid }

def input: Nat -> Parsec (List Game) :=
  Parser.many1 ∘ game

end Parser

def solve: List Game -> Nat :=
  Monoid.Nat.Sum.Instance.foldMap (λ (i, g) => g.bid * i.succ)
    ∘ List.enum
    ∘ Array.toList
    ∘ flip Array.qsort (λ g1 g2 => Card.compare g1.cards g2.cards)
    ∘ List.toArray

def sampleInput1: String :=
  String.intercalate "\n"
    [ "32T3K 765"
    , "T55J5 684"
    , "KK677 28"
    , "KTJJT 220"
    , "QQQJA 483"
    ]

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day7-1" }
      (Parser.input Card.jack)
  IO.println s!"part1 {solve parsed1}"

  let parsed2 <-
    Parser.parseFile
      { toString := "./data/day7-1" }
      (Parser.input Card.joker)
  IO.println s!"part2 {solve parsed2}"
