import Evie.FunctorOf
import Evie.List
import Evie.Monoid
import Evie.Nat
import Evie.Parser
import Lean.Parser

namespace AdventOfCode.Day3
open Evie

structure Coordinate where
  x : Nat
  y : Nat
deriving BEq

def Coordinate.move (coord: Coordinate) (dx: Int) (dy: Int) : Coordinate :=
  { x := (Int.ofNat coord.x + dx).toNat
  , y := (Int.ofNat coord.y + dy).toNat
  }

def Coordinate.range (y: Nat) (x1: Nat) (x2: Nat) : List Coordinate :=
  let go (x: Nat) : Coordinate := { x := x, y := y }
  go <$> Nat.range x1 x2

structure Number where
  value : Nat
  coordinates : List Coordinate

structure Symbol where
  symbol : Char
  coordinate : Coordinate

def Symbol.isGear (s: Symbol) : Bool :=
  s.symbol == '*'

structure Input where
  numbers : List Number
  symbols : List Symbol

def Input.Monoid.Instance: Monoid.Monoid :=
  { Carrier := Input
  , unit := { numbers := [], symbols := [] }
  , op := fun i1 i2 =>
            { numbers := i1.numbers.append i2.numbers
            , symbols := i1.symbols.append i2.symbols
            }
  }

namespace Parser
open Lean

def mkInput
  (before: String.Iterator)
  (after: String.Iterator)
  (y: Nat)
  (inp: Nat ⊕ Char)
  : Input
:=
  match inp with
    | .inl nat =>
        let num :=
          { value := nat
          , coordinates := Coordinate.range y before.pos.byteIdx after.pos.byteIdx
          }
        { numbers := [num], symbols := [] }
    | .inr chr =>
        let coord : Coordinate := { x := before.pos.byteIdx, y := y }
        let symbol : Symbol := { symbol := chr, coordinate := coord }
        { numbers := [], symbols := [symbol] }

def symbol (chr: Char): Bool :=
  not $ chr.isDigit || chr.isWhitespace || chr == '.'

def line (y: Nat) : Parsec Input := do
  _ <- Parsec.manyChars $ Parsec.pchar '.'
  let before <- Parser.iterator
  let numberOrSymbol <- Parser.either Parser.nat (Parsec.satisfy symbol)
  let after <- Parser.iterator
  pure $ mkInput before after y numberOrSymbol

def lines (xs: List String): Except String Input := do
  let go (xs: List Input) (zip: Nat × String) : Except String (List Input) := do
    let next <- Parsec.run (Parser.many $ line zip.fst) zip.snd
    pure $ xs.append next

  let zip := List.zip (Nat.range 1 (xs.length + 1)) xs

  Input.Monoid.Instance.fold <$> zip.foldlM go []

end Parser

def adjacent (coords: Coordinate × Coordinate): Bool :=
  let c1 := coords.fst
  let c2 := coords.snd

  if c1.move      (-1) (-1) == c2 then true -- SW
  else if c1.move (-1)   0  == c2 then true -- W
  else if c1.move (-1)   1  == c2 then true -- NW
  else if c1.move   0  (-1) == c2 then true -- S
  else if c1.move   0    1  == c2 then true -- N
  else if c1.move   1  (-1) == c2 then true -- SE
  else if c1.move   1    0  == c2 then true -- E
  else if c1.move   1    1  == c2 then true -- NE
  else false

def hasAdjacentSymbol (symbols: List Symbol) (number: Number): Bool :=
  let carthesian := List.product (symbols.map Symbol.coordinate) number.coordinates
  carthesian.any adjacent

def solve1 (input: Input): Nat :=
  Monoid.Nat.Sum.Instance.fold
     ∘ List.map Number.value
     $ input.numbers.filter (hasAdjacentSymbol input.symbols)

def solve2 (input: Input): Nat :=
  let multiply: List Nat -> Nat
    | [m, n] => m * n
    | _ => 0

  let neighbors (s: Symbol): List Number :=
    input.numbers.filter
      (fun num =>
        List.elem true
          ∘ List.map adjacent
          ∘ List.map (fun c => (c, s.coordinate))
          $ num.coordinates
      )

  Monoid.Nat.Sum.Instance.fold
    ∘ List.map (multiply ∘ List.map Number.value ∘ neighbors)
    ∘ List.filter Symbol.isGear
    $ input.symbols

def main: IO Unit := do
  let f <- IO.FS.lines { toString := "./data/day3-1" }

  let parsed1 <- IO.ofExcept $ Parser.lines f.toList
  IO.println s!"part1: {solve1 parsed1}"

  IO.println s!"part2: {solve2 parsed1}"
