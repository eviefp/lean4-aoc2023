import Evie.HashMap
import Evie.List
import Evie.Monoid
import Evie.Nat
import Evie.Parser
import Evie.Prelude
import Lean.Parser

namespace AdventOfCode.Day5
open Evie
open Evie.Prelude

structure Range where
  start: Nat
  length: Nat
deriving BEq, Inhabited

instance: ToString Range where
  toString r := s!"({r.start}, {r.length})"

def Range.lt (r1: Range) (r2: Range): Bool :=
  if r1.start == r2.start
    then r1.length < r2.length
    else r1.start < r2.start

-- TODO: prove this terminates?
partial def Range.normalize: List Range -> List Range
  | []             => []
  | [r]            => [r]
  | r1 :: r2 :: rs =>

    if r1.length == 0
      then Range.normalize (r2 :: rs)

    else if r2.length == 0
      then Range.normalize (r1 :: rs)

    -- These are sorted, so if they have the same start, r2.length < r2.length
    else if r1.start == r2.start
      then Range.normalize (r2 :: rs)

    -- Otherwise, if r2 starts after r1 but it doesn't go over its edge
    else if r1.start + r1.length >= r2.start + r2.length
      then Range.normalize (r1 :: rs)

    -- Otherwise, if r2 starts within r1 but goes over its edge
    else if r2.start <= r1.start + r1.length
      then Range.normalize $ { start := r1.start, length := r2.start - r1.start + r2.length } :: rs
    else r1 :: Range.normalize (r2 :: rs)

structure Process where
  input: Nat
  output: Nat
  length: Nat
deriving Inhabited

instance: ToString Process where
  toString p := s!"({p.input}, {p.output}, {p.length})"

def Process.lt (p1: Process) (p2: Process): Bool := p1.input < p2.input

structure Map where
  processes: Array Process
deriving Inhabited

instance: ToString Map where
  toString :=
    String.join
      ∘ List.intersperse "\n"
      ∘ flip List.concat "\n"
      ∘ List.map toString
      ∘ Array.toList
      ∘ Map.processes

def Map.new: Array Process -> Map :=
  Map.mk ∘ flip Array.qsort Process.lt


/--
10,7 / 0,7
r:            |-------|
p: |-------|

10,7 / 4,7
r:     |-------|
p: |-------|

0,7 / 0,7
r: |-------|
p: |-------|

0,7 / 0,10
r: |-------|
p: |----------|

0,7 / 2,2
r: |-------|
p:   |--|

0,7 / 2,5
r: |-------|
p:   |-----|

0,7 / 2,7
r: |-------|
p:   |-------|

0,7 / 10, 2
r: |-------|
p:            |--|

TODO: prove this terminates
-/
partial def Map.processWorker: List Process -> List Range -> List Range
  | [], ranges       => ranges
  | _ , []           => []
  | p :: ps, r :: rs => -- 0 x y
      let rangeEnd := r.start + r.length -- 46
      let processEnd := p.input + p.length -- 70

      -- debugging
      if r.length == 0
        then Map.processWorker (p :: ps) rs

      -- Current range is after process, go to the next process
      else if r.start >= processEnd
        then Map.processWorker ps (r :: rs)

      -- Current process is after range, go to the next range
      else if p.input > rangeEnd
        then r :: Map.processWorker (p :: ps) rs

      -- Current range intersects with process
      else if r.start < processEnd && rangeEnd > p.input
        then
          let remainder :=
            { start := processEnd
            , length := rangeEnd - processEnd
            }
          let processedStart := max p.input r.start
          let processed :=
            { start := (processedStart + p.output) - p.input
            , length := (min rangeEnd processEnd) - processedStart
            }
          if remainder.length == 0
            then processed :: Map.processWorker (p :: ps) rs
            else processed :: Map.processWorker (p :: ps) (remainder :: rs)
      else panic! s!"{r} {p}"

def Map.process (acc: Array Range) (ps: List Process): Array Range :=
  flip Array.qsort Range.lt
    ∘ List.toArray
    ∘ Map.processWorker ps
    ∘ Range.normalize -- this is not actually needed, should I remove?
    ∘ Array.toList
    $ acc

structure Input where
  seeds: Array Range
  maps: Array Map
deriving Inhabited

instance: ToString Input where
  toString input :=
    String.intercalate "\n"
      ∘ flip List.concat (toString input.seeds)
      ∘ List.map toString
      ∘ Array.toList
      $ input.maps

def Input.new (seeds: Array Range) (maps: Array Map): Input where
  seeds := Array.qsort seeds Range.lt
  maps := maps

def Input.solve (input: Input): Nat :=
  Option.get!
    ∘ Monoid.Nat.Min.Instance.fold
    ∘ List.map (some ∘ Range.start)
    ∘ Array.toList
    ∘ List.foldl Map.process input.seeds
    ∘ Array.toList
    ∘ Array.map (Array.toList ∘ Map.processes)
    $ input.maps

namespace Parser
open Lean

def simpleSeed: Parsec Range := do
  let start <- Parsec.skipChar ' ' *> Parser.nat
  pure
    { start := start
    , length := 1
    }

def seed1: Parsec (Array Range) := do
  Parsec.skipString "seeds:"
  Parsec.many1 simpleSeed

def rangeSeed: Parsec Range := do
  let start <- Parsec.skipChar ' ' *> Parser.nat
  let length <- Parsec.skipChar ' ' *> Parser.nat
  pure
    { start := start
    , length := length
    }

def seed2: Parsec (Array Range) := do
  Parsec.skipString "seeds:"
  Parsec.many1 rangeSeed

def process: Parsec Process := do
  let output <- Parser.nat <* Parsec.skipChar ' '
  let input  <- Parser.nat <* Parsec.skipChar ' '
  let length <- Parser.nat
  Parsec.ws
  pure
    { input  := input
    , output := output
    , length := length
    }

def map: Parsec Map := do
  Parsec.ws
  _ <- Parsec.many1Chars ∘ Parsec.satisfy $ not ∘ (. == ':')
  Parsec.skipChar ':'
  Parsec.ws

  let processes <- Parsec.many1 process

  pure $ Map.new processes

def input (parseSeed: Parsec (Array Range)): Parsec Input := do
  let seeds <- parseSeed
  Parsec.ws

  let maps <- Parsec.many1 map
  pure $ Input.new seeds maps

end Parser

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day5-1" }
      $ Parser.input Parser.seed1
  IO.println s!"part1 {Input.solve parsed1}"

  let parsed2 <-
    Parser.parseFile
      { toString := "./data/day5-1" }
      $ Parser.input Parser.seed2
  IO.println s!"part2 {Input.solve parsed2}"
