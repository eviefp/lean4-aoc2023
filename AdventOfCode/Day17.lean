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

namespace AdventOfCode.Day17
open Evie
open Evie.Prelude

inductive Direction where
  | NS
  | SN
  | EW
  | WE
deriving BEq, Hashable

instance: ToString Direction where
  toString
  | .NS => "NS"
  | .SN => "SN"
  | .EW => "EW"
  | .WE => "WE"

structure Pair (x y: Nat) where
  first: Grid.Position x y
  second: Grid.Position x y
  repeats: Nat
deriving BEq, Hashable

structure Path (x y: Nat) where
  heatLoss: Nat
  position: Grid.Position x y
  direction: Direction
  repeats: Nat
  history: Lean.HashMap (Pair x y) Nat

instance: ToString (Path x y) where
  toString p := s!"⟨{p.heatLoss}, {p.position}, {p.direction}, {p.repeats}⟩"

instance: BEq (Path x y) where
  beq p1 p2 :=
    p1.heatLoss == p2.heatLoss
    && p1.position == p2.position
    && p1.direction == p2.direction
    && p1.repeats == p2.repeats

def step: Grid x y Nat -> Grid.Position x y -> Path x y -> StateM (Lean.HashMap (Pair x y) Nat) (List (Path x y))
  | grid, target, path => if target == path.position then pure [] else do
    let directions :=
      List.catMaybes
      [ path.position.up    >>= go grid .SN path
      , path.position.down  >>= go grid .NS path
      , path.position.left  >>= go grid .EW path
      , path.position.right >>= go grid .WE path
      ]
    -- dbg_trace s!"step: {directions}"
    let hash <- StateT.get
    let result := directions.filter
      (λ p => match hash.find? (Pair.mk path.position p.position p.repeats) with
              | .none => path.history.toList.all (λ (k, v) => Option.maybe (λ cached => v <= cached) true $ hash.find? k)
              | .some cache => p.heatLoss < cache)
    StateT.modify'
      (λ hash =>
        List.foldl
          (λ hm p =>
            HashMap.modify
              (Pair.mk path.position p.position p.repeats)
              (Option.maybe (Nat.min p.heatLoss) p.heatLoss)
              hm
          )
          hash
          directions
      )
    pure result
  where
    go: Grid x y Nat -> Direction -> Path x y -> Grid.Position x y -> Option (Path x y)
      | grid, now, ⟨heatLoss, prevPosition, prevDirection, rep, hist ⟩, pos =>
        let cost := grid.get pos
        if now == prevDirection
        then if rep == 3
         then .none
         else .some ⟨heatLoss + cost, pos, prevDirection, rep + 1, hist.insert ⟨prevPosition, pos, rep + 1 ⟩ (heatLoss + cost) ⟩
        else
          match prevDirection, now with -- cannot turn 180 degrees
            | .NS, .SN => .none
            | .SN, .NS => .none
            | .WE, .EW => .none
            | .EW, .WE => .none
            | _  , _   => .some ⟨heatLoss + cost, pos, now, 1, hist.insert ⟨prevPosition, pos, 1⟩ (heatLoss + cost) ⟩

partial def findShortestPath:
  Grid x y Nat ->
  Grid.Position x y ->
  List (Path x y) ->
  StateM (Lean.HashMap (Pair x y) Nat) (List (Path x y))
  | _   , _, []      => pure []
  | grid, target, p :: ps => do
    -- dbg_trace s!"findShortestPath: {p}"
    let next <- step grid target p
    -- findShortestPath grid target (List.append next ps) -- (shortest :: remainder)
    let remainingPaths := List.append next ps
    match remainingPaths.head? with
      | .none => pure []
      | .some h =>
        let shortest := List.foldl (λ min curr => if curr.heatLoss < min.heatLoss then curr else min) h remainingPaths
        if shortest.position == target
          then pure []
          else
            let remainder := remainingPaths.removeAll [shortest]
            findShortestPath grid target (shortest :: remainder)

def solve1 (input: List (List Nat)): Nat :=
  let y := input.length
  match input with
  | [] => 0
  | i :: _ =>
    let x := i.length
    let grid := Grid.fromList x y 0 input
    let startPos := Grid.Position.mkPosition x y 0 0
    let endPos   := Grid.Position.mkPosition x y (x-1) (y-1)
    match startPos, endPos with
    | .some start, .some endPos =>
      match start.down, start.right with
      | .some down, .some right =>
        let paths: List (Path x y) := [ ⟨grid.get down, down, .NS, 1, Lean.HashMap.empty ⟩, ⟨grid.get right, right, .WE, 1, Lean.HashMap.empty ⟩ ]
        let init := HashMap.fromList
          [ (⟨start, right, 1⟩, (grid.get right))
          , (⟨start, down,  1⟩, (grid.get down))
          ]
        let hm := (findShortestPath grid endPos paths).run init
        List.foldl (λ acc (pos, val) => if pos.second == endPos then Nat.min acc val else acc) 9999999999 hm.snd.toList
      | _, _ => 0
    | _, _ => 0

namespace Part2

def step: Grid x y Nat -> Grid.Position x y -> Path x y -> StateM (Lean.HashMap (Pair x y) Nat) (List (Path x y))
  | grid, target, path => if target == path.position then pure [] else do
    let directions :=
      List.catMaybes
      [ path.position.up    >>= go grid .SN path
      , path.position.down  >>= go grid .NS path
      , path.position.left  >>= go grid .EW path
      , path.position.right >>= go grid .WE path
      ]
    -- dbg_trace s!"step: {directions}"
    let hash <- StateT.get
    let result := directions.filter
      (λ p => match hash.find? (Pair.mk path.position p.position p.repeats) with
              | .none => path.history.toList.all (λ (k, v) => Option.maybe (λ cached => v <= cached) true $ hash.find? k)
              | .some cache => p.heatLoss < cache)
    StateT.modify'
      (λ hash =>
        List.foldl
          (λ hm p =>
            HashMap.modify
              (Pair.mk path.position p.position p.repeats)
              (Option.maybe (Nat.min p.heatLoss) p.heatLoss)
              hm
          )
          hash
          directions
      )
    pure result
  where
    go: Grid x y Nat -> Direction -> Path x y -> Grid.Position x y -> Option (Path x y)
      | grid, now, ⟨heatLoss, prevPosition, prevDirection, rep, hist ⟩, pos =>
        let cost := grid.get pos
        if now == prevDirection
        then if rep == 10
         then .none
         else .some ⟨heatLoss + cost, pos, prevDirection, rep + 1, hist.insert ⟨prevPosition, pos, rep + 1 ⟩ (heatLoss + cost) ⟩
        else if rep < 4
        then none
        else
          match prevDirection, now with -- cannot turn 180 degrees
            | .NS, .SN => .none
            | .SN, .NS => .none
            | .WE, .EW => .none
            | .EW, .WE => .none
            | _  , _   => .some ⟨heatLoss + cost, pos, now, 1, hist.insert ⟨prevPosition, pos, 1⟩ (heatLoss + cost) ⟩

partial def findShortestPath:
  Grid x y Nat ->
  Grid.Position x y ->
  List (Path x y) ->
  StateM (Lean.HashMap (Pair x y) Nat) (List (Path x y))
  | _   , _, []      => pure []
  | grid, target, p :: ps => do
    -- dbg_trace s!"findShortestPath: {p}"
    let next <- step grid target p
    -- findShortestPath grid target (List.append next ps) -- (shortest :: remainder)
    let remainingPaths := List.append next ps
    match remainingPaths.head? with
      | .none => pure []
      | .some h =>
        let shortest := List.foldl (λ min curr => if curr.heatLoss < min.heatLoss then curr else min) h remainingPaths
        if shortest.position == target && shortest.repeats > 3
          then pure []
          else
            let remainder := remainingPaths.removeAll [shortest]
            findShortestPath grid target (shortest :: remainder)

def solve (input: List (List Nat)): Nat :=
  let y := input.length
  match input with
  | [] => 0
  | i :: _ =>
    let x := i.length
    let grid := Grid.fromList x y 0 input
    let startPos := Grid.Position.mkPosition x y 0 0
    let endPos   := Grid.Position.mkPosition x y (x-1) (y-1)
    match startPos, endPos with
    | .some start, .some endPos =>
      match start.down, start.right with
      | .some down, .some right =>
        let paths: List (Path x y) := [ ⟨grid.get down, down, .NS, 1, Lean.HashMap.empty ⟩, ⟨grid.get right, right, .WE, 1, Lean.HashMap.empty ⟩ ]
        let init := HashMap.fromList
          [ (⟨start, right, 1⟩, (grid.get right))
          , (⟨start, down,  1⟩, (grid.get down))
          ]
        let hm := (findShortestPath grid endPos paths).run init
        List.foldl (λ acc (pos, val) => if pos.second == endPos && pos.repeats > 3 then Nat.min acc val else acc) 9999999999 hm.snd.toList
      | _, _ => 0
    | _, _ => 0

end Part2

namespace Parser
open Lean

def line: Parsec (List Nat) :=
  Parser.many1 Parser.digit

def input: List String -> List (List Nat) :=
  List.map (Option.maybe id [] ∘ Except.toOption ∘ line.run)

end Parser

namespace Sample

def sampleInput: List String :=
  [ "2413432311323"
  , "3215453535623"
  , "3255245654254"
  , "3446585845452"
  , "4546657867536"
  , "1438598798454"
  , "4457876987766"
  , "3637877979653"
  , "4654967986887"
  , "4564679986453"
  , "1224686865563"
  , "2546548887735"
  , "4322674655533"
  ]

def input: List (List Nat) := Parser.input sampleInput

def sampleInput2: List String :=
  [ "911199"
  , "999199"
  , "991199"
  , "991199"
  , "999199"
  , "999111"
  ]

def input2: List (List Nat) := Parser.input sampleInput2



end Sample

def main: IO Unit := do
  let lines <- (Parser.input ∘ Array.toList) <$> IO.FS.lines { toString := "./data/day17-1" }
  IO.println s!"{solve1 lines}"
  IO.println s!"{Part2.solve lines}"
