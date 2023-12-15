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

namespace AdventOfCode.Day10
open Evie
open Evie.Prelude

inductive Pipe where
  | NS
  | WE
  | NE
  | NW
  | SW
  | SE
  | Ground
  | Start
deriving BEq

instance: Inhabited Pipe where
  default := Pipe.Ground

def Pipe.fromChar: Char -> Option Pipe
  | '|' => .some .NS
  | '-' => .some .WE
  | 'L' => .some .NE
  | 'J' => .some .NW
  | '7' => .some .SW
  | 'F' => .some .SE
  | '.' => .some .Ground
  | 'S' => .some .Start
  | _   => .none

def Pipe.fromChar! (c: Char): Pipe :=
  match Pipe.fromChar c with
    | .some p => p
    | .none   => panic! "Pipe.fromChar!: unexpected character {c.quote}"

def Pipe.toChar: Pipe -> Char
  | .NS     => '|'
  | .WE     => '-'
  | .NE     => '⌞'
  | .NW     => '⌟'
  | .SW     => '⌝'
  | .SE     => '⌜'
  | .Ground => ','
  | .Start  => '#'

def Pipe.fromSouth: Pipe -> Bool
  | .NS | .SW | .SE => true
  | _               => false

def Pipe.fromNorth: Pipe -> Bool
  | .NS | .NW | .NE => true
  | _               => false

def Pipe.fromEast: Pipe -> Bool
  | .WE | .NE | .SE => true
  | _               => false

def Pipe.fromWest: Pipe -> Bool
  | .WE | .NW | .SW => true
  | _               => false

instance: ToString Pipe where
  toString := Char.toString ∘ Pipe.toChar

structure Grid (x: Nat) (y: Nat)  where
  pipes: Vector (Vector Pipe x) y

instance: ToString (Grid x y) where
  toString :=
    String.intercalate "\n"
      ∘ Vector.toList
      ∘ Vector.map (Vector.asString ∘ Vector.map Pipe.toChar)
      ∘ Grid.pipes

def Grid.empty (x: Nat) (y: Nat): Grid x y :=
  Grid.mk
    $ Vector.replicate y (Vector.replicate x Pipe.Ground)

def Grid.fromInput (input: List String): Grid m n -> Grid m n :=
  let pipeAt (x: Nat) (y: Nat): Pipe :=
    Option.maybe
      (λ str => Pipe.fromChar! ∘ str.get ∘ String.Pos.mk $ x)
      Pipe.Ground
      $ input.get? y
  Grid.mk
    ∘ Vector.mapWithIdx
        (λ y lv => lv.mapWithIdx
            (λ x _ => pipeAt x y))
    ∘ Grid.pipes

structure Position (maxX: Nat) (maxY: Nat) where
  x: Fin maxX
  y: Fin maxY
deriving BEq

def Position.up (pos: Position x₁ y₁): Option (Position x₁ y₁) :=
  if h: pos.y.val ≠ 0
    then
      some
        { x := pos.x
        , y := ⟨Nat.pred pos.y.val, trans (Nat.pred_lt h) pos.y.isLt⟩
        }
    else none

def Position.down (pos: Position x₁ y₁): Option (Position x₁ y₁) :=
  if h: pos.y.val + 1 < y₁
    then
      some
        { x := pos.x
        , y := ⟨pos.y.val + 1, h⟩
        }
    else none

def Position.left (pos: Position x₁ y₁): Option (Position x₁ y₁) :=
  if h: pos.x.val ≠ 0
    then
      some
        { x := ⟨Nat.pred pos.x.val, trans (Nat.pred_lt h) pos.x.isLt⟩
        , y := pos.y
        }
    else none

def Position.right (pos: Position x₁ y₁): Option (Position x₁ y₁) :=
  if h: pos.x.val + 1 < x₁
    then
      some
        { x := ⟨pos.x.val + 1, h⟩
        , y := pos.y
        }
    else none

def Position.neighbors (pos: Position m n): List (Position m n) :=
  List.catMaybes
    [ pos.up
    , pos.down
    , pos.left
    , pos.right
    ]

def Grid.get (grid: Grid x y) (pos: Position x y): Pipe :=
  (grid.pipes.get pos.y).get pos.x

def Grid.update (grid: Grid x y) (pos: Position x y) (p: Pipe): Grid x y :=
  let prev    := grid.pipes.get pos.y
  let updated := Vector.setAt p pos.x prev
  Grid.mk $ grid.pipes.setAt updated pos.y

def Grid.positions (_grid: Grid x y) : List (Position x y) :=
  let x_range := Nat.range 0 x
  let y_range := Nat.range 0 y

  y_range.foldl
    (λ ll y₁ =>
      x_range.foldl
        (λ l x₁ =>
          if hx: x₁ < x
            then
              if hy: y₁ < y
                then Position.mk ⟨x₁, hx⟩ ⟨y₁, hy⟩ :: l
                else l
            else l
        ) ll
      ) []

instance: ToString (Position x y) where
  toString p := s!"[{p.x}, {p.y}]"

structure CurrentPipes (maxX: Nat) (maxY: Nat) where
  first: Position maxX maxY
  first_prev: Position maxX maxY
  second: Position maxX maxY
  second_prev: Position maxX maxY

instance: ToString (CurrentPipes x y) where
  toString cp := s!"({cp.first}, {cp.second}) // ({cp.first_prev}, {cp.second_prev})"

def findStart (grid: Grid x y): Option (Position x y) := do
  let y <- grid.pipes.findPosition (λ line =>
                (line.findPosition (BEq.beq Pipe.Start)).toBool)
  let line := grid.pipes.get y
  let x <- line.findPosition (BEq.beq Pipe.Start)
  pure { x := x, y := y }

def findStartPositions (grid: Grid x y): Option (CurrentPipes x y × Grid x y) := do
  let fromSouth := λ x => (x, Pipe.fromSouth ∘ grid.get $ x)
  let fromNorth := λ x => (x, Pipe.fromNorth ∘ grid.get $ x)
  let fromEast := λ x => (x, Pipe.fromEast ∘ grid.get $ x)
  let fromWest := λ x => (x, Pipe.fromWest ∘ grid.get $ x)
  let startPos <- findStart grid
  let up    := startPos.up
  let down  := startPos.down
  let left  := startPos.left
  let right := startPos.right

  match fromSouth <$> up, fromNorth <$> down, fromEast <$> left, fromWest <$> right with
    | some (up', true), some (down', true), _, _ =>
        .some ( { first := up', second := down', first_prev := startPos, second_prev := startPos }
              , grid.update startPos .NS
              )
    | some (up', true), _, some (east', true), _ =>
        .some ( { first := up', second := east', first_prev := startPos, second_prev := startPos }
              , grid.update startPos .NE
              )
    | some (up', true), _, _, some (west', true) =>
        .some ( { first := up', second := west', first_prev := startPos, second_prev := startPos }
              , grid.update startPos .NW
              )
    | _, some (down', true), some (east', true), _ =>
        .some ( { first := down', second := east', first_prev := startPos, second_prev := startPos }
              , grid.update startPos .SE
              )
    | _, some (down', true), _, some (west', true) =>
        .some ( { first := down', second := west', first_prev := startPos, second_prev := startPos }
              , grid.update startPos .SW
              )
    | _, _, some (east', true), some (west', true) =>
        .some ( { first := east', second := west', first_prev := startPos, second_prev := startPos }
              , grid.update startPos .WE
              )
    | _, _, _, _ => none

def nextPosition (grid: Grid x y) (prev: Position x y) (current: Position x y): Option (Position x y) :=
  let ifNotPrev: Option (Position x y) -> Option (Position x y)
    | .some p =>
      if p == prev then none
      else some p
    | none => none
  let currentStep := grid.get current
  match currentStep with
    | Pipe.WE =>
      let left  := ifNotPrev current.left
      let right := ifNotPrev current.right
      left <|> right
    | Pipe.NS =>
      let up  := ifNotPrev current.up
      let down := ifNotPrev current.down
      up <|> down
    | Pipe.NE =>
      let up  := ifNotPrev current.up
      let right := ifNotPrev current.right
      up <|> right
    | Pipe.NW =>
      let up := ifNotPrev current.up
      let left := ifNotPrev current.left
      up <|> left
    | Pipe.SW =>
      let down := ifNotPrev current.down
      let left  := ifNotPrev current.left
      down <|> left
    | Pipe.SE =>
      let down := ifNotPrev current.down
      let right := ifNotPrev current.right
      down <|> right
    | _  => none

partial def step (grid: Grid x y) (pos: CurrentPipes x y) (steps: Nat): Nat :=
  if pos.first == pos.second
    then steps
  else
    let first := nextPosition grid pos.first_prev pos.first
    let second := nextPosition grid pos.second_prev pos.second
    match first, second with
      | .some f, .some s =>
        step grid { first := f, second := s, first_prev := pos.first, second_prev := pos.second } (steps + 1)
      | _, _ => 0

def solveImpl (grid: Grid x y): Nat :=
  let startPositions := findStartPositions grid
  match startPositions with
    | none => 0
    | some (pos, grid') => step grid' pos 1

def solve (xs: List String): Nat :=
  let y := xs.length
  if h: xs ≠ []
    then
      let x := (xs.head h).length
      if x == 0
        then 0
        else
          solveImpl $ Grid.fromInput xs $ Grid.empty x y
     else 0

partial def step2 (grid: Grid x y) (pos: CurrentPipes x y) (l: List (Position x y)): List (Position x y) :=
  if pos.first == pos.second
    then l
  else
    let first := nextPosition grid pos.first_prev pos.first
    let second := nextPosition grid pos.second_prev pos.second
    match first, second with
      | .some f, .some s =>
        step2 grid { first := f, second := s, first_prev := pos.first, second_prev := pos.second } (f :: s :: l)
      | _, _ => l

def solveImpl2 (grid: Grid x y): List (Position x y) :=
  let startPositions := findStartPositions grid
  match startPositions with
    | none => []
    | some (pos, grid') =>
      step2 grid' pos [pos.first_prev, pos.first, pos.second]

mutual

partial def traversePipeLeft (grid: Grid x y) (loop: List (Position x y)) (mode: Pipe) (pos: Position x y): Nat :=
  match pos.left with
    | .none    => panic! s!"traversePipeLeft: unexpected end of grid after {pos} for {mode}"
    | .some p' =>
      match mode, grid.get p' with
        | _  , .WE => traversePipeLeft grid loop mode p' -- navigate pipe
        | .NW, .SE => 1 + countLeftToZero grid loop p'   -- we are here -> F--J
        | .SW, .NE => 1 + countLeftToZero grid loop p'   -- we are here -> L--7
        | _  , _   => countLeftToZero grid loop p'

partial def countLeftToZero (grid: Grid x y) (loop: List (Position x y)) (pos: Position x y): Nat :=
  match pos.left with
    | .some p' =>
      if loop.elem p'
        then
          match grid.get p' with
            | .NS => 1 + countLeftToZero grid loop p'
            | .NW => traversePipeLeft grid loop .NW p'
            | .SW => traversePipeLeft grid loop .SW p'
            | _   => 0
        else countLeftToZero grid loop p'
    | .none => 0

end

def countIfInsideLoop
  (grid: Grid x y)
  (loop: List (Position x y))
  (acc: Nat)
  (pos: Position x y):
  Nat :=
  if loop.elem pos
    then acc
    else
      let leftEdges := countLeftToZero grid loop pos
      if (Nat.mod leftEdges 2) == 1
        then acc + 1
        else acc

def solve2 (xs: List String): Nat :=
  let y := xs.length
  if h: xs ≠ []
    then
      let x := (xs.head h).length
      if x == 0
        then 0
        else
          let grid := Grid.fromInput xs $ Grid.empty x y
          let loop := solveImpl2 grid
          List.foldl (countIfInsideLoop grid loop) 0 grid.positions
     else 0

namespace Sample

def sampleInput: List String :=
  [ "....."
  , ".S-7."
  , ".|.|."
  , ".L-J."
  , "....."
  ]

#eval solve sampleInput

#eval solve2 sampleInput

def sampleInput2: List String :=
  [ "..........."
  , ".S-------7."
  , ".|F-----7|!"
  , ".||.....||."
  , ".||.....||."
  , ".|L-7.F-J|."
  , ".|..|.|..|."
  , ".L--J.L--J."
  , "..........."
  ]

#eval solve2 sampleInput2

def sampleInput3: List String :=
  [ ".F----7F7F7F7F-7...."
  , ".|F--7||||||||FJ...."
  , ".||.FJ||||||||L7...."
  , "FJL7L7LJLJ||LJ.L-7.."
  , "L--J.L7...LJS7F-7L7."
  , "....F-J..F7FJ|L7L7L7"
  , "....L7.F7||L7|.L7L7|"
  , ".....|FJLJ|FJ|F7|.LJ"
  , "....FJL-7.||.||||..."
  , "....L---J.LJ.LJLJ..."
  ]

#eval solve2 sampleInput3

def sampleInput4: List String :=
  [ "FF7FSF7F7F7F7F7F---7"
  , "L|LJ||||||||||||F--J"
  , "FL-7LJLJ||||||LJL-77"
  , "F--JF--7||LJLJ7F7FJ-"
  , "L---JF-JLJ.||-FJLJJ7"
  , "|F|F-JF---7F7-L7L|7|"
  , "|FFJF7L7F-JF7|JL---7"
  , "7-L-JL7||F7|L7F-7F7|"
  , "L.L7LFJ|||||FJL7||LJ"
  , "L7JLJL-JLJLJL--JLJ.L"
  ]

#eval solve2 sampleInput4

end Sample

def main: IO Unit := do
  let lines <- IO.FS.lines { toString := "./data/day10-1" }
  IO.println s!"part1: {solve lines.toList}"

  IO.println s!"part2: {solve2 lines.toList}"
