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

namespace AdventOfCode.Day11
open Evie
open Evie.Prelude

inductive Dot where
  | Galaxy
  | Space
deriving BEq

instance: Inhabited Dot where
  default := Dot.Space

def Dot.fromChar: Char -> Option Dot
  | '#' => .some .Galaxy
  | '.' => .some .Space
  | _   => .none

def Dot.fromChar! (c: Char): Dot :=
  match Dot.fromChar c with
    | .some p => p
    | .none   => panic! "Dot.fromChar!: unexpected character {c.quote}"

def Dot.toChar: Dot -> Char
  | .Galaxy => '#'
  | .Space  => '.'

instance: ToString Dot where
  toString := Char.toString ∘ Dot.toChar

structure Grid (x: Nat) (y: Nat)  where
  dots: Vector (Vector Dot x) y

instance: ToString (Grid x y) where
  toString :=
    String.intercalate "\n"
      ∘ Vector.toList
      ∘ Vector.map (Vector.asString ∘ Vector.map Dot.toChar)
      ∘ Grid.dots

def Grid.empty (x: Nat) (y: Nat): Grid x y :=
  Grid.mk
    $ Vector.replicate y (Vector.replicate x Dot.Space)

def Grid.fromInput (input: List String): Grid m n -> Grid m n :=
  let pipeAt (x: Nat) (y: Nat): Dot :=
    Option.maybe
      (λ str => Dot.fromChar! ∘ str.get ∘ String.Pos.mk $ x)
      Dot.Space
      $ input.get? y
  Grid.mk
    ∘ Vector.mapWithIdx
        (λ y lv => lv.mapWithIdx
            (λ x _ => pipeAt x y))
    ∘ Grid.dots

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

def Grid.get (grid: Grid x y) (pos: Position x y): Dot :=
  (grid.dots.get pos.y).get pos.x

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

def findGalaxies (grid: Grid x y): List (Position x y) :=
  List.filter
    (λ pos => grid.get pos == Dot.Galaxy)
    $ grid.positions

def findExpandedColumns (grid: Grid x y): List Nat :=
  Nat.fold
    (λ x'  l =>
      let expands :=
        Nat.fold
          (λ y' hasGalaxy =>
            if hx: x' < x
              then if hy: y' < y
                then match grid.get ⟨⟨x', hx⟩, ⟨y', hy⟩⟩ with
                       | Dot.Galaxy => true
                       | Dot.Space  => hasGalaxy
                else hasGalaxy
               else hasGalaxy
          )
          y
          false
        if expands then l else x' :: l
    )
    x
    []

-- TODO: should probably write these for Vector rather than using toList
def findExpandedLines (grid: Grid x y): List Nat :=
  grid.dots.enum.toList.foldr
    (λ (y, line) res => if line.toList.all (BEq.beq Dot.Space) then y :: res else res) []


def findPath (expansionFactor: Nat) (columns: List Nat) (lines: List Nat) (first: Position x y) (second: Position x y): Nat :=
  let one : Nat := 1
  let distanceY :=
    if first.y.val == second.y.val then Nat.zero
    else
      if first.y.val > second.y.val
        then Monoid.Nat.Sum.Instance.foldMap (λ n => if lines.any (λ pos => pos == n) then expansionFactor else one) $ (Nat.range second.y.val first.y.val)
        else Monoid.Nat.Sum.Instance.foldMap (λ n => if lines.any (λ pos => pos == n) then expansionFactor else one) $ (Nat.range first.y.val  second.y.val)
  let distanceX :=
    if first.x.val == second.x.val then Nat.zero
      else if first.x.val > second.x.val
        then Monoid.Nat.Sum.Instance.foldMap (λ n => if columns.any (λ pos => pos == n) then expansionFactor else one) $ (Nat.range second.x.val first.x.val)
        else Monoid.Nat.Sum.Instance.foldMap (λ n => if columns.any (λ pos => pos == n) then expansionFactor else one) $ (Nat.range first.x.val  second.x.val)

  Nat.add distanceX distanceY

def solve (expansionFactor: Nat) (input: List String): Nat :=
  let y := input.length
  if h: input ≠ []
    then
      let x := (input.head h).length
      if x == 0
        then 0
        else
          let grid            := Grid.fromInput input $ Grid.empty x y
          let galaxies        := findGalaxies grid
          let expandedColumns := findExpandedColumns grid
          let expandedLines   := findExpandedLines grid
          Monoid.Nat.Sum.Instance.foldMap (uncurry $ findPath expansionFactor expandedColumns expandedLines)
            ∘ List.groupsOfTwo
            $ galaxies
     else 0

namespace Sample

def sampleInput1: List String :=
  [ "...#......"
  , ".......#.."
  , "#........."
  , ".........."
  , "......#..."
  , ".#........"
  , ".........#"
  , ".........."
  , ".......#.."
  , "#...#....."
  ]

def grid1: Grid 10 10 := Grid.fromInput sampleInput1 $ Grid.empty 10 10

#eval grid1

#eval findGalaxies grid1

#eval findExpandedLines grid1

#eval findExpandedColumns grid1

#eval solve 2 sampleInput1

end Sample

def main: IO Unit := do
  let lines <- IO.FS.lines { toString := "./data/day11-1" }
  let expansionFactor1 : Nat := 2
  IO.println s!"part1: {solve expansionFactor1 lines.toList}"

  let expansionFactor2 : Nat := 1000000
  IO.println s!"part2: {solve expansionFactor2 lines.toList}"

  -- IO.println s!"part2: {solve2 lines.toList}"
