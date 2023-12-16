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

namespace AdventOfCode.Day16
open Evie
open Evie.Prelude

inductive Cell where
  | Empty              -- '.', empty space
  | UpMirror           -- '/' mirror, reflects left light UP
  | DownMirror         -- '\' mirror, reflect left light DOWN
  | VerticalSplitter   -- '|' splitter, splits UP and DOWN
  | HorizontalSplitter -- '-' splitter, splits UP and DOWN

def Cell.toString: Cell -> String
  | .Empty              => "."
  | .UpMirror           => "/"
  | .DownMirror         => "\\"
  | .VerticalSplitter   => "|"
  | .HorizontalSplitter => "-"

instance: ToString Cell where
  toString := Cell.toString

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

structure Beam (x y: Nat) where
  direction: Direction
  position: Grid.Position x y
deriving BEq, Hashable

instance: ToString (Beam x y) where
  toString b := s!"<{b.direction}, {b.position}>"

def step: Cell -> Beam x y -> List (Beam x y)
  | .Empty, ⟨.NS, pos⟩              => down  pos
  | .Empty, ⟨.SN, pos⟩              => up    pos
  | .Empty, ⟨.EW, pos⟩              => left  pos
  | .Empty, ⟨.WE, pos⟩              => right pos

  | .UpMirror, ⟨.NS, pos⟩           => left  pos
  | .UpMirror, ⟨.SN, pos⟩           => right pos
  | .UpMirror, ⟨.EW, pos⟩           => down  pos
  | .UpMirror, ⟨.WE, pos⟩           => up    pos

  | .DownMirror, ⟨.NS, pos⟩         => right pos
  | .DownMirror, ⟨.SN, pos⟩         => left  pos
  | .DownMirror, ⟨.EW, pos⟩         => up    pos
  | .DownMirror, ⟨.WE, pos⟩         => down  pos

  | .VerticalSplitter, ⟨.NS, pos⟩   => down pos
  | .VerticalSplitter, ⟨.SN, pos⟩   => up   pos
  | .VerticalSplitter, ⟨.EW, pos⟩   => List.join [ up pos, down pos ]
  | .VerticalSplitter, ⟨.WE, pos⟩   => List.join [ up pos, down pos ]

  | .HorizontalSplitter, ⟨.NS, pos⟩ => List.join [ left pos, right pos ]
  | .HorizontalSplitter, ⟨.SN, pos⟩ => List.join [ left pos, right pos ]
  | .HorizontalSplitter, ⟨.EW, pos⟩ => left  pos
  | .HorizontalSplitter, ⟨.WE, pos⟩ => right pos
  where
    up (pos: Grid.Position x y): List (Beam x y) :=
      Option.toList $ Option.map (Beam.mk .SN) pos.up
    down (pos: Grid.Position x y): List (Beam x y) :=
      Option.toList $ Option.map (Beam.mk .NS) pos.down
    left (pos: Grid.Position x y): List (Beam x y) :=
      Option.toList $ Option.map (Beam.mk .EW) pos.left
    right (pos: Grid.Position x y): List (Beam x y) :=
      Option.toList $ Option.map (Beam.mk .WE) pos.right

partial def loop: Grid x y Cell -> List (Beam x y) -> StateM (Lean.HashSet (Beam x y)) (List (Beam x y))
  | _, [] => pure []
  | grid, beam :: xs => do
    let hs <- StateT.get

    if hs.contains beam
    then do
      loop grid xs     -- stop, we already went through it
    else do
        let cell := grid.get beam.position
        let next := step cell beam
        StateT.modify' (λ hs => hs.insert beam)
        loop grid (next.append xs)

def energizedCells (grid: Grid x y Cell) (start: Beam x y): Nat :=
  let beams := (loop grid [start]).run Lean.HashSet.empty -- go over the whole thing
  let hash := beams.snd.insert start

  Lean.HashSet.size
    ∘ List.foldl (λ hs ⟨_, pos⟩ => hs.insert pos) Lean.HashSet.empty -- create a new HashSet with just the positions
    $ hash.toList

def solve1 (input: List (List Cell)): Nat :=
  let y := input.length
  match input with
  | [] => 0
  | i :: _ =>
    let x := i.length
    let grid := Grid.fromList x y .Empty input
    let startPos := Grid.Position.mkPosition x y 0 0
    match startPos with
    | .none => 0
    | .some start => energizedCells grid ⟨.WE, start⟩

/--
This could be a lot faster if we cached beams.

For example, regardless of where we start, if we ever reach a `Beam x y`, we only need to compute it once.

This would make things A LOT faster. However, that would require to keep track of beams, which I currently don't.

Besides, the current solution is reasonably fast.
-/
def solve2 (input: List (List Cell)): Nat :=
  let y := input.length
  match input with
  | [] => 0
  | i :: _ =>
    let x := i.length
    let grid := Grid.fromList x y .Empty input
    let startPos := startPositions x y
    Monoid.Nat.Max.Instance.foldMap (energizedCells grid) $ startPos
  where
    startPositions (x y: Nat): List (Beam x y) :=
      List.catMaybes ∘ List.join $
        [ List.map (λ x' => Beam.mk .NS <$> Grid.Position.mkPosition x y x'    0)     $ Nat.range 0 x -- NS
        , List.map (λ x' => Beam.mk .SN <$> Grid.Position.mkPosition x y x'    (y-1)) $ Nat.range 0 x -- SN
        , List.map (λ y' => Beam.mk .WE <$> Grid.Position.mkPosition x y 0     y')    $ Nat.range 0 y -- WE
        , List.map (λ y' => Beam.mk .EW <$> Grid.Position.mkPosition x y (x-1) y')    $ Nat.range 0 y -- EW
        ]



namespace Parser
open Lean

def cell: Parsec Cell :=
  Parser.sum
    [ Parsec.skipChar '.'  *> pure .Empty
    , Parsec.skipChar '/'  *> pure .UpMirror
    , Parsec.skipChar '\\' *> pure .DownMirror
    , Parsec.skipChar '|'  *> pure .VerticalSplitter
    , Parsec.skipChar '-'  *> pure .HorizontalSplitter
    ]

def input: Parsec (List (List Cell)) := do
  let line <- Parser.many1 cell
  let rest <- Parser.many1 (Parsec.skipChar '\n' *> Parser.many1 cell)
  pure $ line :: rest

end Parser

namespace Sample

def sampleInput: String := ".|...\\....\n|.-.\\.....\n.....|-...\n........|.\n..........\n.........\\\n..../.\\\\..\n.-.-/..|..\n.|....-|.\\\n..//.|...."

def parsedInput: List (List Cell) := Option.maybe id [] (Parser.input.run sampleInput).toOption

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day16-1" }
      Parser.input
  IO.println s!"part1 {solve1 parsed1}"
  IO.println s!"part2 {solve2 parsed1}"
