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

namespace AdventOfCode.Day21
open Evie
open Evie.Prelude

inductive Cell where
  | Start
  | Garden
  | Rock
  | Occupied
deriving BEq
instance: ToString Cell where
  toString
  | .Start    => "S"
  | .Garden   => "."
  | .Rock     => "#"
  | .Occupied => "O"

def SomeGrid (pair: Nat × Nat): Type := Grid pair.fst pair.snd Cell

def step (grid: Grid x y Cell) (_s: Nat): List (Grid.Position x y) -> List (Grid.Position x y) :=
  Lean.HashSet.toList
    ∘ Lean.HashSet.empty.insertMany           -- throw them into a set to ensure uniqueness
    ∘ List.filter ((. != .Rock) ∘ grid.get)   -- remove rocks
    ∘ List.join                               -- join them; did I write foldMap somewhere?
    ∘ List.map Grid.Position.neighbors        -- find all neighbors

def solve1 (steps: Nat) (input: Sigma SomeGrid) (startX: Nat) (startY: Nat): Nat :=
  List.length
    ∘ Nat.fold (step input.snd) steps
    ∘ Option.toList
    $ Grid.Position.mkPosition input.fst.fst input.fst.snd startX startY

/--
I really don't like this.
-/
def solve2 (steps: Nat) (input: Sigma SomeGrid): Nat :=
  let (width, height) := input.fst 
  match input.snd.find (. == .Start), width == height with
    | .none, _     => 0 -- No .Start position
    | _    , false => 0 -- I assume the input is a square and use width as both width and hight below
    | .some start, true =>
        let visitedDiameter := Nat.div steps width - 1                              -- diameter of the giant <>

                                                                                    -- The number of alternatives alternates between two values
        let oddGardens  := Nat.pow (Nat.div (visitedDiameter    ) 2 * 2 + 1) 2      -- How many gardens will have an odd number of steps
        let evenGardens := Nat.pow (Nat.div (visitedDiameter + 1) 2 * 2    ) 2      -- and how many will have an even number

                                                                                    -- we need a width * 2 number of steps to reach the sequential equilibrium
        let oddGardenAlts  := solve1 (width * 2 + 1) input start.x start.y          -- find alternatives for odd  gardens
        let evenGardenAlts := solve1 (width * 2)     input start.x start.y          -- find alternatives for even gardens
                                                                                    -- no matter how many steps we go, there's going to be one garden on each coordinate
        let northAlts := solve1 (width - 1) input start.x     (width - 1)           -- so here we see how many alternatives we have in each of the four cases
        let eastAlts  := solve1 (width - 1) input 0           start.y
        let southAlts := solve1 (width - 1) input start.x     0
        let westAlts  := solve1 (width - 1) input (width - 1) start.y

                                                                                    -- And lastly, we have diagonal gardens. There's two kinds which alternate: small and large.
                                                                                    -- And we have them in every coordinate diagonal.
        let smallSteps := Nat.div width 2 - 1

        let neSmallAlts := solve1 smallSteps input 0           (width - 1)
        let nwSmallAlts := solve1 smallSteps input (width - 1) (width - 1)
        let seSmallAlts := solve1 smallSteps input 0           0
        let swSmallAlts := solve1 smallSteps input (width - 1) 0

        let largeSteps := Nat.div (width * 3) 2 - 1

        let neLargeAlts := solve1 largeSteps input 0           (width - 1)
        let nwLargeAlts := solve1 largeSteps input (width - 1) (width - 1)
        let seLargeAlts := solve1 largeSteps input 0           0
        let swLargeAlts := solve1 largeSteps input (width - 1) 0

        let mainGardenAlts := oddGardens * oddGardenAlts + evenGardens * evenGardenAlts

        let smallGardenAlts := (visitedDiameter + 1) * (neSmallAlts + nwSmallAlts + seSmallAlts + swSmallAlts)
        let largeGardenAlts := (visitedDiameter    ) * (neLargeAlts + nwLargeAlts + seLargeAlts + swLargeAlts)

        Monoid.Nat.Sum.Instance.fold
          [ mainGardenAlts
          , northAlts
          , eastAlts
          , southAlts
          , westAlts
          , smallGardenAlts
          , largeGardenAlts
          ]

namespace Debug

def markAlternative (positions: List (Grid.Position x y)): Nat × Nat -> Cell -> Cell
  | _     , .Rock => .Rock
  | (x, y), _     =>
    if positions.any (λpos => pos.x.val == x && pos.y.val == y)
    then .Occupied
    else .Garden

def debugStep (grid: Grid x y Cell) (n: Nat) (positions: List (Grid.Position x y)): IO (List (Grid.Position x y)) := do
  IO.println $ grid.mapWithPosition (markAlternative positions)
  IO.println s!"step: {n}, positions: {positions.length}"
  let _ <- IO.getStdin >>= IO.FS.Stream.getLine

  pure $ step grid n positions

def debug (steps: Nat) (input: Sigma SomeGrid): IO Unit := do
  let _ <- Nat.foldM (debugStep input.snd) (Option.toList $ input.snd.find (. == .Start) ) steps
  pure ()

end Debug

namespace Parser
open Lean

def cell: Parsec Cell :=
  Parser.sum
    [ Parsec.skipChar 'S' *> pure .Start
    , Parsec.skipChar '.' *> pure .Garden
    , Parsec.skipChar '#' *> pure .Rock
    ]

def grid: Parsec (List (List Cell)) :=
  Parser.sepBy' Parsec.ws $ Parser.many1 cell

def input (multiplier: Nat): Parsec (Sigma SomeGrid) := do
  let baseInput <- grid
  let input :=
    replicate' multiplier
      ∘ List.map (replicate multiplier)
      $ baseInput
  match input with
  | [] => Parsec.fail "empty first line"
  | head :: _ => do
    let x := head.length
    let y := input.length
    pure $ ⟨(x, y), Grid.fromList x y .Rock input⟩
  where
    replicate (times: Nat) (cells: List Cell): List Cell :=
      let noStart := cells.replace .Start .Garden
      List.join ∘ List.join
        $ [ List.replicate times noStart
          , cells :: List.replicate times noStart
          ]

    replicate' (times: Nat) (grid: List (List Cell)): List (List Cell) :=
      let noStart := grid.map (λcells => cells.replace .Start .Garden)
      List.join ∘ List.join
        $ [ List.replicate times noStart
          , grid :: List.replicate times noStart
          ]


end Parser

namespace Sample

def sampleInput: String := "........... .....###.#.\n.###.##..#.\n..#.#...#..\n....#.#....\n.##..S####.\n.##..#...#.\n.......##..\n.##.#.####.\n.##..##.##.\n..........."

def input: Sigma SomeGrid :=
  Option.maybe
    id
    (Sigma.mk (0, 0) $ Grid.replicate 0 0 Cell.Start)
    ((Parser.input 1).run sampleInput).toOption

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day21-1" }
      (Parser.input 0)
  match parsed1.snd.find (. == .Start) with
    | .none => pure ()
    | .some start => IO.println s!"part1 {solve1 64 parsed1 start.x start.y}"

  IO.println s!"part2 {solve2 26501365 parsed1}"
