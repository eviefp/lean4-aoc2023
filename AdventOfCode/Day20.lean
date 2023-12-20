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
import Std.Data.Nat.Gcd

namespace AdventOfCode.Day20
open Evie
open Evie.Prelude

abbrev ModuleName: Type := String

abbrev Outputs: Type := List ModuleName

inductive Pulse where
  | High: ModuleName -> Pulse
  | Low : ModuleName -> Pulse
instance: ToString Pulse where
  toString
  | .High _ => "High"
  | .Low  _ => "Low"

def Pulse.isHigh: Pulse -> Bool
  | .High _ => true
  | .Low  _ => false

def Pulse.name: Pulse -> ModuleName
  | .High name => name
  | .Low  name => name

inductive Module where
  | Broadcaster: ModuleName -> Outputs -> Module
  | FlipFlop: ModuleName -> Bool -> Outputs -> Module
  | Conjunction: ModuleName -> Lean.HashMap ModuleName Pulse -> Outputs -> Module
instance: ToString Module where
  toString
  | .Broadcaster name outputs => s!"{name} -> {outputs}"
  | .FlipFlop name state outputs => s!"%{name}/{state} -> {outputs}"
  | .Conjunction name _ outputs => s!"&{name} -> {outputs}"

def Module.name: Module -> ModuleName
  | .Broadcaster name _   => name
  | .FlipFlop name _ _    => name
  | .Conjunction name _ _ => name

def Module.outputs: Module -> Outputs
  | .Broadcaster _ outputs   => outputs
  | .FlipFlop _ _ outputs    => outputs
  | .Conjunction _ _ outputs => outputs

def step: Pulse -> ModuleName -> StateM (Lean.HashMap ModuleName Module) (Pulse × Outputs)
  | pulse, name => do
    let modules <- get

    match pulse, modules.find? name with
    | _, .none => pure (pulse, [])

    | .High _, .some (.Broadcaster bName dest) => pure (.High bName, dest)
    | .Low  _, .some (.Broadcaster bName dest) => pure (.Low bName ,dest)

    | .High _, .some (.FlipFlop _ _ _)     => pure (pulse, [])
    | .Low  _, .some (.FlipFlop flipName state dest) => do
        modify (λ hm => hm.insert flipName $ .FlipFlop flipName (not state) dest)
        pure $
            if state
            then (.Low  flipName, dest)
            else (.High flipName, dest)

    | .High _, .some (.Conjunction conjName history dest) => do
      let newHist := history.insert pulse.name (.High pulse.name) -- bit redundant
      modify (λ hm => hm.insert conjName $ .Conjunction conjName newHist dest)
      pure $
        if List.all (HashMap.values newHist) Pulse.isHigh
        then (.Low  conjName, dest)
        else (.High conjName, dest)
    | .Low  _, .some (.Conjunction conjName history dest) =>
      let newHist := history.insert pulse.name (.Low pulse.name) -- bit redundant
      modify (λ hm => hm.insert conjName $ .Conjunction conjName newHist dest)
      pure (.High conjName, dest)
  where
    countHighs: List Pulse -> Nat
      | [] => 0
      | (.High _) :: xs => 1 + countHighs xs
      | (.Low  _) :: xs => countHighs xs

partial def process: Nat -> List (Pulse × Outputs) -> StateM (Lean.HashMap ModuleName Module) (Nat × Nat)
  | 0    , [] => pure (0, 0)
  | n + 1, [] => process n [(.Low "button", ["broadcaster"])]
  | k    , (p, ms) :: rest => do
    let results <- List.mapM (step p) ms
    let current := results.foldl countPulse (0, 0)
    add current <$> process k (rest ++ results)

  where
    countPulse: (Nat × Nat) -> (Pulse × Outputs) -> (Nat × Nat)
      | acc, (.Low  _, xs) => (acc.fst + xs.length, acc.snd            )
      | acc, (.High _, xs) => (acc.fst            , acc.snd + xs.length)

    add (l: Nat × Nat) (r: Nat × Nat): Nat × Nat := (l.fst + r.fst, l.snd + r.snd)

def solve1 (input: Lean.HashMap ModuleName Module): Nat :=
  let n := 999
  let result := (process n [(.Low "button", ["broadcaster"])]).run input
  (result.fst.fst + n + 1) * result.fst.snd

partial def process2: List (Pulse × Outputs) -> Nat -> (Lean.HashMap ModuleName Nat) -> StateM (Lean.HashMap ModuleName Module) (Lean.HashMap ModuleName Nat)
  | [], n, cache => process2 [(.Low "button", ["broadcaster"])] (n+1) cache
  | (p, ms)  :: rest, n, cache => do
    let results <- List.mapM (step p) ms
    let cache' := updateCache n cache results
    if cache'.size == 4
    then pure cache'
    else process2 (rest ++ results) n cache'
  where
    update: String -> String -> Nat -> Lean.HashMap ModuleName Nat -> Lean.HashMap ModuleName Nat
    | expected, name, n, hm =>
      if name == expected && not (hm.contains expected)
      then hm.insert name n
      else hm

    -- Yeah, this is pretty awful. The idea is, a Conjunction module goes to 'rx' as its only input: 'ns'
    -- For this to throw a .Low, it needs to receive all .High
    -- The four modules below are the four inputs for 'ns'
    -- So, in order to figure out when this happens, we need to find the cycle at which each send a .High
    -- We store the first time this occurs, then stop.
    -- We then do a lcm over these numbers in 'solve2'.
    updateCache: Nat -> Lean.HashMap ModuleName Nat -> List (Pulse × Outputs) -> Lean.HashMap ModuleName Nat
    | _, hm, [] => hm
    | n, hm, (.High name, _xs) :: rest =>
        let newCache :=
          update "cq" name n
          ∘ update "vp" name n
          ∘ update "rv" name n
          ∘ update "dc" name n
          $ hm
        updateCache n newCache rest
    | _, hm, _ => hm

def solve2 (input: Lean.HashMap ModuleName Module): Nat :=
  let result := (process2 [(.Low "button", ["broadcaster"])] 1 Lean.HashMap.empty).run input
  List.foldl Nat.lcm 1 (HashMap.values result.fst)

namespace Parser
open Lean

def broadcaster: Parsec Module := do
  Parsec.skipString "broadcaster -> "
  let modules <- Parser.sepBy ", " Parser.identifier
  pure $ .Broadcaster "broadcaster" modules

def flipFlop: Parsec Module := do
  Parsec.skipChar '%'
  let name <- Parser.identifier
  Parsec.skipString " -> "
  let modules <- Parser.sepBy ", " Parser.identifier
  pure $ .FlipFlop name false modules

def conjunction: Parsec Module := do
  Parsec.skipChar '&'
  let name <- Parser.identifier
  Parsec.skipString " -> "
  let modules <- Parser.sepBy ", " Parser.identifier
  pure $ .Conjunction name Lean.HashMap.empty modules

def module: Parsec Module := broadcaster <|> flipFlop <|> conjunction

def input: List String -> Lean.HashMap ModuleName Module :=
  createMap
    ∘ List.catMaybes
    ∘ List.map Except.toOption
    ∘ List.map module.run
  where
    mkInputs (name: ModuleName) (hm: Lean.HashMap ModuleName Pulse) (module: Module): Lean.HashMap ModuleName Pulse :=
      if module.outputs.elem name
      then hm.insert module.name $ .Low module.name
      else hm

    go (modules: List Module) (hm: Lean.HashMap ModuleName Module) (m: Module): Lean.HashMap ModuleName Module :=
      match m with
      | .Conjunction name _ outputs => hm.insert name $ .Conjunction name (List.foldl (mkInputs name) Lean.HashMap.empty modules) outputs
      | mod                         => hm.insert mod.name mod

    createMap (modules: List Module): Lean.HashMap ModuleName Module :=
      List.foldl (go modules) Lean.HashMap.empty modules

end Parser

namespace Sample

def sampleInput1: List String :=
  [ "broadcaster -> a, b, c"
  , "%a -> b"
  , "%b -> c"
  , "%c -> inv"
  , "&inv -> a"
  ]

def sampleInput2: List String :=
  [ "broadcaster -> a"
  , "%a -> inv, con"
  , "&inv -> b"
  , "%b -> con"
  , "&con -> output"
  ]

end Sample

def main: IO Unit := do
  let parsed <- (Parser.input ∘ Array.toList) <$> IO.FS.lines { toString := "./data/day20-1" }
  IO.println s!"part1: {solve1 parsed}"
  IO.println s!"part2: {solve2 parsed}"
