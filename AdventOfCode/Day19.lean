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

namespace AdventOfCode.Day19
open Evie
open Evie.Prelude

structure Rating where
  x: Nat
  m: Nat
  a: Nat
  s: Nat
instance: ToString Rating where
  toString r := s!"({r.x}, {r.m}, {r.a}, {r.s})"

inductive Target where
  | ToWorkflow: String -> Target
  | ToRejected
  | ToAccepted
instance: Inhabited Target where
  default := .ToRejected
instance: ToString Target where
  toString
    | .ToRejected => "R"
    | .ToAccepted => "A"
    | .ToWorkflow t => t

inductive Attribute where
  | X | M | A | S

structure Constraint where
  min: Nat
  max: Nat
instance: ToString Constraint where
  toString
    | ⟨min, max⟩ => s!"[{min}, {max}]"

structure Condition where
  constraint: Constraint
  attr: Attribute

structure Rule where
  condition: Condition
  target: Target
instance: ToString Rule where
  toString r := s!"<{r.target}>"

structure Workflow where
  name: String
  rules: List Rule
instance: ToString Workflow where
  toString w := s!"({w.name}: {w.rules})"

structure Input where
  workflows: List Workflow
  ratings: List Rating
instance: ToString Input where
  toString i := s!"{i.workflows}\n{i.ratings}"

structure RatingConstraint where
  x: Constraint
  m: Constraint
  a: Constraint
  s: Constraint
instance: Inhabited RatingConstraint where
  default := ⟨ ⟨0, 4001⟩, ⟨0, 4001⟩, ⟨0, 4001⟩, ⟨0, 4001⟩ ⟩
instance: ToString RatingConstraint where
  toString
    | ⟨x, m, a, s⟩ => s!"<{x}, {m}, {a}, {s}>"

/--
Wait, there's more things here. What I wrote is fine in the positive case.

But we also have negative constraints, as in "else, it didn't match so". SO this function
DOES need to return two RatingConstraints.

Additionally, I don't think a single 'Constraint' is enough. For example, say we have

.Between 20 30

nope it's fine, because, I think, we always have [0, x] or [x, 4001] so we can't take chunks.

oh wait, yes; after a few steps (2 minimum) we may find:

we start at    .Between 50 100

then we find   .Between  0 70

we have two:   .Between 50 70 => goes forward
               .Between 0 50 => goes to next rule

  |----------|
----------|
            |------|
                |-------------

-/
def RatingConstraint.apply: Condition -> RatingConstraint -> Option RatingConstraint × Option RatingConstraint
  | ⟨c, .X⟩, rc => Prod.both' (Option.map (updateX rc)) $ go c rc.x
  | ⟨c, .M⟩, rc => Prod.both' (Option.map (updateM rc)) $ go c rc.m
  | ⟨c, .A⟩, rc => Prod.both' (Option.map (updateA rc)) $ go c rc.a
  | ⟨c, .S⟩, rc => Prod.both' (Option.map (updateS rc)) $ go c rc.s
  where
    updateX (rc: RatingConstraint) (x: Constraint): RatingConstraint := ⟨x   , rc.m, rc.a, rc.s⟩
    updateM (rc: RatingConstraint) (m: Constraint): RatingConstraint := ⟨rc.x, m   , rc.a, rc.s⟩
    updateA (rc: RatingConstraint) (a: Constraint): RatingConstraint := ⟨rc.x, rc.m, a   , rc.s⟩
    updateS (rc: RatingConstraint) (s: Constraint): RatingConstraint := ⟨rc.x, rc.m, rc.a, s   ⟩

    go: Constraint -> Constraint -> Option Constraint × Option Constraint
      | ⟨condMin, condMax⟩, ⟨ratingMin, ratingMax⟩ =>
        let min := Nat.max condMin ratingMin
        let max := Nat.min condMax ratingMax
        let succeed :=
          if max >= min
          then .some $ ⟨min, max⟩
          else .none
        let fail :=
          if ratingMax > condMax && ratingMin < condMax
          then .some ⟨condMax - 1, ratingMax⟩
          else if ratingMin < condMin
          then .some ⟨ratingMin, condMin + 1⟩
          else .none
        (succeed, fail)

def RatingConstraint.merge: RatingConstraint -> RatingConstraint -> RatingConstraint
  | ⟨x1, m1, a1, s1⟩, ⟨x2, m2, a2, s2⟩ => ⟨merge x1 x2, merge m1 m2, merge a1 a2, merge s1 s2⟩
    where
      merge: Constraint -> Constraint -> Constraint
        | ⟨min1, max1⟩, ⟨min2, max2⟩ => ⟨Nat.min min1 min2, Nat.max max1 max2⟩

def RatingConstraint.Monoid: Monoid.Monoid where
  Carrier := RatingConstraint
  unit := default
  op := RatingConstraint.merge

def process (r: Rating): List Rule -> Target
  | []      => panic! "no default target"
  | x :: xs =>
    if test r x.condition
      then x.target
      else process r xs
  where
    test (r: Rating): Condition -> Bool
      | ⟨ ⟨m, n⟩, .X⟩ => r.x > m && r.x < n
      | ⟨ ⟨m, n⟩, .M⟩ => r.m > m && r.m < n
      | ⟨ ⟨m, n⟩, .A⟩ => r.a > m && r.a < n
      | ⟨ ⟨m, n⟩, .S⟩ => r.s > m && r.s < n

partial def isAccepted (workflows: Lean.HashMap String Workflow) (workflow: Workflow) (rating: Rating): Bool :=
  match process rating workflow.rules with
    | .ToAccepted => true
    | .ToRejected => false
    | .ToWorkflow t =>
      match workflows.find? t with
        | .none => false
        | .some nextWorkflow => isAccepted workflows nextWorkflow rating

def solve1 (i: Input): Nat :=
  let workflows := i.workflows.foldl (λhm wf => hm.insert wf.name wf) Lean.HashMap.empty
  match workflows.find? "in" with
    | .none => 0
    | .some start =>
        Monoid.Nat.Sum.Instance.foldMap ratingValue
            ∘ List.filter (isAccepted workflows start)
            $ i.ratings

  where
    ratingValue (r: Rating): Nat := r.x + r.m + r.a + r.s

partial def findConstraints (wf: Lean.HashMap String Workflow): List (RatingConstraint × List Rule) -> List RatingConstraint
  | []                   => [] -- done processing, nothing left to do
  | (_, []) :: _         => panic! "findConstraints: no default"
  | (c, r :: rs) :: rest =>
    let (pass', fail') := c.apply r.condition

    let pass := pass'.map (λ pass =>
      match r.target with
      | .ToRejected => []
      | .ToAccepted => pass :: findConstraints wf rest
      | .ToWorkflow targetName =>
        match wf.find? targetName with
        | .none        => panic! s!"findConstraints: no such target {targetName}"
        | .some target => findConstraints wf $ (pass, target.rules) :: rest)

    let fail := fail'.map (λ fail => findConstraints wf $ (fail, rs) :: rest)

    List.join ∘ List.catMaybes $ [pass, fail]

/--
[0   , 4001], [0   , 837 ], [0   , 1715], [1352, 2769]
[0   , 4001], [838 , 1801], [0   , 4001], [1352, 2769]
[0   , 4001], [0   , 1547], [0   , 4001], [2770, 3447]
[0   , 4001], [1548, 4001], [0   , 4001], [2770, 3447]
[0   , 4001], [0   , 4001], [0   , 4001], [3448, 4001]
[0   , 4001], [2090, 4001], [2007, 4001], [0   , 1351]

[2662, 4001], [0   , 4001], [0   , 2006], [0   , 1351]

[0   , 2439], [0   , 2089], [2007, 4001], [538 , 1351]
[0   , 1416], [0   , 4001], [0   , 2006], [0   , 1351]
-/
def solve2 (i: Input): Nat :=
  let workflows := i.workflows.foldl (λhm wf => hm.insert wf.name wf) Lean.HashMap.empty
  match workflows.find? "in" with
    | .none       => 0
    | .some start =>
      uncurry removeOverlap
        ∘ Prod.both (Monoid.Nat.Sum.Instance.foldMap toVariants) overlap
        ∘ (λ c => (c, c))
        ∘ findConstraints workflows
        $ [(default, start.rules)]
  where
    toVariants: RatingConstraint -> Nat
    | ⟨x, m, a, s⟩ =>
        (x.max - x.min - 1)
      * (m.max - m.min - 1)
      * (a.max - a.min - 1)
      * (s.max - s.min - 1)

    overlap: List RatingConstraint -> Nat := λ _ => 0

    removeOverlap (total: Nat) (over: Nat): Nat := total - over

namespace Parser
open Lean

def rule: Parsec Rule := Parsec.attempt regular <|> last
  where
    last: Parsec Rule := do
      let name <- Parsec.many1Chars Parsec.asciiLetter
      pure ⟨ ⟨⟨0, 4001⟩, .X⟩, mkTarget name⟩

    mkTarget: String -> Target
      | "A" => .ToAccepted
      | "R" => .ToRejected
      | t   => .ToWorkflow t

    gtOrLt: Char -> Nat -> Attribute -> Condition
      | '>', n, attr => ⟨ ⟨n, 4001⟩, attr⟩
      | '<', n, attr => ⟨ ⟨0, n   ⟩, attr⟩
      | _ , _, _     => ⟨ ⟨0, 4001⟩, .X⟩

    mkCondition: Char -> Char -> Nat -> Condition
      | 'x', op, val => gtOrLt op val .X
      | 'm', op, val => gtOrLt op val .M
      | 'a', op, val => gtOrLt op val .A
      | 's', op, val => gtOrLt op val .S
      | _  , _ , _   => ⟨ ⟨0, 4001⟩, .X⟩

    regular: Parsec Rule := do
      let rating <- Parsec.asciiLetter
      let ltOrGt <- Parser.oneOf ['>', '<']
      let value <- Parser.nat
      Parsec.skipChar ':'
      let name <- Parsec.many1Chars Parsec.asciiLetter
      pure ⟨mkCondition rating ltOrGt value, mkTarget name⟩


def workflow: Parsec Workflow := do
  let name <- Parsec.many1Chars Parsec.asciiLetter
  Parsec.skipChar '{'
  let rules <- Parser.sepBy "," rule
  Parsec.skipChar '}'
  pure ⟨name, rules⟩

def rating: Parsec Rating := do
  Parsec.skipString "{x="
  let x <- Parser.nat

  Parsec.skipString ",m="
  let m <- Parser.nat

  Parsec.skipString ",a="
  let a <- Parser.nat

  Parsec.skipString ",s="
  let s <- Parser.nat

  Parsec.skipChar '}'

  pure ⟨x, m, a, s⟩

def input: Parsec Input := do
  let workflows <- Parser.sepBy "\n" workflow
  Parsec.ws
  let ratings <- Parser.sepBy "\n" rating
  pure ⟨workflows, ratings⟩

end Parser

namespace Sample

def sampleInput: String := "px{a<2006:qkq,m>2090:A,rfg}\npv{a>1716:R,A}\nlnx{m>1548:A,A}\nrfg{s<537:gd,x>2440:R,A}\nqs{s>3448:A,lnx}\nqkq{x<1416:A,crn}\ncrn{x>2662:A,R}\nin{s<1351:px,qqz}\nqqz{s>2770:qs,m<1801:hdj,R}\ngd{a>3333:R,R}\nhdj{m>838:A,pv}\n\n{x=787,m=2655,a=1222,s=2876}\n{x=1679,m=44,a=2067,s=496}\n{x=2036,m=264,a=79,s=2244}\n{x=2461,m=1339,a=466,s=291}\n{x=2127,m=1623,a=2188,s=1013}\n"

def input: Input := Option.maybe id ⟨[], []⟩ (Parser.input.run sampleInput).toOption

end Sample

def main: IO Unit := do
  let parsed1 <-
    Parser.parseFile
      { toString := "./data/day19-1" }
      Parser.input
  IO.println s!"part1 {solve1 parsed1}"
  IO.println s!"part2 {solve2 parsed1}"
