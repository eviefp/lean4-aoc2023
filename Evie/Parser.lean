import Lean.Parser

namespace Evie.Parser

def sum: List (Lean.Parsec α) -> Lean.Parsec α :=
  List.foldl (λ all p => p <|> all) (Lean.Parsec.fail "")

def optionToParser (o: Option α) (err: String) : Lean.Parsec α :=
  match o with
    | .some res => pure res
    | .none => Lean.Parsec.fail err

def iterator (iter: String.Iterator) : Lean.Parsec.ParseResult String.Iterator :=
  Lean.Parsec.ParseResult.success iter iter

def digit: Lean.Parsec Nat := do
  let char <- Lean.Parsec.digit
  let optNat := String.toNat? char.toString
  optionToParser optNat "failed to parse digit"

def nat : Lean.Parsec Nat := do
  let optNat <- String.toNat? <$> Lean.Parsec.many1Chars (Lean.Parsec.attempt Lean.Parsec.digit)
  optionToParser optNat "failed to parse nat"

def int : Lean.Parsec Int := do
  let optSign <- Lean.Parsec.peek!
  let sign <- match optSign with
    | '-' => Lean.Parsec.pstring "-"
    | _   => pure ""

  let intString <- Lean.Parsec.many1Chars (Lean.Parsec.attempt Lean.Parsec.digit)
  let optInt := String.toInt? (sign ++ intString)
  optionToParser optInt "failed to parse int"

def parseOptionalChar (c: Char): Lean.Parsec Unit := do
  let hasNext <- Lean.Parsec.peek?
  match hasNext with
    | some _ => Lean.Parsec.skipChar c
    | none => pure ()

def many: (parser: Lean.Parsec α) -> Lean.Parsec (List α) :=
  Functor.map Array.toList
    ∘ Lean.Parsec.many
    ∘ Lean.Parsec.attempt

def many1: (parser: Lean.Parsec α) -> Lean.Parsec (List α) :=
  Functor.map Array.toList
    ∘ Lean.Parsec.many1
    ∘ Lean.Parsec.attempt

def either (l: Lean.Parsec α) (r: Lean.Parsec β) : Lean.Parsec (α ⊕ β) := do
  let left := Sum.inl <$> l
  let right := Sum.inr <$> r
  left <|> right

/-- Warning: blows up in IO if the parsing fails -/
def parseFile (fname: System.FilePath) (parser: Lean.Parsec α): IO α :=
  IO.FS.readFile fname >>= IO.ofExcept ∘ parser.run
