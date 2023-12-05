import Lean.Parser

namespace Evie.Parser

def optionToParser (o: Option α) (err: String) : Lean.Parsec α :=
  match o with
    | .some res => pure res
    | .none => Lean.Parsec.fail err

def iterator (iter: String.Iterator) : Lean.Parsec.ParseResult String.Iterator :=
  Lean.Parsec.ParseResult.success iter iter

def nat : Lean.Parsec Nat := do
  let optNat <- String.toNat? <$> Lean.Parsec.many1Chars (Lean.Parsec.attempt Lean.Parsec.digit)
  optionToParser optNat "failed to parse nat"

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
