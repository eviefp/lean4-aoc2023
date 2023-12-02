import Lean.Parser

namespace Evie.Parser

def optionToParser (o: Option α) (err: String) : Lean.Parsec α :=
  match o with
    | .some res => pure res
    | .none => Lean.Parsec.fail err


def nat : Lean.Parsec Nat := do
  let optNat <- String.toNat? <$> Lean.Parsec.many1Chars Lean.Parsec.digit
  optionToParser optNat "failed to parse nat"

/-- Warning: blows up in IO if the parsing fails -/
def parseFile (fname: System.FilePath) (parser: Lean.Parsec α): IO α :=
  IO.FS.readFile fname >>= IO.ofExcept ∘ parser.run
