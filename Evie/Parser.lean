import Lean.Parser

namespace Evie.Parser

/-- Warning: blows up in IO if the parsing fails -/
def parseFile (fname: System.FilePath) (parser: Lean.Parsec α): IO α :=
  IO.FS.readFile fname >>= IO.ofExcept ∘ parser.run
