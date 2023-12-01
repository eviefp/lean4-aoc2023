namespace Evie.String

def slices (str: String): List String :=
  str.length.foldRev (fun n r => str.drop n :: r) []
