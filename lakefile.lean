import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "stable"

package «aoc» { }

lean_lib AdventOfCode

lean_lib Evie

@[default_target]
lean_exe aoc {
  root := `Main
}
