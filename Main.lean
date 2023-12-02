import AdventOfCode.All

open AdventOfCode

def main (args: List String): IO Unit := do
  match args.head? with
    | "1" => Day1.main
    | "2" => Day2.main
    | _   => IO.println "huh?"
