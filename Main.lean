import AdventOfCode.All

open AdventOfCode

def main (args: List String): IO Unit := do
  match args.head? with
    |  "1" => Day1.main
    |  "2" => Day2.main
    |  "3" => Day3.main
    |  "4" => Day4.main
    |  "5" => Day5.main
    |  "6" => Day6.main
    |  "7" => Day7.main
    |  "8" => Day8.main
    |  "9" => Day9.main
    | "10" => Day10.main
    | _    => IO.println "huh?"
