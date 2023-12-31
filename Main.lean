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
    | "11" => Day11.main
    | "12" => Day12.main
    | "13" => Day13.main
    | "14" => Day14.main
    | "15" => Day15.main
    | "16" => Day16.main
    | "17" => Day17.main
    | "18" => Day18.main
    | "19" => Day19.main
    | "20" => Day20.main
    | "21" => Day21.main
    | "22" => Day22.main
    | "23" => Day23.main
    | "24" => Day24.main
    | "25" => Day25.main
    | _    => IO.println "huh?"
