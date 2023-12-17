import AoC2023Lean4.AoC2023helpers
import Mathlib.Tactic
/-
...#......
.......#..
#.........
..........
......#...
.#........
.........#
..........
.......#..
#...#.....
-/

structure Cosmos where
  space : List (List Char)

def Cosmos.transpose (cosm : Cosmos) : Cosmos := Cosmos.mk (cosm.space.transpose)

def Cosmos.expandRows (cosm : Cosmos) : Cosmos :=
  let rs := cosm.space.map (fun r => (r, r.all (· == '.')))
  Cosmos.mk (rs.map fun rb => if rb.2 then [rb.1, rb.1] else [rb.1]).join

def Cosmos.expandColumns (cosm : Cosmos) : Cosmos := cosm.transpose.expandRows.transpose

/-- A cosmos parser. -/
def parseCosmos (data : String) : Cosmos :=
  Cosmos.mk (String.toList <$> (data.splitOn "\n"))

def Cosmos.galaxies (cosm : Cosmos) : List (Nat × Nat) :=
  let rsi := List.join $ (cosm.space.zip (List.range cosm.space.length)).map fun ri =>
    ((ri.1.zip (List.range ri.1.length)).map fun c => (c.1, (c.2 , ri.2)))
  (·.2) <$> (rsi.filter (·.1 == '#'))

def galDist (p q : Nat × Nat) := natDist p.1 q.1 + natDist p.2 q.2

def Cosmos.galaxyPairDistSum (cosm : Cosmos) : Nat :=
  let gals := cosm.galaxies
  let js := List.range gals.length
  ((js.drop 1).map (fun j =>
    ((List.range j).map fun i => galDist gals[i]! gals[j]!).sum)).sum

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d11p1.txt").trim
  let cosmos := parseCosmos probInput
  let sumGalDist := cosmos.expandRows.expandColumns.galaxyPairDistSum
  IO.println s!"Answer 1 (sum of galaxy distances) : {sumGalDist}"

--#eval main
