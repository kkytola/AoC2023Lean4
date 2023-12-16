import AoC2023Lean4.AoC2023helpers
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

def expansionFactor := 1000000

structure Cosmos where
  space : List (List Char)

def Cosmos.toString (cosm : Cosmos) : String :=
  "\n".intercalate ((fun lc => "".intercalate (lc.map Char.toString)) <$> cosm.space)

instance : ToString Cosmos := ⟨Cosmos.toString⟩

def Cosmos.transpose (cosm : Cosmos) : Cosmos := Cosmos.mk (cosm.space.transpose)

def Cosmos.expandRows (cosm : Cosmos) : Cosmos :=
  let rs := cosm.space.map (fun r => (r, r.all (· == '.')))
  Cosmos.mk (rs.map fun rb => if rb.2 then [rb.1, rb.1] else [rb.1]).join

unsafe def Cosmos.expandableRows (cosm : Cosmos) : List Nat :=
  let rs := (List.range cosm.space.length).map (fun i => (i, cosm.space[i]!.all (· == '.')))
  (·.1) <$> rs.filter (·.2)

unsafe def Cosmos.expandableColumns (cosm : Cosmos) : List Nat := cosm.transpose.expandableRows

def Cosmos.expandColumns (cosm : Cosmos) : Cosmos := cosm.transpose.expandRows.transpose

/-- A cosmos parser. -/
def parseCosmos (data : String) : Cosmos :=
  Cosmos.mk (String.toList <$> (data.splitOn "\n"))

def Cosmos.galaxies (cosm : Cosmos) : List (Nat × Nat) :=
  let rsi := List.join $ (cosm.space.zip (List.range cosm.space.length)).map fun ri =>
    ((ri.1.zip (List.range ri.1.length)).map fun c => (c.1, (c.2 , ri.2)))
  (·.2) <$> (rsi.filter (·.1 == '#'))

def galDist (p q : Nat × Nat) := natDist p.1 q.1 + natDist p.2 q.2

def galExpVertDist (rexp : List Nat) (p q : Nat × Nat) :=
  let extra := (rexp.filter (fun i => min p.2 q.2 < i ∧ i < max p.2 q.2)).length
  natDist p.2 q.2 + (expansionFactor - 1) * extra

def galExpHorizDist (cexp : List Nat) (p q : Nat × Nat) :=
  let extra := (cexp.filter (fun i => min p.1 q.1 < i ∧ i < max p.1 q.1)).length
  natDist p.1 q.1 + (expansionFactor - 1) * extra

def galExpDist (rexp cexp : List Nat) (p q : Nat × Nat) :=
  galExpHorizDist cexp p q + galExpVertDist rexp p q

def Cosmos.galaxyPairDistSum (cosm : Cosmos) : Nat :=
  let gals := cosm.galaxies
  let js := List.range gals.length
  ((js.drop 1).map (fun j =>
    ((List.range j).map fun i => galDist gals[i]! gals[j]!).sum)).sum

unsafe def Cosmos.galaxyPairExpDistSum (cosm : Cosmos) : Nat :=
  let gals := cosm.galaxies
  let rexp := cosm.expandableRows
  let cexp := cosm.expandableColumns
  let js := List.range gals.length
  ((js.drop 1).map (fun j =>
    ((List.range j).map fun i => galExpDist rexp cexp gals[i]! gals[j]!).sum)).sum

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d11p1.txt").trim
  let cosmos := parseCosmos probInput
  let sumGalDist := cosmos.galaxyPairExpDistSum
  IO.println s!"Answer 2 (sum of galaxy distances) : {sumGalDist}"

--#eval main
