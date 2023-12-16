import AoC2023Lean4.AoC2023helpers
import Mathlib.Tactic
/-
467..114..
...*......
..35..633.
......#...
617*......
.....+.58.
..592.....
......755.
...$.*....
.664.598..
-/

/-- Adjacency relation on the grid (`Bool`-valued, computable). -/
def adjacent (p q : Position) : Bool := natDist p.x q.x ≤ 1 ∧ natDist p.y q.y ≤ 1

def anyAdjacent (ps qs : List Position) : Bool :=
  (ps.map fun p => qs.map fun q => adjacent p q).join.any id

/-- A symbol together with its coordinates on the grid. -/
structure Symbol where
  sym : Char
  pos : Position
deriving BEq, DecidableEq

instance : ToString Symbol := ⟨fun s => s!"'{s.sym}'@{s.pos}"⟩

def Symbol.mkCXY (c : Char) (x y : Nat) : Symbol := { sym := c, pos := Position.mkXY x y}

def readSymbols (data : String) : List Symbol :=
  let rows := data.splitOn "\n"
  ((rows.zip $ List.range rows.length).map fun row => (row.1.toList.zip $ List.range row.1.length).map
    fun cx => Symbol.mkCXY cx.1 cx.2 row.2).join

def isNumSymbol (s : Symbol) : Bool := s.sym.isNum

def isBlankSymbol (s : Symbol) : Bool := s.sym == '.' ∨ isNumSymbol s

def extractNonblankSymbols (syms : List Symbol) : List Symbol :=
  syms.filter $ (¬ isBlankSymbol ·)

def extractStarSymbols (syms : List Symbol) : List Symbol :=
  syms.filter $ (·.sym == '*')

def extractNumSymbols (syms : List Symbol) : List Symbol :=
  syms.filter isNumSymbol

def List.groupConsecutiveNats (L : List Nat) : List (List Nat) :=
  let S := L.dedup.mergeSort (· ≤ ·)
  let maxS := optNum S.getLast?
  ((List.range $ maxS + 1).splitOnP $ fun n => (S.find? (· == n) == none)).filter (· ≠ [])

/-- Group a list of objects into consequtive ones according to an indexing `f`.
The implementation assumes no duplicate `f`-values exist in the list. -/
def List.groupConsecutive {α : Type*} (L : List α) (f : α → Nat) : List (List α) :=
  listOpt <$> ((L.map f).groupConsecutiveNats.map fun g => g.map fun i => L.find? (f · == i))

def groupConsecutiveSymbols (syms : List Symbol) : List (List Symbol) :=
  let ys := (syms.map (fun s => s.pos.y)).dedup
  let yGrps := (List.range (optNum ys.maximum? + 1)).map fun y => syms.filter (·.pos.y == y)
  List.join $ yGrps.map fun yg => List.groupConsecutive yg (·.pos.x)

def symbolGroupToNum (syms : List Symbol) : Nat :=
  decimalNum ((·.sym.toDigit) <$> syms.dedup.mergeSort (·.pos.leLex ·.pos))

def gears (stars : List Symbol) (numgrps : List (List Symbol)) : List (Nat × Nat) :=
  let aux'' : List (List (Bool × Nat)) := stars.map (fun x =>
              (numgrps.map (fun ng =>
              (anyAdjacent [x.pos] (((·.pos) <$> ng)), symbolGroupToNum ng))))
  let aux' := (fun lbn => lbn.filter (·.fst)) <$> aux''
  let aux := (aux'.filter (·.length == 2)).map (fun lbn => ((·.snd) <$> lbn))
  aux.map (fun ln => (optNum ln[0]?, optNum ln[1]?))

def mulPair {α : Type*} [Mul α] (p : α × α) : α := p.fst * p.snd

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d03p1.txt").trim
  let processedInput := readSymbols probInput
  let numGrps := groupConsecutiveSymbols $ extractNumSymbols $ processedInput
  let starSyms := extractStarSymbols $ processedInput
  let sumMulPair := (mulPair <$> gears starSyms numGrps).sum
  IO.println s!"Answer (sum of gear ratios) : {sumMulPair}"

--#eval main
