import AoC2023Lean4.AoC2023helpers
/-
0 3 6 9 12 15
1 3 6 10 15 21
10 13 16 21 30 45
-/

def List.consecutivePairs {α : Type*} (l : List α) : List (α × α) :=
  let rec helper (prev : α) (rem : List α) : List (α × α) := match rem with
    | [] => []
    | a :: as => (prev, a) :: helper a as
  optList (do pure (helper (← l[0]?) (l.drop 1)))

def List.differences {α : Type*} [Sub α] (l : List α) : List α :=
  l.consecutivePairs.map (fun p => p.2 - p.1)

-- Unnecessary?
def List.isAllZeros {α : Type*} [Zero α] [BEq α] (l : List α) : Bool := l.all (· == 0)

unsafe def iteratedDifferences {α : Type*} [BEq α] [Sub α] [Zero α] (l : List α) : List (List α) :=
  if l.isAllZeros then [l]
    else l :: iteratedDifferences l.differences

unsafe def extendIteratedDifferences {α : Type*} [BEq α] [Sub α] [Add α] [Zero α] (ll : List (List α)) :
    List (List α) :=
  let rec fillIn (arr : List (List α)) (r : Nat) : List (List α) :=
    let targetLine := optList arr[r]?
    let nextLine := optList arr[r+1]?
    let updatedLine : List α :=
      if r ≥ arr.length - 1 then targetLine ++ [0]
        else
          let incr := optNum nextLine.getLast?
          let last := optNum targetLine.getLast?
          targetLine ++ [last + incr]
    let withUpdated := (arr.removeNth r).insertNth r updatedLine
    if r == 0 then withUpdated
      else fillIn withUpdated (r-1)
  fillIn ll (ll.length - 1)

/-- A number list parser. -/
def readNumbers (data : String) : List Int :=
  listOpt $ String.toInt? <$> data.splitOn " "

def parseInput (data : String) : List (List Int) :=
  (readNumbers <$> data.splitOn "\n").map (fun l => l.map (fun i => i))

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d09p1.txt").trim
  let dataRev := List.reverse <$> parseInput probInput
  let predictions := (optNum ·.getLast?) <$> ((optList ·[0]?) <$> (extendIteratedDifferences <$> (iteratedDifferences <$> dataRev)))
  IO.println s!"Answer (foo) : {predictions.sum}"

--#eval main
