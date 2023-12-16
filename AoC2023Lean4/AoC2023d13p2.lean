import AoC2023Lean4.AoC2023helpers
/-
#.##..##.
..#.##.#.
##......#
##......#
..#.##.#.
..##..##.
#.#.##.#.

#...##..#
#....#..#
..##..###
#####.##.
#####.##.
..##..###
#....#..#
-/

def isEqualUntilRunsOut {α : Type*} [BEq α] : List α → List α → Bool
  | [] , _ => true
  | _ , [] => true
  | a :: as , b :: bs => if a == b then isEqualUntilRunsOut as bs else false

def List.isMirroredAt {α : Type*} [BEq α] (m : Nat) (as : List α) : Bool :=
  isEqualUntilRunsOut (as.drop m) (as.take m).reverse

def List.locationsOfMirroring {α : Type*} [BEq α] (as : List α) : List Nat :=
  listOpt $ (((List.range as.length)).drop 1).map fun m =>
            if as.isMirroredAt m then some m else none

def Valley := List (List Char)
deriving Inhabited

def Valley.toString (val : Valley) : String :=
  "\n".intercalate $ (fun row => "".intercalate (row.map Char.toString)) <$> val

instance : ToString Valley := ⟨Valley.toString⟩

def Valley.toList (val : Valley) : List (List Char) := val

def Valley.getRow? (val : Valley) (r : Nat) : Option (List Char) := val.toList[r]?

def Valley.getRow (val : Valley) (r : Nat) : List Char := optList (val.getRow? r)

def Valley.height (val : Valley) := val.toList.length

def Valley.width (val : Valley) := (val.getRow 0).length

def Char.desmudge (c : Char) : Char := match c with
  | '#' => '.'
  | '.' => '#'
  | _   => c

def desmudgeOpt (c : Option Char) : Char := match c with
  | some '#'  => '.'
  | some '.'  => '#'
  | _         => ' '

def Valley.desmudgeAt (val : Valley) (x y : Nat) : Valley :=
  let rowDesmudgeAt (i : Nat) : Option (List Char) → List Char
    | some row => row.set i (desmudgeOpt row[i]?)
    | none => []
  val.toList.set y (rowDesmudgeAt x val.toList[y]?)

-- Unnecessary
def Valley.findSmudgePos (val : Valley) : List (Nat × Nat) :=
  let origRefls := (val.transpose.locationsOfMirroring, val.locationsOfMirroring)
  let xys := (List.range val.width).product (List.range val.height)
  listOpt $ xys.map fun (x,y) =>
    let val' := val.desmudgeAt x y
    let newRefls := (val'.transpose.locationsOfMirroring, val'.locationsOfMirroring)
    if newRefls == origRefls then none else some (x,y)

def Valley.findSmudgePosAndLine' (val : Valley) : Many ((Nat × Nat) × (List Nat × List Nat)) := do
  let origRefls := (val.transpose.locationsOfMirroring, val.locationsOfMirroring)
  let (x,y) ← Many.ofList ((List.range val.width).product (List.range val.height))
  let val' := val.desmudgeAt x y
  let diffsX := val'.transpose.locationsOfMirroring.diff origRefls.1
  let diffsY := val'.locationsOfMirroring.diff origRefls.2
  if diffsX.length + diffsY.length = 0 then Many.none else pure ((x,y), (diffsX,diffsY))

def parseValley (data : String) : Valley := String.toList <$> data.trim.splitOn "\n"

def parseValleys (data : String) : List Valley := parseValley <$> data.trim.splitOn "\n\n"

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d13p1.txt").trim
  let valleys := parseValleys probInput
  IO.println ""
  let mut summary := 0
  for v in valleys do
    let desmRefl := v.findSmudgePosAndLine'.first.2
    summary := summary + 100 * desmRefl.2.sum + desmRefl.1.sum
  IO.println "\n"
  IO.println s!"Answer 2 (mirrorings with smudges) : {summary}"

--#eval main
