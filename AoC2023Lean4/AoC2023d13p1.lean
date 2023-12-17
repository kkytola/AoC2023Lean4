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
  listOpt $ (((List.range (as.length))).drop 1).map fun m =>
            if as.isMirroredAt m then some m else none

def Valley := List (List Char)
deriving Inhabited

def parseValley (data : String) : Valley := String.toList <$> data.trim.splitOn "\n"

def parseValleys (data : String) : List Valley := parseValley <$> data.trim.splitOn "\n\n"

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d13p1.txt").trim
  let valleys := parseValleys probInput
  let anss := valleys.map fun valley => 100 * valley.locationsOfMirroring.sum + valley.transpose.locationsOfMirroring.sum
  let ans := anss.sum
  IO.println s!"Answer 1 (mirrorings) : {ans}"

--#eval main
