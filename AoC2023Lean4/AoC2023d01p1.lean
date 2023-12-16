import AoC2023Lean4.AoC2023helpers
/-
1abc2
pqr3stu8vwx
a1b2c3d4e5f
treb7uchet
-/

def firstAndLastDigit (s : String) : String :=
  optChar (s.toList.find? Char.isDigit) ++ optChar (s.toList.reverse.find? Char.isDigit)

def main : IO Unit := do
  IO.println ((fun s => optNat (s.toNat?)) <$> firstAndLastDigit <$>
    (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d01p1.txt").splitOn "\n").sum

--#eval main
