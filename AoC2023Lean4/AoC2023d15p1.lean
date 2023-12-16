import AoC2023Lean4.AoC2023helpers
/-
rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7
-/

def String.holidayHash (s : String) : Int :=
  let rec hashStep (cur : Int) : List Char → Int
    | [] => cur
    | c :: cs => hashStep (((cur + c.toNat) * 17) % 256) cs
  hashStep 0 s.toList

def parseInitialization (data : String) : List String :=
  List.join ((·.splitOn ",") <$> data.trim.splitOn "\n")

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d15p1.txt").trim
  let initSeq := parseInitialization probInput
  let hashes := String.holidayHash <$> initSeq
  IO.println s!"Answer 1 (hash sum) : {hashes.sum}"

--#eval main
