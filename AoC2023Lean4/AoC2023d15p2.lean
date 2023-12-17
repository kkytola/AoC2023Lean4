import AoC2023Lean4.AoC2023helpers
/-
rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7
-/

def String.holidayHash (s : String) : Int :=
  let rec hashStep (cur : Int) : List Char → Int
    | [] => cur
    | c :: cs => hashStep (((cur + c.toNat) * 17) % 256) cs
  hashStep 0 s.toList

inductive LensOper where
  | removal : String → LensOper
  | addition : String → Nat → LensOper

def LensOper.hasHash (hash : Int) : LensOper → Bool
  | removal lab => lab.holidayHash == hash
  | addition lab _ => lab.holidayHash == hash

def initializationStepToLensOper (step : String) : Option LensOper :=
  let label := step.takeWhile (fun c => c.isAlpha)
  match (step.drop label.length).take 1 with
  | "-" => some (.removal label)
  | "=" => do some (.addition label (← (step.drop (label.length + 1)).toNat?))
  | _ => none

def initializationStepToLabel (step : String) : String :=
  step.takeWhile (fun c => c.isAlpha)

def boxAddition (label : String) (flen : Nat) (box : List (String × Nat)) : List (String × Nat) :=
  let sameLabel := box.findIdx? (·.1 == label)
  match sameLabel with
  | none => (label, flen) :: box
  | some idx => box.set idx (label, flen)

def boxRemoval (label : String) (box : List (String × Nat)) : List (String × Nat) :=
  let sameLabel := box.findIdx? (·.1 == label)
  match sameLabel with
  | none => box
  | some idx => box.removeNth idx

def LensOper.operateInBox : LensOper → List (String × Nat) → List (String × Nat)
  | .removal lab => boxRemoval lab
  | .addition lab foclen => boxAddition lab foclen

def lensesFocusingPower (lenses : List Nat) : Nat :=
  List.sum $ (fun ab => ab.1 * ab.2) <$> (lenses.zip ((· + 1) <$> List.range lenses.length))

def parseInitialization (data : String) : List String :=
  List.join ((·.splitOn ",") <$> data.trim.splitOn "\n")

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d15p1.txt").trim
  let initSeq := parseInitialization probInput
  let opers' := listOpt (initializationStepToLensOper <$> initSeq)
  let listCIs := (List.range 256).map fun i => (Char.ofNat i, i)
  let opersB := listCIs.map fun ci => opers'.reverse.filter (fun ho => ho.hasHash ci.1.toNat)
  let finalB := List.reverse <$>
                (opersB.map fun bol => applyAll (LensOper.operateInBox <$> bol) [])
  let focusingB := finalB.map fun labslens => (lensesFocusingPower $ (·.2) <$> labslens)
  let focusing := List.sum $
    (focusingB.zip ((· + 1) <$> List.range listCIs.length)).map (fun ab => ab.1 * ab.2)
  IO.println s!"Answer 2 (focusing power) : {focusing}"

--#eval main
