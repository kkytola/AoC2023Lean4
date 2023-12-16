import AoC2023Lean4.AoC2023helpers
/-
Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11
-/

def readNumbers (data : String) : List Nat :=
  listOpt $ String.toNat? <$> data.splitOn " "

def splitWinningChosen (data : String) : List Nat × List Nat :=
  let wc := (·.splitOn "|") <$> (data.splitOn ":")
  (readNumbers $ optString (wc[1]? >>= (·[0]?)), readNumbers $ optString (wc[1]? >>= (·[1]?)))

def hitCounter (targets data : List Nat) : Counter Nat := do
  for t in targets do
    if data.contains t then Counter.incr
  pure (← get)

def countHits (targets data : List Nat) : Nat := (hitCounter targets data).valFromInit

def winOfHits (hits : Nat) : Nat :=
  if hits == 0 then 0 else 2^(hits-1)

unsafe def multiplicitiesOfHits (hits : List Nat) : List Nat :=
  let rec helper (mhsMs : List (Nat × Nat) × (List Nat)) : List Nat :=
    match mhsMs.fst with
    | [] => mhsMs.snd
    | mh :: mhs' =>
      let ms' := mh.fst :: mhsMs.snd
      let mhs'' := (List.range mhs'.length).map (fun i =>
                    if i < mh.snd then (mhs'[i]!.fst + mh.fst, mhs'[i]!.snd) else mhs'[i]!)
      helper (mhs'', ms')
  (helper ((((fun _ => 1) <$> List.range hits.length).zip hits), []))

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d04p1.txt").trim.splitOn "\n"
  let rawhits := (fun (w,c) => countHits w c) <$> splitWinningChosen <$> probInput
  let totalCards := (multiplicitiesOfHits rawhits).sum
  IO.println s!"Answer (total copies) : {totalCards}"

--#eval main
