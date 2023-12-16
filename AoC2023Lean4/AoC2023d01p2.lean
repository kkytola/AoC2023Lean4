import AoC2023Lean4.AoC2023helpers
/-
two1nine
eightwothree
abcone2threexyz
xtwone3four
4nineeightseven2
zoneight234
7pqrstsixteen
-/

def digitsDigits : List (String × Nat) :=
  [ ("0", 0),
    ("1", 1),
    ("2", 2),
    ("3", 3),
    ("4", 4),
    ("5", 5),
    ("6", 6),
    ("7", 7),
    ("8", 8),
    ("9", 9) ]

def digitsSpelled : List (String × Nat) :=
  [ ("one",   1),
    ("two",   2),
    ("three", 3),
    ("four",  4),
    ("five",  5),
    ("six",   6),
    ("seven", 7),
    ("eight", 8),
    ("nine",  9) ]

def digitsAny := digitsDigits ++ digitsSpelled

def digitsAnyRev := digitsAny.map (fun p =>
  (String.join $ Char.toString <$> p.1.toList.reverse, p.2))

def firstAndLastDigit' (s : String) : Nat × Nat :=
  let first : Option Nat := do
    let pos ← s.toList.findFirstOfPatterns? ((·.fst.toList) <$> digitsAny)
    let rest := s.toList.drop pos
    (listOpt $ digitsAny.map (fun si =>
                if (si.fst.toList == rest.take si.fst.length)
                  then some si.snd else none))[0]?
  let last : Option Nat := do
    let pos ← s.toList.reverse.findFirstOfPatterns? ((·.fst.toList) <$> digitsAnyRev)
    let rest := s.toList.reverse.drop pos
    (listOpt $ digitsAnyRev.map (fun si =>
                if (si.fst.toList == rest.take si.fst.length)
                  then some si.snd else none))[0]?
  (optNum first, optNum last)

def combineDigits (dd : Nat × Nat) : Nat := 10 * dd.fst + dd.snd

def main : IO Unit := do
  IO.println ((combineDigits <$> firstAndLastDigit' <$>
    (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d01p2.txt").splitOn "\n")).sum

--#eval main
