import AoC2023Lean4.AoC2023helpers
import Mathlib.Tactic.Zify
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic
/-
Time:      7  15   30
Distance:  9  40  200

->

Time:      71530
Distance:  940200
-/

structure Race where
  time : Nat
  record : Nat

instance : ToString Race where
  toString r := s!"[TIME:{r.time}, REC:{r.record}]"

/-- Product of `speed := holdTime` and `remainingTime := raceTime - holdTime`. -/
def holdTimeToDistance (raceTime holdTime : Nat) : Nat :=
  (raceTime - holdTime) * holdTime

/-- Hold times that beat the record in a race. -/
def winningOptions (race : Race) : List Nat :=
  (List.range (race.time + 1)).filter (fun hold => holdTimeToDistance race.time hold > race.record)

def upToEven (n : Nat) : Nat := if Even n then n else n + 1
def downToEven (n : Nat) : Nat := if Even n then n else n - 1

/-
    0 < (t-x)*x - r
      = tx - x² - r
      = -(x-t/2)² + t²/4 - r

    |x-t/2|² < t²/4 - r

    |x-t/2| < sqrt( t²/4 - r )
-/
def numberOfWinningOptions (race : Race) : Nat :=
  have twoWidth := Nat.sqrt (race.time^2 - 4 * race.record - 1)
  (1 + (downToEven (race.time + twoWidth))/2 - (upToEven (race.time - twoWidth))/2)

/-- A number list parser. -/
def readNumbers (data : String) : List Nat :=
  listOpt $ String.toNat? <$> data.splitOn " "

/-- Race list parser. -/
def parseInput (data : String) : List Race :=
  let lines := (fun ln => readNumbers $ optString (ln.splitOn ":")[1]?) <$> data.splitOn "\n"
  if h : lines.length < 2
    then []
    else (fun p => { time := p.1, record := p.2 }) <$>
          (lines[0]'(by linarith)).zip (lines[1]'(by linarith))

/-- Race list parser. -/
def parseOneInput (data : String) : List Race :=
  let lines := (fun ln => optString (ln.splitOn ":")[1]?) <$> data.splitOn "\n"
  let readLines := lines.map (fun ln => (fun s => [optNum s.toNat?]) $ String.join $ Char.toString <$> (ln.toList.filter (·≠' ')))
  if h : readLines.length < 2
    then []
    else (fun p => { time := p.1, record := p.2 }) <$>
          (readLines[0]'(by linarith)).zip (readLines[1]'(by linarith))

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d06p1.txt").trim
  let ans := (numberOfWinningOptions <$> (parseOneInput probInput)).prod
  IO.println s!"Answer (number of winning options) : {ans}"

--#eval main
