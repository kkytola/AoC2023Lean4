import AoC2023Lean4.AoC2023helpers
/-
O....#....
O.OO#....#
.....##...
OO.#O....O
.O.....O#.
O.#..O.#.#
..O..#O..O
.......O..
#....###..
#OO..#....
-/

def maxIterNum := 250
def desiredIterations := 1000000000

def Platform := List (List Char)
deriving Inhabited, BEq

def Platform.toList (pf : Platform) : List (List Char) := pf

def Platform.transpose (pf : Platform) : Platform := pf.toList.transpose

def Platform.mirrorNS (pf : Platform) : Platform := pf.toList.reverse

def Platform.mirrorEW (pf : Platform) : Platform := List.reverse <$> pf.toList

def Platform.getRow? (pf : Platform) (r : Nat) : Option (List Char) := pf.toList[r]?

def Platform.getRow (pf : Platform) (r : Nat) : List Char := optList (pf.getRow? r)

def Platform.height (pf : Platform) := pf.toList.length

def Platform.width (pf : Platform) := (pf.getRow 0).length

def pileOs (segment : List Char) : List Char :=
  let numOs := segment.count 'O'
  listRepeat numOs 'O' ++ listRepeat (segment.length - numOs) '.'

def rowTilt (row : List Char) : List Char :=
  ['#'].intercalate $ pileOs <$> row.splitOn '#'

def Platform.tiltWest (pf : Platform) : Platform := rowTilt <$> pf.toList

def Platform.tiltNorth (pf : Platform) : Platform := pf.transpose.tiltWest.transpose

def Platform.tiltSouth (pf : Platform) : Platform := pf.mirrorNS.tiltNorth.mirrorNS

def Platform.tiltEast (pf : Platform) : Platform := pf.mirrorEW.tiltWest.mirrorEW

def Platform.cycleNWSE (pf : Platform) : Platform :=
  pf.tiltNorth.tiltWest.tiltSouth.tiltEast

def rowLoadings (row : List Char) : List Nat :=
  ((row.zip (List.range row.length)).filter (·.1 == 'O')).map fun ci =>
    row.length - ci.2

def Platform.eastLoading (pf : Platform) : Nat :=
  ((fun row => (rowLoadings row).sum) <$> pf.toList).sum

def Platform.northLoading (pf : Platform) : Nat := pf.transpose.eastLoading

unsafe def iterateNWSE : List Platform → List Platform × Bool
  | [] => ([], false)
  | pf :: pfs =>
    let newpf := pf.cycleNWSE
    let flag : Bool := (pf :: pfs).contains newpf
    if pfs.length > maxIterNum ∨ flag
      then (newpf :: (pf :: pfs), flag)
      else iterateNWSE (newpf :: (pf :: pfs))

def parsePlatform (data : String) : Platform := String.toList <$> data.trim.splitOn "\n"

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d14p1.txt").trim
  let platform := parsePlatform probInput
  IO.println ""
  let (iterations, foundRepeated) := iterateNWSE [platform]
  let repeats := iterations.findIdxs (· == iterations[0]!)
  let period := repeats[1]! - repeats[0]!
  let untilStart := iterations.length - repeats[1]!
  let goodIndex := period - 1 - (((desiredIterations - untilStart) % period))
  let loading := (iterations[goodIndex]!).northLoading
  IO.println s!"Answer 2 (loading) : {loading}"

--#eval main
