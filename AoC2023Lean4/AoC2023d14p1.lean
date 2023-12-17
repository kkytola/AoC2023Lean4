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

def Platform := List (List Char)
deriving Inhabited

def Platform.toList (pf : Platform) : List (List Char) := pf

def Platform.transpose (pf : Platform) : Platform := pf.toList.transpose

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

def rowLoadings (row : List Char) : List Nat :=
  ((row.zip (List.range row.length)).filter (·.1 == 'O')).map fun ci =>
    row.length - ci.2

def Platform.WestLoading (pf : Platform) : Nat :=
  ((fun row => (rowLoadings row).sum) <$> pf.toList).sum

def Platform.northLoading (pf : Platform) : Nat := pf.transpose.WestLoading

def parsePlatform (data : String) : Platform := String.toList <$> data.trim.splitOn "\n"

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d14p1.txt").trim
  let platform := parsePlatform probInput
  IO.println ""
  let loading := platform.transpose.tiltWest.WestLoading
  IO.println s!"Answer 1 (loading) : {loading}"

--#eval main
