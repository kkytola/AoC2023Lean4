import AoC2023Lean4.AoC2023helpers
/-
???.### 1,1,3
.??..??...?##. 1,1,3
?#?#?#?#?#?#?#? 1,3,1,6
????.#...#... 4,1,1
????.######..#####. 1,6,5
?###???????? 3,2,1
-/

inductive HotSpring
  | broken
  | operational
  | unknown
deriving BEq

def HotSpring.toChar : HotSpring → Char
  | broken      => '#'
  | operational => '.'
  | unknown     => '?'

def Char.toHotSpring? : Char → Option HotSpring
  | '#' => some .broken
  | '.' => some .operational
  | '?' => some .unknown
  | _   => none

instance : ToString HotSpring := ⟨(·.toChar.toString)⟩

def hsRowToString (sr : List HotSpring) : String :=
  String.join $ (sr.map fun h => h.toChar.toString)

def hsRowSlots (hsr : List HotSpring) : List Nat :=
  (List.range hsr.length).filter (hsr[·]? == some HotSpring.unknown)

def countKnownBroken (hsr : List HotSpring) : Nat :=
  ((List.range hsr.length).filter (hsr[·]? == some HotSpring.broken)).length

def hsRowToInfo (hsr : List HotSpring) : Option (List Nat) :=
  if hsr.any (· == .unknown) then none
    else some $ String.length <$>
          ((hsRowToString hsr).splitOn ".").filter (¬ · == "")

unsafe def binomialLists (n k : Nat) : List (List Nat) :=
  if k > n then []
    else if k == 0 then [[]]
    else if k == n then [List.range n] -- maybe a tiny inefficiency mitigation?
    else List.join $ (List.range (n + 1 - k)).map fun j =>
          (binomialLists (n - 1 -j) (k - 1)).map fun rest =>
          j :: ((1 + j + ·) <$> rest)

unsafe def List.binomialSublists {α : Type*} [Inhabited α] (l : List α) (k : Nat) : List (List α) :=
  (binomialLists l.length k).map fun blist => (blist.map fun i => l[i]!)

def hsRowPlaceBrokens (hsr : List HotSpring) (br : List Nat) : List HotSpring :=
  let withBrokens := List.foldr (fun b => (·.set b .broken)) hsr br
  withBrokens.map (fun hs => if hs == .unknown then .operational else hs)

unsafe def hsRowTryPlacements (hsr : List HotSpring) (k : Nat) : List (List HotSpring) :=
  ((hsRowSlots hsr).binomialSublists k).map fun trial => hsRowPlaceBrokens hsr trial

unsafe def hsRowAllowedPlacements (hsr : List HotSpring) (info : List Nat) : List (List HotSpring) :=
  (hsRowTryPlacements hsr (info.sum - countKnownBroken hsr)).filter fun trialHSR =>
    hsRowToInfo trialHSR == some info

/-- A hot spring row and info parser. -/
def parseHotSpringRow (srdata : String) : List HotSpring × List Nat :=
  (fun s => ( listOpt $ Char.toHotSpring? <$> (optString s[0]?).toList,
              optNum <$> (String.toNat? <$> (optString s[1]?).splitOn ",") ))
    $ srdata.splitOn " "

/-- A full input parser for the hot springs problem. -/
def parseHotSprings (data : String) : List (List HotSpring × List Nat) :=
   parseHotSpringRow <$> data.splitOn "\n"

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d12p1.txt").trim
  let hss := parseHotSprings probInput
  let sna := (hss.map fun hsri => (hsRowAllowedPlacements hsri.1 hsri.2).length).sum
  IO.println s!"Answer (sum of numbers of arrangements) : {sna}"

--#eval main
