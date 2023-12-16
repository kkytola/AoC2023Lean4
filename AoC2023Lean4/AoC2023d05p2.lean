import AoC2023Lean4.AoC2023helpers
/-
seeds: 79 14 55 13

seed-to-soil map:
50 98 2
52 50 48

soil-to-fertilizer map:
0 15 37
37 52 2
39 0 15

fertilizer-to-water map:
49 53 8
0 11 42
42 0 7
57 7 4

water-to-light map:
88 18 7
18 25 70

light-to-temperature map:
45 77 23
81 45 19
68 64 13

temperature-to-humidity map:
0 69 1
1 0 69

humidity-to-location map:
60 56 37
56 93 4
-/

/-- An X-to-Y-map segment, with minimum and maximum x values it applies to, and the
minimum y value corresponding to the minimum x value. -/
structure XtoYeffSegment where
  minx : Nat
  maxx : Int
  miny : Nat

/-- An X-to-Y-map, consisting of segments that tell how given ranges of x values
are mapped to ranges of y values. -/
structure XtoYeff where
  segments : List XtoYeffSegment
deriving Inhabited

/-- A map segment that has an empty x range; never applies. -/
def impossibleSegment : XtoYeffSegment := {minx := 1, maxx := 0, miny := 0}

/-- Applying the function specified by an X-to-Y-map segment. -/
def applyXtoYeffSegment (seg : XtoYeffSegment) (x : Nat) : Option Nat := do
  if seg.minx ≤ x ∧ x ≤ seg.maxx
    then pure (seg.miny + (x - seg.minx))
    else none

/-- Applying the function specified by an X-to-Y-map, with value `none` if none
of the x ranges apply. -/
def applyXtoYeff' (xstoys : XtoYeff) (x : Nat) : Option Nat :=
  (listOpt (xstoys.segments.map (fun seg => applyXtoYeffSegment seg x)))[0]?

/-- Applying the function specified by an X-to-Y-map, with identity map applied
if none of the x ranges apply. -/
def applyXtoYeff (xstoys : XtoYeff) (x : Nat) : Nat :=
  match applyXtoYeff' xstoys x with
  | some y => y
  | none => x

/-- A segment of indices, with minimum index and length of the segment part of the data. -/
structure IndexSegment where
  minInd : Nat
  length : Nat

/-- The maximum index in an index segment. -/
def IndexSegment.maxInd (iseg : IndexSegment) : Int := -1 + iseg.minInd + iseg.length

instance : ToString IndexSegment where
  toString iseg := s!"[{iseg.minInd}..{iseg.maxInd}]"

/-- Breaking an index segment into (at most) two pieces at a specified index. -/
def IndexSegment.breakAt (iseg : IndexSegment) (b : Int) : Many IndexSegment :=
  if b < iseg.minInd ∨ iseg.maxInd < b then pure iseg
    else
      let first : IndexSegment := { iseg with length := (b - iseg.minInd).toNat }
      let second : IndexSegment := { minInd := b.toNat, length := iseg.length - first.length }
      Many.both (pure first) (pure second)

/-- Applying the function specified by an X-to-Y-map segment to an IndexSegment. -/
def applyXtoYeffToIndexSegment (xtoys : XtoYeff) (iseg : IndexSegment) : Many IndexSegment := do
  let pieces : Many IndexSegment :=
    Many.composeListMap (xtoys.segments.map
      (fun seg indSeg => indSeg.breakAt seg.minx >>= (·.breakAt seg.maxx))) iseg
  pieces.map (fun indSeg => { indSeg with minInd := applyXtoYeff xtoys indSeg.minInd })

/-- A number list parser. -/
def readNumbers (data : String) : List Nat :=
  listOpt $ String.toNat? <$> data.splitOn " "

/-- A parser for X-to-Y-map segments. -/
def parseXtoYeffSegment (segString : String) : XtoYeffSegment :=
  let parse := (readNumbers segString).take 3
  if parse.length < 3
    then impossibleSegment
    else { minx := optNum parse[1]?,
           maxx := (optNum parse[1]? + optNum parse[2]? : Nat) - 1,
           miny := optNum parse[0]?}

/-- A parser for X-to-Y-maps. -/
def parseXtoYeff (segString : String) : XtoYeff :=
  { segments := parseXtoYeffSegment <$> (segString.splitOn "\n").drop 1 }

/-- A parser for input: list of initial seeds and maps applied to it. -/
def parseInput (data : String) : List Nat × (List XtoYeff) :=
  let seedsAndMaps := data.splitOn "\n\n"
  let seeds : Option (List Nat) := do
    pure (readNumbers (← ((← seedsAndMaps[0]?).splitOn ": ")[1]?))
  let maps := parseXtoYeff <$> seedsAndMaps.drop 1
  (optList seeds, maps)

/-- A parser for input: list of ranges initial seeds and maps applied to it. -/
def parseInput' (data : String) : List IndexSegment × List XtoYeff :=
  let (isegdata, maps) := parseInput data
  (isegdata.toPairs.map (fun p => { minInd := p.1, length := p.2 }), maps)

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d05p1.txt").trim
  let (seeds', maps) := parseInput' probInput
  let seeds := Many.ofList seeds'
  let funcs := maps.map (fun mp => applyXtoYeffToIndexSegment mp)
  let final := seeds >>= Many.composeListMap funcs
  let minLoc := optNum (final.map (fun iseg => iseg.minInd)).toList.minimum?
  IO.println s!"Answer (minimum location) : {minLoc}"

--#eval main
