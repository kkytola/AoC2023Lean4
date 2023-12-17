import AoC2023Lean4.AoC2023helpers
/-

.|...\....
|.=.\.....
.....|=...
........|.
..........
.........\
..../.\\..
.=.=/..|..
.|....=|.\
..//.|....

>|<<<\....
|v=.\^....
.v...|=>>>
.v...v^.|.
.v...v^...
.v...v^..\
.v../2\\..
<=>=/vv|..
.|<<<2=|.\
.v//.|.v..

-/

inductive Tile where
  | empty
  | slash
  | backslash
  | horiz
  | vert

def Char.toTile : Char → Tile
  | '/'   => .slash
  | '\\'  => .backslash
  | '-'   => .horiz
  | '|'   => .vert
  | _     => .empty

def Grid := List (List Tile)

def Grid.rows (grid : Grid) : List (List Tile) := grid

def Grid.height (grid : Grid) : Nat := grid.rows.length

def Grid.width (grid : Grid) : Nat := (optList grid.rows[0]?).length

def Grid.tileAt? (grid : Grid) (x y : Int) : Option Tile :=
  if x < 0 ∨ y < 0 then none
    else grid.rows[y.toNat]? >>= fun row => row[x.toNat]?

inductive Dir where
  | left
  | right
  | up
  | down
deriving BEq

/-- The grid stored in a read only state. -/
def Contraption := ReaderT Grid Id
deriving Monad, MonadReader

/-- The grid stored in a read only state and . -/
def ContraptionWithBeams := StateT ((Int × Int) → List Dir) Contraption
deriving Monad, MonadState

instance : MonadReader Grid ContraptionWithBeams where
  read := do pure (← StateT.lift (do pure (← read)))

/-- Create just a grid without any beams. -/
def noBeams {α : Type} (contr : Contraption α) : ContraptionWithBeams α := do
  MonadState.set (fun _ => [])
  pure (← StateT.lift contr)

/-- Try to create a single new beam, but discard if it exists already or is outside of the grid. -/
def createBeam (x y : Int) (dir : Dir) : ContraptionWithBeams (Many ((Int × Int) × Dir)) := do
  let grid ← read
  let beams ← get
  if ¬ (x < grid.width ∧ y < grid.height) ∨ (beams (x, y)).contains dir
    then pure (Many.none)
    else
      MonadState.set (Function.update beams (x, y) (dir :: beams (x, y)))
      pure (pure ((x, y), dir))

def beamAdvance (x y : Int) (dir : Dir) : ContraptionWithBeams (Many ((Int × Int) × Dir)) := do
  let grid ← read
  match grid.tileAt? x y with
  | none    => pure Many.none
  | some t  => match dir with
    | .right  => match t with
      | .slash      => createBeam x (y - 1) .up     -- reflect up
      | .backslash  => createBeam x (y + 1) .down   -- reflect down
      | .vert       => do pure $ Many.both          -- split |
                                (← createBeam x (y - 1) .up)
                                (← createBeam x (y + 1) .down)
      | _           => createBeam (x + 1) y .right  -- continue to the right
    | .left  => match t with
      | .slash      => createBeam x (y + 1) .down   -- reflect down
      | .backslash  => createBeam x (y - 1) .up     -- reflect up
      | .vert       => do pure $ Many.both          -- split |
                                (← createBeam x (y - 1) .up)
                                (← createBeam x (y + 1) .down)
      | _           => createBeam (x - 1) y .left   -- continue to the left
    | .up  => match t with
      | .slash      => createBeam (x + 1) y .right  -- reflect right
      | .backslash  => createBeam (x - 1) y .left   -- reflect left
      | .horiz      => do pure $ Many.both          -- split =
                                (← createBeam (x + 1) y .right)
                                (← createBeam (x - 1) y .left)
      | _           => createBeam x (y - 1) .up     -- continue up
    | .down  => match t with
      | .slash      => createBeam (x - 1) y .left   -- reflect left
      | .backslash  => createBeam (x + 1) y .right  -- reflect right
      | .horiz      => do pure $ Many.both          -- split =
                                (← createBeam (x + 1) y .right)
                                (← createBeam (x - 1) y .left)
      | _           => createBeam x (y + 1) .down   -- continue down

def beamsAdvance (bs : Many ((Int × Int) × Dir)) :
    ContraptionWithBeams (Many ((Int × Int) × Dir)) := do
  pure $ manyMany (← runMany $ bs.map fun b => beamAdvance b.1.1 b.1.2 b.2)

def keepAdvancing (steps : Nat) (bs : Many ((Int × Int) × Dir)) :
    ContraptionWithBeams (Many ((Int × Int) × Dir)) := match steps with
  | 0     => pure Many.none
  | s + 1 => do
    let advancedBeams ← beamsAdvance bs
    match advancedBeams with
    | Many.none     => pure Many.none
    | Many.more _ _ => keepAdvancing s advancedBeams

def countEnergized : ContraptionWithBeams Nat := do
  let grid ← read
  let beams ← get
  pure $  List.sum $ (List.range grid.height).map  fun y =>
          List.sum $ (List.range grid.width).map   fun x =>
                      if (beams (x, y)).length > 0 then 1 else 0

def parseGrid (data : String) : Grid :=
  (String.toList <$> data.trim.splitOn "\n").map fun row => (Char.toTile <$> row)

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d16p1.txt").trim
  let grid := parseGrid probInput
  let allEntrances :=
    ((List.range grid.width).map fun x => createBeam x 0 .down) ++
    ((List.range grid.width).map fun x => createBeam x (grid.height - 1) .up) ++
    ((List.range grid.height).map fun y => createBeam 0 y .right) ++
    ((List.range grid.height).map fun y => createBeam (grid.width - 1) y .left)
  let energizations := (allEntrances.map fun entr =>
    entr >>= fun bs => keepAdvancing 5000 bs >>= fun _ => countEnergized).map fun ene =>
    (ene default grid).1
  let maxEnergization := energizations.maximum?
  IO.println s!"Answer 2 (max energization) : {maxEnergization}"

--#eval main
