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

def Tile.toChar : Tile → Char
  | .empty      => '.'
  | .slash      => '/'
  | .backslash  => '\\'
  | .horiz      => '='
  | .vert       => '|'

def Char.toTile : Char → Tile
  | '/'   => .slash
  | '\\'  => .backslash
  | '-'   => .horiz
  | '|'   => .vert
  | _     => .empty

instance : ToString Tile := ⟨(·.toChar.toString)⟩

def Grid := List (List Tile)

def Grid.rows (grid : Grid) : List (List Tile) := grid

def Grid.height (grid : Grid) : Nat := grid.rows.length

def Grid.width (grid : Grid) : Nat := (optList grid.rows[0]?).length

def Grid.tileAt? (grid : Grid) (x y : Int) : Option Tile :=
  if x < 0 ∨ y < 0 then none
    else grid.rows[y.toNat]? >>= fun row => row[x.toNat]?

def Grid.toString (grid : Grid) : String :=
  "\n".intercalate $ (grid.rows.map fun row => "".intercalate (row.map (·.toChar.toString)))

instance : ToString Grid := ⟨Grid.toString⟩

inductive Dir where
  | left
  | right
  | up
  | down
deriving BEq

def Dir.toChar : Dir → Char
  | .left   => '<'
  | .right  => '>'
  | .up     => '^'
  | .down   => 'v'

instance : ToString Dir := ⟨(·.toChar.toString)⟩

def LocalBeams := List Dir

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
  | 0     => beamsAdvance bs
  | s + 1 => do keepAdvancing s (← beamsAdvance bs)

def localBeamsToChar : List Dir → Char
  | []        => '.'
  | d :: drs  => match drs with
    | []      => d.toChar
    | _ :: _  => (drs.length + 1).toChar

def displayBeams : ContraptionWithBeams String := do
  let grid ← read
  let beams ← get
  pure $  "\n".intercalate  $ (List.range grid.height).map  fun y =>
          "".intercalate    $ (List.range grid.width).map   fun x =>
                              (localBeamsToChar (beams (x, y))).toString

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
  let one := createBeam 0 0 .right
  let plenty : ContraptionWithBeams (Many ((ℤ × ℤ) × Dir)) :=
    one >>= fun bs => keepAdvancing 1000 bs
  let energized := ((plenty >>= fun _ => countEnergized) default grid).1
  IO.println s!"Answer 1 (energized) : {energized}"

--#eval main
