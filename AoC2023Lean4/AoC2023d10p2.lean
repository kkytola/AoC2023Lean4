import AoC2023Lean4.AoC2023helpers
import Mathlib.Tactic
/-
7-F7-
.FJ|7
SJLL7
|F--J
LJ.LJ
-/

inductive Quadrant where
  | NE
  | NW
  | SW
  | SE
deriving BEq, Inhabited

def Quadrant.toZMod : Quadrant → Int
  | NE => 0
  | NW => 1
  | SW => 2
  | SE => 3

def Quadrant.ofXY (x y : Int) : Quadrant :=
  if y < 0
    then
      if x < 0 then Quadrant.SW
      else Quadrant.SE
    else
      if x < 0 then Quadrant.NW
      else Quadrant.NE

def Quadrant.ofPoint (xy : Int × Int) : Quadrant := Quadrant.ofXY xy.1 xy.2

def Quadrant.stepAngle (p q : Quadrant) : Int :=
  match (q.toZMod - p.toZMod) % 4 with
  | 1 => 1
  | 3 => -1
  | _ => 0

def windingOfWalk' (walk : List (Int × Int)) : List (Int × Quadrant × Quadrant) :=
  ((Quadrant.ofPoint <$> walk).toConsecutivePairs.map fun qp => (Quadrant.stepAngle qp.1 qp.2, qp.1, qp.2))

def windingOfWalk (walk : List (Int × Int)) : Int :=
  ((Quadrant.ofPoint <$> walk).toConsecutivePairs.map fun qp => Quadrant.stepAngle qp.1 qp.2).sum

inductive Dir where
  | N
  | E
  | S
  | W
deriving BEq, Inhabited

open Dir in
def allDirections : List Dir := [N, E, S, W]

def Dir.backwards : Dir → Dir
  | N => S
  | E => W
  | S => N
  | W => E

def Dir.toStep : Dir → Int × Int
  | N => ( 0,  1)
  | E => ( 1,  0)
  | S => ( 0, -1)
  | W => (-1,  0)

abbrev Connection := Dir × Dir

open Dir in
def readTileType (c : Char) : Option Connection ⊕ Unit := match c with
  | 'S' => Sum.inr ()    -- animal starting position
  | '.' => Sum.inl none
  | '|' => Sum.inl (N,S)
  | '-' => Sum.inl (E,W)
  | 'L' => Sum.inl (N,E)
  | 'J' => Sum.inl (N,W)
  | '7' => Sum.inl (S,W)
  | 'F' => Sum.inl (E,S)
  | _ => Sum.inl none

def connectEntering (conn : Connection) (entry : Dir) : Option Dir :=
  if      conn.1.backwards == entry then  some conn.2
  else if conn.2.backwards == entry then  some conn.1
  else                                    none

structure Tile where
  x : Int
  y : Int
  conn : Option Connection
  anim : Bool := false

def Tile.mkOfRead (x y : Int) : Option Connection ⊕ Unit → Tile
  | .inl conn' => {x := x, y := y, conn := conn'}
  | .inr _ => {x := x, y := y, conn := none, anim := true}

def noneTile : Tile := { x := -1, y := -1, conn := none}

instance : Inhabited Tile := ⟨noneTile⟩

def optTile (ot : Option Tile) : Tile := match ot with
  | none => noneTile
  | some t => t

def PipeMaze := ReaderT (List (List Tile)) Id
deriving Monad, MonadReader

def animalPos (maze : List (List Tile)) : Option Tile := do
  for r in maze do
    for t in r do
      if t.anim then return t
  none

def PipeMaze.animal : PipeMaze (Option Tile) := do pure (animalPos (← read))

def PipeMaze.tileAt (x y : Int) : PipeMaze (Option Tile) := do
  let maze ← read
  pure do
    let row ← maze[y.toNat]? -- mildly dangerous but faster search
    let tile ← row[x.toNat]? -- mildly dangerous but faster search
    if tile.x == x ∧ tile.y == y then pure tile else none

def PipeMaze.tileInDir (x y : Int) (dir : Dir) : PipeMaze (Option Tile) :=
  let (dx, dy) := Dir.toStep dir
  tileAt (x+dx) (y+dy)

def PipeMaze.nbrsAt (x y : Int) : PipeMaze (List Tile) := do
  pure (listOpt (← readerList ((tileInDir x y ·) <$> allDirections)))

def PipeMaze.nbrsAt' (x y : Int) : PipeMaze (List Tile) :=
  readerList ((tileInDir x y ·) <$> allDirections) >>= fun lo => pure (listOpt lo)

def PipeMaze.connectedNbrsAt (x y : Int) : PipeMaze (List (Tile × Dir)) := do
  let nbrs ← readerList ((fun dir => tileInDir x y dir) <$> allDirections)
  let nbrsDir := (nbrs.zip allDirections).map fun otd => otd.1 >>= fun t => pure (t, otd.2)
  let passages : List (Option (Tile × Dir)) := (listOpt nbrsDir).map fun td =>
    td.1.conn >>= fun conn => connectEntering conn td.2 >>= fun _ => (td.1, td.2)
  pure (listOpt passages)

def PipeMaze.stepFromTileToDir (t : Tile) (dir : Dir) : PipeMaze (Option (Tile × Dir)) := do
  let nextTile' ← PipeMaze.tileInDir t.x t.y dir
  pure do
    let nextTile ← nextTile'
    let nextDir ← connectEntering (← nextTile.conn) dir
    pure (nextTile, nextDir)

unsafe def PipeMaze.walkFromTileToDir (start : Tile) (dir : Dir) : PipeMaze (List (Tile × Dir) × Bool) := do
  let env ← read -- Is this a bad way to use a reader monad?
  let rec helper (already : List (Tile × Dir)) (t : Tile) (d : Dir) : List (Tile × Dir) :=
    match PipeMaze.stepFromTileToDir t d env with
    | none => (t, d) :: already
    | some (t', d') => (helper ((t, d) :: already) t' d')
    -- The termination of this is actually unsafe (if env is arbitrary).
  let walk := (helper [] start dir).reverse
  let last := walk.getLast! -- Overkill to mark this as unsafe.
  let wanted := optTile (← PipeMaze.tileInDir last.1.x last.1.y last.2)
  pure ((helper [] start dir).reverse,
        wanted.x == start.x ∧wanted.y == start.y )

unsafe def PipeMaze.walkFromTileToDir' (start : Tile) (dir : Dir) : PipeMaze (List (Tile × Dir)) := do
  let env ← read -- Is this a bad way to use a reader monad?
  let rec helper (already : List (Tile × Dir)) (t : Tile) (d : Dir) : List (Tile × Dir) :=
    match PipeMaze.stepFromTileToDir t d env with
    | none => (t, d) :: already
    | some (t', d') => (helper ((t, d) :: already) t' d')
    -- The termination of this is actually unsafe (if env is arbitrary).
  pure (helper [] start dir).reverse

/-- A tile array parser. -/
def parseTiles (data : String) : List (List Tile) :=
  let rows := (data.splitOn "\n").reverse
  let rowsNumbered := rows.zip (List.range rows.length)
  let rowsAndColumnsNumbered := rowsNumbered.map fun rn =>
    ((rn.1.toList.zip (List.range rn.1.toList.length)).map fun cx =>
    (cx.1, cx.2, rn.2))
  rowsAndColumnsNumbered.map fun r => r.map fun c =>
    Tile.mkOfRead c.2.1 c.2.2 (readTileType c.1)

unsafe def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d10p1.txt").trim
  let tiles := parseTiles probInput
  let tilePile := List.join tiles
  IO.println ""
  IO.println s!"    total # of tiles : {tilePile.length}"
  let ani := optTile (PipeMaze.animal tiles)
  let owb : Option (List (Tile × Dir) × Bool) :=
    ((PipeMaze.walkFromTileToDir ani · tiles) <$> allDirections).find? (fun wb => wb.2)
  let loop : List (Tile × Dir) := optList (owb >>= fun wb => wb.1)
  let loop' := loop.map (fun td => (td.1.x, td.1.y)) ++ [(ani.x, ani.y)]
  let xyPile := tilePile.map fun t => (t.x, t.y)
  let xyPileWithoutLoop := xyPile.filter (fun xy => ¬(loop'.contains xy))
  let windings := windingOfWalk <$>
    xyPileWithoutLoop.map (fun xy => loop'.map (fun lxy => (lxy.1 - xy.1, lxy.2 - xy.2)))
  IO.println ""
  IO.println s!"Answer 1 (half loop length) : {loop.length / 2}"
  IO.println s!"Answer 2 (loop interior area) : {(windings.filter (· ≠ 0)).length}"

--#eval main
