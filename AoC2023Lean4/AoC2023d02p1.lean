import AoC2023Lean4.AoC2023helpers
/-
Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green
-/

/-- The type of colors of cubes (red, green, or blue). -/
inductive Color where
  | red
  | green
  | blue
deriving BEq

def readColor? : String → Option Color
  | "red" => some Color.red
  | "green" => some Color.green
  | "blue" => some Color.blue
  | _ => none

/-- A round consists of numbers of cubes of different colors drawn. -/
def Round := Color → Nat

def Round.mkRGB (r g b : Nat) : Round
  | Color.red => r
  | Color.green => g
  | Color.blue => b

open Color in
instance : LE Round where
  le a b := ((a red ≤ b red) ∧ (a green ≤ b green) ∧ (a blue ≤ b blue) : Bool)

instance : DecidableRel (fun (a b : Round) => a ≤ b) := fun _ _ => Bool.decEq (decide _) true

/-- The elf's hypothetical bag has 12 red, 13 green, and 14 blue cubes. -/
def hypotheticalBag : Round := Round.mkRGB 12 13 14

/-- Would the round have been possible with the hypothetical bag? -/
def Round.possible (rnd : Round) : Bool := rnd ≤ hypotheticalBag

/-- A game has an ID and a number of rounds. -/
structure Game where
  id : Nat
  rounds : List Round

/-- Would the game have been possible with the hypothetical bag? -/
def Game.possible (game : Game) : Bool := game.rounds.all (·.possible)

/-- Reads the game ID from a string of the form `"Game ID"`. -/
def readGameId? (idStr : String) : Option Nat := do
  (← (idStr.splitOn " ").getLast?).toNat?

def readColorCount? (colCountStr : String) : Option (Color × Nat) := do
  let colCountStr' := colCountStr.splitOn " "
  (← readColor? (← colCountStr'[1]?), ← String.toNat? (← colCountStr'[0]?))

/-- Reads the round information from a string of the form `"R red, G green, B blue"`
(in any order of colors and with possible omissions of colors). -/
def readRound (rndStr : String) : Round :=
  let rndData := listOpt (readColorCount? <$> rndStr.splitOn ", ")
  let redCount : Option Nat := do (← rndData.find? (fun cc => cc.fst == Color.red)).snd
  let greenCount : Option Nat := do (← rndData.find? (fun cc => cc.fst == Color.green)).snd
  let blueCount : Option Nat := do (← rndData.find? (fun cc => cc.fst == Color.blue)).snd
  Round.mkRGB (optNum redCount) (optNum greenCount) (optNum blueCount)

/-- Parses the game data from a string of the form `"Game ID: RND1; RND2; ...; RNDx"`. -/
def readGame (dat : String) : Game := by
  let dat' := dat.splitOn ": "
  exact { id := optNum (readGameId? (optString dat'[0]?)),
          rounds := readRound <$> (optString dat'[1]?).splitOn "; " }

def main : IO Unit := do
  let games := readGame <$> (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d02p1.txt").trim.splitOn "\n"
  let sum := List.sum (games.map (fun game => if game.possible then game.id else 0))
  IO.println s!"Answer (sum of IDs of possible games) : {sum}"

--#eval main
