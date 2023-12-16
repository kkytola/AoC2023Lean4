import Mathlib.Combinatorics.Composition


section OptionHandling -- Dirty.

def optString :  Option String → String
  | none => ""
  | some s => s

def optList {α : Type*} : Option (List α) → List α
  | none => []
  | some l => l

def listOpt {α : Type*} : List (Option α) → List α
  | [] => []
  | oa :: oas => match oa with
    | none => listOpt oas
    | some a => a :: listOpt oas
/-
def optNat : Option Nat → Nat
  | none => 0
  | some n => n
 -/
/-- TODO: Supercedes `optNat`, so remove the former. -/
def optNum {R : Type*} [Zero R] : Option R → R
  | none => 0
  | some x => x

def optChar (c : Option Char) : String := optString $ c.map Char.toString

end OptionHandling -- section


section List_helpers

/-- The list repeating a given list n times. -/
def List.repeat (l : List α) (n : Nat) : List α :=
  List.join $ ((fun _ => l) <$> List.range n)

/-- The list containing n times the same element a. -/
def listRepeat (n : Nat) (a : α) : List α :=
  (fun _ => a) <$> List.range n

/-- Auxiliary: The natural map `List (Reader α) → Reader (List α)`. -/
def readerList {α ρ : Type u} {m : Type u → Type v} [Monad m] [MonadReader ρ m] (lr : List (m α)) : m (List α) :=
  match lr with
  | [] => pure []
  | ra :: ras => do pure ((← ra) :: (← readerList ras))

/-- Applying a list of maps sequentially. -/
def applyAll {α : Type*} (funs : List (α → α)) (a : α) : α :=
  match funs with
  | [] => a
  | f :: fs => f (applyAll fs a)

/-- Split a list to consecutive, non-overlapping pairs. -/
def List.toPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | _ :: [] => []
  | a :: b :: as => (a, b) :: as.toPairs

/-- Get the list of consecutive pairs from a list (with overlaps). -/
def List.toConsecutivePairs {α : Type*} (l : List α) : List (α × α) :=
  l.zip (l.drop 1)

/-- The greatest common divisor of a list of natural numbers. -/
def List.gcd : List Nat → Nat
  | [] => 0
  | n :: [] => n
  | n :: rest => Nat.gcd n (rest.gcd)

/-- TODO: Redundant: this is `List.gcd` now. -/
def List.commonPeriod : List Nat → Nat
  | [] => 0
  | n :: [] => n
  | n :: rest => Nat.gcd n (rest.gcd)

/-- Applying a list of maps sequentially. -/
def applyAllTracing {α : Type*} (funs : List (α → α)) (a : α) : List α :=
  match funs with
  | [] => [a]
  | f :: fs =>
    let soFar := applyAllTracing fs a
    let foo := (soFar[0]? >>= some ∘ f) :: (some <$> soFar)
    listOpt foo

/-- Index of first difference in two lists. -/
def List.firstDiff? {α : Type*} [DecidableEq α] (L₁ L₂ : List α) : Option Nat :=
  let rec helper (A B : List α) (agree : Nat) : Option Nat :=
    match A, B with
    | [], [] => none
    | [], _ :: _ => some (agree + 1)
    | _ :: _, [] => some (agree + 1)
    | a :: as, b :: bs =>
      if a == b
        then helper as bs (agree + 1)
        else some (agree + 1)
  helper L₁ L₂ 0

/-- Index of first occurrence of a pattern in a list. -/
def List.findFirstPattern? {α : Type*} [DecidableEq α] (L : List α) (pat : List α) :
    Option Nat :=
  let aux : List (Option Nat) :=
            (((List.range L.length).map
              fun i => (L.drop i, i)).map
              fun si => (si.fst.firstDiff? pat, si.snd)).map
              fun oi => match oi.fst with
              | none => pure oi.snd
              | some c => if c > pat.length then pure oi.snd else none
  (listOpt aux)[0]?

/-- Index of first occurrence of any of multiple patterns in a list. -/
def List.findFirstOfPatterns? {α : Type*} [DecidableEq α] (L : List α) (pats : List (List α)) :
    Option Nat :=
  (listOpt (pats.map (fun pat => L.findFirstPattern? pat))).minimum?

/-- The list of pairs (i, j) of natural numbers 0 ≤ i < j < n. -/
def distinctNatPairs (n : Nat) : List (Nat × Nat) :=
  List.join $ ((List.range n).drop 1).map fun k => ((List.range k).map ((·, k)))

/-- The list of pairs (l(i), l(j)) with indices 0 ≤ i < j < n. -/
def List.distinctPairs {α : Type*} (l : List α) : List (α × α) :=
  let pairs'' := (distinctNatPairs l.length).map (fun (i,j) => (l[i]?, l[j]?))
  -- One could prove that there are no `none`s.
  listOpt $ pairs''.map fun ab => (do (← ab.1, ←ab.2))

/-- Run all monadic actions in a list. -/
def runList {m : Type u → Type v} {α : Type u} [Monad m] (as' : List (m α)) :
    m (List α) := do
  match as' with
  | []          => pure []
  | a' :: rest  => do pure ((← a') :: (← runList rest))

end List_helpers -- section


section Nat_helpers

/-- Distances between natural numbers (`ℕ`-valued, computable). -/
def natDist (n m : Nat) := (n - m) + (m - n)

/-- "Print" a natural number in a single character. -/
def Nat.toChar (n : Nat) : Char :=
  if (n > 9) then '#'
    else match (toString n).toList[0]? with
    | none => '.'
    | some c => c

def decimalNum (ds : List Nat) : Nat :=
  ((fun p => p.1 * p.2) <$> ds.reverse.zip ((List.range ds.length).map (10^·))).sum

end Nat_helpers -- section


section String_helpers

/-- Remove any copy of a given substring in a string. -/
def String.remove (orig rem : String) : String :=
  orig.replace rem ""

/-- Remove any copy of any of given substrings in a string. -/
def String.removeAny (orig : String) (rems : List String) : String :=
  let rec helper : List String → String → String
    | [], s => s
    | r :: rs, s => helper rs (s.remove r)
  helper rems orig

end String_helpers -- section


section Char_helpers

def Char.isNum (c : Char) : Bool := c.isAlphanum ∧ ¬c.isAlpha

def Char.toDigit (c : Char) : Nat := optNat c.toString.toNat?

end Char_helpers -- section


section Position

/-- A position on the grid: `x` and `y` coordinates. -/
structure Position where
  x : Nat
  y : Nat
deriving BEq, DecidableEq

instance : ToString Position := ⟨fun p => s!"⟨{p.x},{p.y}⟩"⟩

def Position.mkXY (x y : Nat) : Position := {x := x, y := y}

def Position.leLex (p q : Position) : Bool := p.y < q.y ∨ (p.y == q.y ∧ p.x ≤ q.x)

end Position -- section


section Counter

abbrev Counter := StateT Nat Id

def Counter.init : Counter Unit := do set 0

def Counter.incr : Counter Unit := do set ((← get) + 1)

def Counter.valFromInit {α : Type} (ca : Counter α) : α := (ca 0).fst

end Counter -- section


section Many

/-- A monad of lazily evaluated unordered bunches of things. -/
inductive Many (α : Type*) where
  | none
  | more : α → (Unit → Many α) → Many α

def Many.one (a : α) : Many α := .more a (fun _ => none)

def Many.both : Many α → Many α → Many α
  | none, bs => bs
  | more a as', bs => more a (fun _ => both (as' ()) bs)

def manyMany : Many (Many α) → Many α
  | Many.none         => Many.none
  | Many.more a' as'' => Many.both a' (manyMany (as'' ()))

def Many.bind {α β : Type*} (as : Many α) (f : α → Many β) : Many β :=
  match as with
  | none => none
  | more a as' => both (f a) (bind (as' ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

abbrev Many.map (as : Many α) (f : α → β) := f <$> as

def manyOfListMany (ml : List (Many α)) : Many α := match ml with
  | [] => .none
  | ma :: mas => .both ma (manyOfListMany mas)

def Many.ofList (l : List α) : Many α :=
  manyOfListMany (pure <$> l) -- Inefficient?

def Many.toList : Many α → List α
  | none => []
  | more a as' => a :: (as' ()).toList

instance [ToString α] : ToString (Many α) where
  toString as := s!"M{as.toList}"

def Many.isSingle : Many α → Bool
  | none => false
  | more _ as' => match as' () with
    | none => true
    | _ => false

def Many.find? (as : Many α) (p : α → Bool) : Option α :=
  match as with
  | none => Option.none
  | more a as' => if p a then some a else find? (as' ()) p

def Many.first? (as : Many α) : Option α := as.find? (fun _ => true)

def Many.first [Inhabited α] (as : Many α) : α := match as.first? with
  | some a => a
  | Option.none => default

def Many.composeListMap {α : Type*} (fs : List (α → Many α)) (a : α) : Many α :=
  match fs with
  | [] => pure a
  | f :: rest => f a >>= Many.composeListMap rest

def Many.count {α : Type*} : Many α → Nat
  | none => 0
  | more _ as' => (as' ()).count + 1

/-- Run all monadic actions in a Many. -/
def runMany {m : Type u → Type v} {α : Type u} [Monad m] (as' : Many (m α)) :
    m (Many α) := do
  match as' with
  | Many.none           => pure Many.none
  | Many.more a' rest'  => do
    let rest ← runMany $ rest' ()
    pure $ Many.more (← a') (fun _ => rest)

end Many -- section
