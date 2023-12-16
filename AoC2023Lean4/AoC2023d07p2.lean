import AoC2023Lean4.AoC2023helpers
/-
32T3K 765
T55J5 684
KK677 28
KTJJT 220
QQQJA 483
-/

def cardCharList := ['A', 'K', 'Q', 'J', 'T', '9', '8', '7', '6', '5', '4', '3', '2']

structure Card where
  val : Char
  prop : cardCharList.contains val

instance : BEq Card := ⟨fun a b => a.val == b.val⟩

instance : ToString Card := ⟨fun card => s!"⌈{card.val}⌉"⟩

def Card.value (card : Card) : Nat := 14 - optNum (cardCharList.indexOf card.val)
def Card.value' (card : Card) : Nat := if card.val == 'J' then 0 else card.value

def Card.le (a b : Card) : Bool := a.value' ≤ b.value'

instance : LE Card := ⟨fun a b => Card.le a b⟩

instance : DecidableRel (fun (a b : Card) => a ≤ b) := fun _ _ => Bool.decEq _ true

def Char.toCard? (c : Char) : Option Card :=
  if h : cardCharList.contains c
    then pure { val := c, prop := h }
    else none

def cardList : List Card := listOpt (Char.toCard? <$> cardCharList)

def Card.joker : Card := cardList[3]

def String.toCardList (s : String) : List Card := listOpt (Char.toCard? <$> s.toList)

def countCardOccurrences (cards : List Card) : List Nat :=
  cardList.map (fun refCard => cards.count refCard)

def countCardOccurrences' (cards : List Card) : List Nat × Nat :=
  ((cardList.filter (fun c => ¬(c == Card.joker))).map (fun refCard => cards.count refCard),
    cards.count Card.joker)

def countCardOccurrenceType (cards : List Card) : List Nat :=
  ((countCardOccurrences cards).filter (· ≠ 0)).mergeSort (· ≥ ·)

def countCardOccurrenceType' (cards : List Card) : List Nat :=
  let counts := countCardOccurrences' cards
  let aux := (counts.1.filter (· ≠ 0)).mergeSort (· ≥ ·)
  (optNum aux.maximum + counts.2) :: aux.drop 1

def listNatLE (ns ms : List Nat) : Bool := match ns, ms with
  | [], [] => true
  | _ :: _, [] => false
  | [], _ :: _ => true
  | n :: ns', m :: ms' =>
    if n < m then true
      else if m < n then false
      else listNatLE ns' ms'

instance : LE (List Nat) where
  le ns ms := listNatLE ns ms

instance : DecidableRel (fun (ns ms : List Nat) => ns ≤ ms) := fun _ _ => Bool.decEq _ true

structure Hand where
  cards : List Card
  five : cards.length = 5

def String.toHand? (s : String) : Option Hand :=
  if h : s.toCardList.length = 5
    then pure { cards := s.toCardList, five := h }
    else none

instance : ToString Hand where
  toString hand := "‹" ++ (String.intercalate " " (toString <$> hand.cards)) ++ "›"

inductive HandType
  | fiveOfKind
  | fourOfKind
  | fullHouse
  | threeOfKind
  | twoPairs
  | onePair
  | highCard
deriving BEq

def HandType.toString : HandType → String
  | fiveOfKind => "5-of-a-kind"
  | fourOfKind => "4-of-a-kind"
  | fullHouse => "full-house"
  | threeOfKind => "3-of-a-kind"
  | twoPairs => "two-pairs"
  | onePair => "one-pair"
  | highCard => "high-card"

instance : ToString HandType := ⟨HandType.toString⟩

def HandType.toMultiplicities : HandType → List Nat
  | fiveOfKind =>   [5,0,0,0,0]
  | fourOfKind =>   [4,1,0,0,0]
  | fullHouse =>    [3,2,0,0,0]
  | threeOfKind =>  [3,1,1,0,0]
  | twoPairs =>     [2,2,1,0,0]
  | onePair =>      [2,1,1,1,0]
  | highCard =>     [1,1,1,1,1]

open HandType in
def Hand.toHandType (hand : Hand) : HandType :=
  let tp := countCardOccurrenceType hand.cards
  if (optNum tp[0]? == 5) then fiveOfKind
    else if (optNum tp[0]? == 4) then fourOfKind
    else if (optNum tp[0]? == 3)
      then
        if (optNum tp[1]? == 2) then fullHouse
        else threeOfKind
    else if (optNum tp[0]? == 2)
      then
        if (optNum tp[1]? == 2) then twoPairs
        else onePair
    else highCard

instance : LE Hand where
  le H K :=
    let Ht := countCardOccurrenceType' H.cards
    let Kt := countCardOccurrenceType' K.cards
    let com : Bool := (Ht ≤ Kt) ∧
                      (Ht == Kt → (·.value') <$> H.cards ≤ (·.value') <$> K.cards)
    com

instance : DecidableRel (fun (H K : Hand) => H ≤ K) := fun _ _ => Bool.decEq _ true

structure HandBid where
  hand : Hand
  bid : Nat

instance : ToString HandBid where
  toString hb := s!"⟨{hb.1} : {hb.2}⟩"

instance : LE HandBid := ⟨fun HB KB => HB.hand ≤ KB.hand⟩

instance : DecidableRel (fun (HB KB : HandBid) => HB ≤ KB) := fun _ _ => Bool.decEq _ true

/-- Hand & bid list parser. -/
def parseInput (data : String) : List HandBid :=
  let aux := listOpt ( ((data.splitOn "\n").map (fun ln => ln.splitOn " ")).map (fun hb => do
    pure (← (optString hb[0]?).toHand?, ← (← hb[1]?).toNat?) ))
  (fun hb => { hand := hb.1, bid := hb.2}) <$> aux

def score (HB : List HandBid) : Nat :=
  let sz := ((HB.mergeSort (· ≤ ·)).zip (List.range HB.length))
  (sz.map (fun hbr => hbr.1.bid * (hbr.2 + 1))).sum

def main : IO Unit := do
  let probInput := (← IO.FS.readFile "./AoC2023Lean4/data-AoC2023d07p1.txt").trim
  IO.println s!"Answer (score) : {score (parseInput probInput)}"

--#eval main
