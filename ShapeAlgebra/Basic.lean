/-
  The rules of the shape algebra, following the posts
  "Algebra for Polyominoes" and "Formula reduction for Polyominoes".
-/

/-! ## 1. Vocabulary -/

/-- Row or column. Used by strips, units, the push button and mirrors. -/
inductive Dir where
  | R | C
  deriving DecidableEq, Repr

/-- One step of a formula. A formula is a strip followed by a list of these. -/
inductive Op where
  | add    (d : Dir)  -- `+ 1_d`
  | sub    (d : Dir)  -- `- 1_d`
  | mirror (d : Dir)  -- `(·)^M_d`
  | push   (d : Dir)  -- `(·)_d`, the push button
  | pin               -- `(·)_P`
  deriving DecidableEq, Repr

open Dir Op

/-- A cell `(x, y)`. `x` grows to the right, `y` grows upwards. -/
abbrev Cell := Int × Int

/-- Everything a formula has to remember from one step to the next. -/
structure State where
  cells  : List Cell          -- the shape
  latch  : Dir                -- latch type: row or column
  pushed : Bool               -- button pressed and not yet used up by a ±1
  pin    : Option (List Cell) -- the pinned cells, once `(·)_P` has been used
  deriving DecidableEq, Repr

/-! ## 2. Lines -/

/-- The line of type `d` a cell sits on: a row is named by its `y`, a column by its `x`. -/
def lineOf : Dir → Cell → Int
  | R, (_, y) => y
  | C, (x, _) => x

/-- How far along that line the cell is: along a row that is `x`, along a column `y`. -/
def along : Dir → Cell → Int
  | R, (x, _) => x
  | C, (_, y) => y

/-- The cell on line `k` of type `d`, at position `a` along it. -/
def cellAt : Dir → Int → Int → Cell
  | R, k, a => (a, k)
  | C, k, a => (k, a)

/-- How many cells of `cs` are on line `k`. -/
def count (d : Dir) (cs : List Cell) (k : Int) : Nat :=
  (cs.filter (lineOf d · == k)).length

/-- Position of the far cell on line `k`: a row's rightmost cell, a column's topmost.
    `none` if the line has no cells. -/
def reach (d : Dir) (cs : List Cell) (k : Int) : Option Int :=
  ((cs.filter (lineOf d · == k)).map (along d)).max?

/-! ## 3. Shapes up to translation

Shapes are kept slid down to `x = 0`, `y = 0` and sorted, so two lists are equal
exactly when the shapes are the same. -/

def cellLe (a b : Cell) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

def insertCell (c : Cell) : List Cell → List Cell
  | [] => [c]
  | d :: ds => if cellLe c d then c :: d :: ds else d :: insertCell c ds

def sortCells : List Cell → List Cell
  | [] => []
  | c :: cs => insertCell c (sortCells cs)

/-- Slide the shape (and its pin, by the same amount) to the origin, then sort. -/
def normalize (s : State) : State :=
  match (s.cells.map (·.1)).min?, (s.cells.map (·.2)).min? with
  | some x0, some y0 =>
    let slide (cs : List Cell) := sortCells (cs.map fun (x, y) => (x - x0, y - y0))
    { s with cells := slide s.cells, pin := s.pin.map slide }
  | _, _ => s

/-! ## 4. The rules -/

/-- The cells that selection may look at: the pinned cells still present, or all of them. -/
def scope (s : State) : List Cell :=
  match s.pin with
  | none   => s.cells
  | some p => s.cells.filter (p.contains ·)

/-- The latched line. By default the topmost row / rightmost column (largest index).
    Right after a push: the line with the most cells, ties to the largest index. -/
def select (s : State) : Option Int := do
  let lines := (scope s).map (lineOf s.latch)
  if s.pushed then
    let n := count s.latch (scope s)
    let most ← (lines.map n).max?                  -- the largest number of cells on a line
    (lines.filter (n · == most)).max?              -- the largest index among those lines
  else
    lines.max?

/-- Where a unit of direction `u` goes: the line it travels along, and the position of
    the first cell it meets on that line. -/
def hit (s : State) (u : Dir) : Option (Int × Int) := do
  let k ← select s
  -- Unit and latch agree: travel along the latched line itself.
  -- They differ: travel along the line through the latched line's far cell,
  -- where the far cell is looked up among the pinned cells only.
  let line ← if s.latch = u then pure k else reach s.latch (scope s) k
  -- Landing uses the whole figure.
  let a ← reach u s.cells line
  pure (line, a)

/-- `M_R` flips top-to-bottom, `M_C` flips left-to-right. -/
def reflect : Dir → Cell → Cell
  | R, (x, y) => (x, -y)
  | C, (x, y) => (-x, y)

/-- One step. `none` means the step is undefined (nothing in scope to select). -/
def step (s : State) : Op → Option State
  | push d   => some { s with latch := d, pushed := true }
  | pin      => some { s with pin := some s.cells }
  | mirror d => some (normalize { s with cells := s.cells.map (reflect d),
                                         pin := s.pin.map (·.map (reflect d)) })
  | add u    => do
      let (line, a) ← hit s u
      pure (normalize { s with cells := cellAt u line (a + 1) :: s.cells, pushed := false })
  | sub u    => do
      let (line, a) ← hit s u
      pure (normalize { s with cells := s.cells.filter (· != cellAt u line a), pushed := false })

/-- `A_d^(j)`: a strip of `j` cells. It sets the latch type to `d`. -/
def strip (d : Dir) (j : Nat) : State :=
  normalize { cells := (List.range j).map fun (i : Nat) => cellAt d 0 i, latch := d, pushed := false, pin := none }

/-- Run a formula: start from the strip, apply the steps left to right. -/
def eval (d : Dir) (j : Nat) (w : List Op) : Option State :=
  w.foldlM step (strip d j)

def shapeOf (d : Dir) (j : Nat) (w : List Op) : Option (List Cell) :=
  (eval d j w).map (·.cells)

/-! ## 5. Pictures -/

/-- Read a picture, top row first: `pic ["##", "#."]`. -/
def pic (rows : List String) : List Cell :=
  let h : Int := rows.length
  let cells := rows.zipIdx.flatMap fun (row, i) =>
    (row.toList.zipIdx.filter (·.1 == '#')).map fun (_, x) => ((x : Int), h - 1 - i)
  (normalize { cells, latch := R, pushed := false, pin := none }).cells

/-- Draw a shape as text, top row first. -/
def render (cs : List Cell) : String :=
  let w := ((cs.map Prod.fst).max?.getD 0).toNat + 1
  let h := ((cs.map Prod.snd).max?.getD 0).toNat + 1
  "\n".intercalate <| (List.range h).reverse.map fun (y : Nat) =>
    String.ofList <| (List.range w).map fun (x : Nat) =>
      if cs.contains (x, y) then '#' else '.'

def draw (d : Dir) (j : Nat) (w : List Op) : String :=
  match shapeOf d j w with
  | some cs => render cs
  | none    => "(undefined)"

