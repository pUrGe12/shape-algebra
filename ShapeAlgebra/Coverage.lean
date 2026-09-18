import ShapeAlgebra.Conjecture
import ShapeAlgebra.Data.Table1
import ShapeAlgebra.Data.Table2
import ShapeAlgebra.Data.Table3
import ShapeAlgebra.Data.Table4
import ShapeAlgebra.Data.Table5
import ShapeAlgebra.Data.Table6
import ShapeAlgebra.Data.Table7
import ShapeAlgebra.Data.BlockedTable

/-!
# Item 3: coverage, one size at a time

Each table lists shapes with a formula for each. Lean checks, for every row, that the
shape is a genuine polyomino (in one piece, no repeated cells, slid to the origin), that
the formula builds exactly that shape, and that no two rows hold the same shape.

The tables for 1–7 cells have 1, 2, 6, 19, 63, 216 and 760 rows. Those are the known
numbers of fixed polyominoes of each size (OEIS A001168, which our own enumeration in
python/peel.py reproduces), so these tables contain every polyomino with up to 7 cells.
That last step, "the known count is right", is the one fact taken from outside Lean.
-/

open Dir Op

/-! ## A trustworthy "in one piece" check -/

theorem Path.symm {S : Cell → Prop} {a b : Cell} (h : Path S a b) : Path S b a := by
  induction h with
  | here ha => exact .here ha
  | next hab hc hadj ih =>
    exact Path.trans (.next (.here hc) (Path.start ih) hadj.symm) ih

/-- Everything `grow` collects is reachable from where it started. -/
theorem grow_reaches {all : List Cell} {a : Cell} :
    ∀ (n : Nat) (comp : List Cell), (∀ x ∈ comp, Path (· ∈ all) a x) →
      ∀ y ∈ grow all n comp, Path (· ∈ all) a y := by
  intro n
  induction n with
  | zero => intro comp h y hy; exact h y hy
  | succ n ih =>
    intro comp h
    apply ih
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact h y hy
    · simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
        decide_eq_true_eq] at hy
      obtain ⟨hy, -, x, hx, hadj⟩ := hy
      exact .next (h x hx) hy hadj

def connectedB : List Cell → Bool
  | [] => true
  | a :: rest => (a :: rest).all ((grow (a :: rest) (a :: rest).length [a]).contains ·)

theorem connectedB_sound {cs : List Cell} (h : connectedB cs = true) : Connected (· ∈ cs) := by
  match cs, h with
  | [], _ => intro a b ha; simp at ha
  | a :: rest, h =>
    simp only [connectedB, List.all_eq_true, List.contains_iff_mem] at h
    have from_a : ∀ y ∈ a :: rest, Path (· ∈ a :: rest) a y := fun y hy =>
      grow_reaches _ [a] (by intro x hx; simp at hx; subst hx; exact .here (by simp)) y (h y hy)
    intro x y hx hy
    exact Path.trans (from_a x hx).symm (from_a y hy)

/-! ## Checking a table -/

abbrev Row := List Cell × Dir × Nat × List Op

def noSub (w : List Op) : Bool := w.all fun | sub _ => false | _ => true

/-- One row: a genuine `n`-cell polyomino, built by its formula. -/
def rowOK (n : Nat) (addOnly : Bool) : Row → Bool
  | (cs, d, j, w) =>
    cs.length == n && decide cs.Nodup && (normalize ⟨cs, R, false, none⟩).cells == cs &&
    connectedB cs && shapeOf d j w == some cs && (!addOnly || noSub w)

def tableOK (n : Nat) (addOnly : Bool) (tbl : List Row) : Bool :=
  tbl.all (rowOK n addOnly) && decide (tbl.map (·.1)).Nodup

/-! ## The checks -/

theorem table1_ok : tableOK 1 true table1 = true := by decide +kernel
theorem table2_ok : tableOK 2 true table2 = true := by decide +kernel
theorem table3_ok : tableOK 3 true table3 = true := by decide +kernel
theorem table4_ok : tableOK 4 true table4 = true := by decide +kernel
theorem table5_ok : tableOK 5 true table5 = true := by decide +kernel
theorem table6_ok : tableOK 6 true table6 = true := by decide +kernel
theorem table7_ok : tableOK 7 true table7 = true := by decide +kernel

theorem table_sizes :
    [table1.length, table2.length, table3.length, table4.length, table5.length, table6.length,
     table7.length] = [1, 2, 6, 19, 63, 216, 760] := by decide +kernel

/-! ## What the checks mean -/

theorem buildable_of_shapeOf {d : Dir} {j : Nat} {w : List Op} {cs : List Cell}
    (h : shapeOf d j w = some cs) : Buildable (· ∈ cs) := by
  simp only [shapeOf, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨d, j, w, t, 0, 0, ht, fun x => by simp⟩

theorem rowOK_spec {n : Nat} {addOnly : Bool} {r : Row} (h : rowOK n addOnly r = true) :
    shapeOf r.2.1 r.2.2.1 r.2.2.2 = some r.1 ∧ r.1.length = n ∧
      (addOnly = true → noSub r.2.2.2 = true) := by
  obtain ⟨cs, d, j, w⟩ := r
  simp only [rowOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hn, -⟩, -⟩, -⟩, hb⟩, hs⟩ := h
  refine ⟨hb, hn, fun ha => ?_⟩
  rcases hs with hs | hs
  · simp [ha] at hs
  · exact hs

theorem rows_of_tableOK {n : Nat} {addOnly : Bool} {tbl : List Row} (h : tableOK n addOnly tbl = true) :
    ∀ r ∈ tbl, shapeOf r.2.1 r.2.2.1 r.2.2.2 = some r.1 ∧ r.1.length = n ∧
      (addOnly = true → noSub r.2.2.2 = true) := by
  intro r hr
  simp only [tableOK, Bool.and_eq_true, List.all_eq_true] at h
  exact rowOK_spec (h.1 r hr)

def tables : List (List Row) := [table1, table2, table3, table4, table5, table6, table7]

/-- **Item 3.** Every one of the 1,067 fixed polyominoes with up to 7 cells can be built
    without subtraction. -/
theorem coverage_upto_7 :
    ∀ tbl ∈ tables, ∀ r ∈ tbl, Buildable (· ∈ r.1) ∧ noSub r.2.2.2 = true := by
  intro tbl htbl r hr
  simp only [tables, List.mem_cons, List.not_mem_nil, or_false] at htbl
  have ok : ∃ n, tableOK n true tbl = true := by
    rcases htbl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, table1_ok⟩
    · exact ⟨2, table2_ok⟩
    · exact ⟨3, table3_ok⟩
    · exact ⟨4, table4_ok⟩
    · exact ⟨5, table5_ok⟩
    · exact ⟨6, table6_ok⟩
    · exact ⟨7, table7_ok⟩
  obtain ⟨n, ok⟩ := ok
  obtain ⟨hb, -, hs⟩ := rows_of_tableOK ok r hr
  exact ⟨buildable_of_shapeOf hb, hs rfl⟩

/-! ## The blocked shapes with 11–14 cells -/

def blockedTableOK : Bool :=
  blockedTable.all (fun r => rowOK r.1.length false r && blocked r.1) &&
  decide (blockedTable.map (·.1)).Nodup

theorem blockedTable_ok : blockedTableOK = true := by decide +kernel

theorem blockedTable_sizes :
    [11, 12, 13, 14].map (fun n => (blockedTable.filter (·.1.length == n)).length) = [4, 4, 36, 56] := by
  decide +kernel

/-- Each of the 100 blocked shapes can be built, and every formula that builds it
    uses subtraction. -/
theorem blocked_shapes :
    ∀ r ∈ blockedTable, Buildable (· ∈ r.1) ∧
      ∀ (d : Dir) (j : Nat) (w : List Op), (∀ u, sub u ∉ w) → shapeOf d j w ≠ some r.1 := by
  intro r hr
  have h := blockedTable_ok
  simp only [blockedTableOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hrow, hblocked⟩ := h.1 r hr
  obtain ⟨hb, -, -⟩ := rowOK_spec hrow
  exact ⟨buildable_of_shapeOf hb, fun d j w hw => needs_subtraction hblocked hw⟩
