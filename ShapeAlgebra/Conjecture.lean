import ShapeAlgebra.Blocked
import ShapeAlgebra.Swap

/-!
# Item 4: can every polyomino be built? (open)

This file states the question precisely and proves the parts of it we can:

* building a shape is unaffected by mirroring it or flipping it along the diagonal, so
  the question only has to be answered once per shape up to rotation and reflection;
* shapes where no cell can be added last (`Blocked.lean`) need a subtraction.

The question itself is not proved here. The evidence for it is in `Coverage.lean`
and the Python experiments.
-/

open Dir Op

/-- A polyomino: finitely many cells, at least one, in one piece. -/
def IsPolyomino (S : Cell → Prop) : Prop :=
  ∃ cs : List Cell, cs ≠ [] ∧ (∀ x, S x ↔ x ∈ cs) ∧ Connected S

/-- Some formula builds `S` (wherever `S` happens to sit). -/
def Buildable (S : Cell → Prop) : Prop :=
  ∃ (d : Dir) (j : Nat) (w : List Op) (t : State) (dx dy : Int),
    eval d j w = some t ∧ ∀ x : Cell, x ∈ t.cells ↔ S (x.1 + dx, x.2 + dy)

/-- **The open question.** Every polyomino can be built by some formula. -/
def EveryPolyominoBuildable : Prop := ∀ S, IsPolyomino S → Buildable S

/-! ## Symmetry: one orientation is enough -/

/-- `normalize` slides a shape and does nothing else. -/
theorem normalize_slides (s : State) :
    ∃ x0 y0 : Int, ∀ x : Cell, x ∈ (normalize s).cells ↔ (x.1 + x0, x.2 + y0) ∈ s.cells := by
  unfold normalize
  split
  · rename_i x0 y0 _ _
    refine ⟨x0, y0, fun x => ?_⟩
    simp only [mem_sortCells, List.mem_map]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩; simpa using hab
    · intro h; exact ⟨_, h, by simp⟩
  · exact ⟨0, 0, fun x => by simp⟩

theorem eval_append (d : Dir) (j : Nat) (w w' : List Op) :
    eval d j (w ++ w') = (eval d j w).bind fun t => w'.foldlM step t := by
  simp [eval, List.foldlM_append]

/-- Mirroring a buildable shape gives a buildable shape: add a mirror at the end. -/
theorem Buildable.mirror {S : Cell → Prop} (m : Dir) (h : Buildable S) :
    Buildable (fun x => S (reflect m x)) := by
  obtain ⟨d, j, w, t, dx, dy, ht, hS⟩ := h
  let t' : State := { t with cells := t.cells.map (reflect m), pin := t.pin.map (·.map (reflect m)) }
  obtain ⟨x0, y0, hn⟩ := normalize_slides t'
  have hstep : eval d j (w ++ [Op.mirror m]) = some (normalize t') := by
    simp [eval_append, ht, step, t']
  -- where the mirrored shape ends up
  let shift : Int × Int := match m with
    | R => (x0 + dx, y0 - dy)
    | C => (x0 - dx, y0 + dy)
  refine ⟨d, j, w ++ [Op.mirror m], _, shift.1, shift.2, hstep, fun x => ?_⟩
  rw [hn]
  simp only [t']
  rw [mem_map_reflect, ← reflect_eq, hS]
  have e : ((reflect m (x.1 + x0, x.2 + y0)).1 + dx, (reflect m (x.1 + x0, x.2 + y0)).2 + dy) =
      reflect m (x.1 + shift.1, x.2 + shift.2) := by
    cases m <;> simp [reflect, shift] <;> omega
  rw [e]

/-- Flipping a buildable shape along the diagonal gives a buildable shape:
    swap `R` and `C` everywhere in its formula (item 2). -/
theorem Buildable.transpose {S : Cell → Prop} (h : Buildable S) :
    Buildable (fun x => S (transpose x)) := by
  obtain ⟨d, j, w, t, dx, dy, ht, hS⟩ := h
  have hf := swap_symmetry d j w
  rw [ht] at hf
  cases ht' : eval d.swap j (w.map Op.swap) with
  | none => rw [ht'] at hf; exact hf.elim
  | some t' =>
    rw [ht'] at hf
    refine ⟨d.swap, j, w.map Op.swap, t', dy, dx, ht', fun x => ?_⟩
    rw [hf.cells.mem_iff, List.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [_root_.transpose] using (hS c).1 hc
    · intro hx
      exact ⟨_root_.transpose x, (hS _).2 (by simpa [_root_.transpose] using hx), rfl⟩

/-- A shape is buildable exactly when its diagonal flip is. -/
theorem buildable_transpose_iff {S : Cell → Prop} :
    Buildable (fun x => S (transpose x)) ↔ Buildable S :=
  ⟨fun h => by simpa using h.transpose, Buildable.transpose⟩

/-- A shape is buildable exactly when its mirror image is. -/
theorem buildable_mirror_iff {S : Cell → Prop} (m : Dir) :
    Buildable (fun x => S (reflect m x)) ↔ Buildable S := by
  refine ⟨fun h => ?_, Buildable.mirror m⟩
  have := h.mirror m
  have hr : ∀ x, reflect m (reflect m x) = x := by intro x; obtain ⟨a, b⟩ := x; cases m <;> simp [reflect]
  simpa [hr] using this
