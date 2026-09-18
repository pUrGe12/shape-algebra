import ShapeAlgebra.Basic

/-!
# Item 2: swapping R and C flips the shape along the diagonal

Write a formula with every `R` and `C` exchanged, and it builds the original
shape flipped along the diagonal (`(x, y) ↦ (y, x)`). With the two mirrors, that
means one orientation of a shape can be built exactly when all 8 can.

The flipped shape can come out with its cells listed in a different order, so the
statements say "same cells" (`List.Perm`) rather than "same list".
-/

open Dir Op

def Dir.swap : Dir → Dir
  | R => C
  | C => R

def Op.swap : Op → Op
  | add d    => add d.swap
  | sub d    => sub d.swap
  | mirror d => mirror d.swap
  | push d   => push d.swap
  | pin      => pin

/-- Flip a cell along the diagonal. -/
def transpose (p : Cell) : Cell := (p.2, p.1)

@[simp] theorem transpose_transpose (p : Cell) : transpose (transpose p) = p := rfl

theorem transpose_inj {p q : Cell} : transpose p = transpose q ↔ p = q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp [transpose]; exact And.comm

@[simp] theorem Dir.swap_swap (d : Dir) : d.swap.swap = d := by cases d <;> rfl

theorem Dir.swap_inj {d e : Dir} : d.swap = e.swap ↔ d = e := by
  cases d <;> cases e <;> simp [Dir.swap]

@[simp] theorem lineOf_swap (d : Dir) (p : Cell) : lineOf d.swap (transpose p) = lineOf d p := by
  obtain ⟨x, y⟩ := p; cases d <;> rfl

@[simp] theorem along_swap (d : Dir) (p : Cell) : along d.swap (transpose p) = along d p := by
  obtain ⟨x, y⟩ := p; cases d <;> rfl

@[simp] theorem cellAt_swap (d : Dir) (k a : Int) : cellAt d.swap k a = transpose (cellAt d k a) := by
  cases d <;> rfl

@[simp] theorem reflect_swap (d : Dir) (p : Cell) :
    reflect d.swap (transpose p) = transpose (reflect d p) := by
  obtain ⟨x, y⟩ := p; cases d <;> rfl

/-! ## Largest and smallest only depend on which numbers are present -/

theorem max?_congr {α : Type} [Max α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {l₁ l₂ : List α} (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.max? = l₂.max? := by
  cases h₁ : l₁.max? with
  | none =>
    rw [List.max?_eq_none_iff] at h₁; subst h₁
    symm; rw [List.max?_eq_none_iff]
    cases l₂ with
    | nil => rfl
    | cons y ys => exact absurd ((h y).2 (by simp)) (by simp)
  | some a =>
    symm; rw [List.max?_eq_some_iff] at h₁ ⊢
    exact ⟨(h a).1 h₁.1, fun b hb => h₁.2 b ((h b).2 hb)⟩

theorem min?_congr {l₁ l₂ : List Int} (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.min? = l₂.min? := by
  cases h₁ : l₁.min? with
  | none =>
    rw [List.min?_eq_none_iff] at h₁; subst h₁
    symm; rw [List.min?_eq_none_iff]
    cases l₂ with
    | nil => rfl
    | cons y ys => exact absurd ((h y).2 (by simp)) (by simp)
  | some a =>
    symm; rw [List.min?_eq_some_iff] at h₁ ⊢
    exact ⟨(h a).1 h₁.1, fun b hb => h₁.2 b ((h b).2 hb)⟩

theorem insertCell_perm (c : Cell) (l : List Cell) : (insertCell c l).Perm (c :: l) := by
  induction l with
  | nil => exact .refl _
  | cons d ds ih =>
    simp only [insertCell]
    split
    · exact .refl _
    · exact (ih.cons d).trans (.swap c d ds)

theorem sortCells_perm (l : List Cell) : (sortCells l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons c cs ih => exact (insertCell_perm c _).trans (ih.cons c)

/-! ## "`t` is `s` flipped along the diagonal" -/

def PinRel : Option (List Cell) → Option (List Cell) → Prop
  | none,   none   => True
  | some q, some p => q.Perm (p.map transpose)
  | _,      _      => False

structure Flipped (s t : State) : Prop where
  cells  : t.cells.Perm (s.cells.map transpose)
  latch  : t.latch = s.latch.swap
  pushed : t.pushed = s.pushed
  pin    : PinRel t.pin s.pin

def OptFlipped : Option State → Option State → Prop
  | none,   none   => True
  | some s, some t => Flipped s t
  | _,      _      => False

/-! ## Each rule treats the flipped shape the same way -/

theorem scope_perm {s t : State} (h : Flipped s t) : (scope t).Perm ((scope s).map transpose) := by
  have hc := h.cells
  have hp := h.pin
  unfold scope
  cases hs : s.pin with
  | none =>
    cases ht : t.pin with
    | none => exact hc
    | some q => rw [hs, ht] at hp; simp [PinRel] at hp
  | some p =>
    cases ht : t.pin with
    | none => rw [hs, ht] at hp; simp [PinRel] at hp
    | some q =>
      rw [hs, ht] at hp
      simp only [PinRel] at hp
      -- hp : q is p flipped
      refine (hc.filter _).trans (.of_eq ?_)
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro x _
      show q.contains (transpose x) = p.contains x
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, hp.mem_iff, List.mem_map]
      constructor
      · rintro ⟨y, hy, hxy⟩
        rw [transpose_inj] at hxy
        exact hxy ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩

theorem filter_line_swap (d : Dir) (l : List Cell) (k : Int) :
    (l.map transpose).filter (lineOf d.swap · == k) = (l.filter (lineOf d · == k)).map transpose := by
  rw [List.filter_map]; simp [Function.comp_def]

theorem reach_swap {d : Dir} {cs cs' : List Cell} (h : cs'.Perm (cs.map transpose)) (k : Int) :
    reach d.swap cs' k = reach d cs k := by
  unfold reach
  apply max?_congr
  intro x
  apply List.Perm.mem_iff
  refine ((h.filter _).map _).trans (.of_eq ?_)
  rw [filter_line_swap, List.map_map]
  simp [Function.comp_def]

theorem count_swap {d : Dir} {cs cs' : List Cell} (h : cs'.Perm (cs.map transpose)) (k : Int) :
    count d.swap cs' k = count d cs k := by
  unfold count
  rw [(h.filter _).length_eq, filter_line_swap, List.length_map]

theorem select_eq {s t : State} (h : Flipped s t) : select t = select s := by
  have hl : ((scope t).map (lineOf t.latch)).Perm ((scope s).map (lineOf s.latch)) := by
    rw [h.latch]
    refine ((scope_perm h).map _).trans (.of_eq ?_)
    simp [Function.comp_def]
  have hn : count t.latch (scope t) = count s.latch (scope s) := by
    funext k; rw [h.latch]; exact count_swap (scope_perm h) k
  unfold select
  rw [h.pushed, hn]
  split
  · simp only [bind]
    rw [max?_congr (fun x => (hl.map _).mem_iff)]
    cases (List.map (count s.latch (scope s)) (List.map (lineOf s.latch) (scope s))).max? with
    | none => rfl
    | some m => exact max?_congr (fun x => (hl.filter _).mem_iff)
  · exact max?_congr (fun x => hl.mem_iff)

theorem hit_eq {s t : State} (h : Flipped s t) (u : Dir) : hit t u.swap = hit s u := by
  unfold hit
  rw [select_eq h, h.latch]
  simp only [Dir.swap_inj, reach_swap (scope_perm h), reach_swap h.cells]

theorem normalize_flipped {s t : State} (h : Flipped s t) : Flipped (normalize s) (normalize t) := by
  have hx : (t.cells.map (·.1)).min? = (s.cells.map (·.2)).min? :=
    min?_congr fun x => ((h.cells.map _).trans (.of_eq (by simp [transpose]))).mem_iff
  have hy : (t.cells.map (·.2)).min? = (s.cells.map (·.1)).min? :=
    min?_congr fun x => ((h.cells.map _).trans (.of_eq (by simp [transpose]))).mem_iff
  unfold normalize
  rw [hx, hy]
  cases ha : (s.cells.map (·.1)).min? <;> cases hb : (s.cells.map (·.2)).min? <;> simp only
  all_goals try exact h
  rename_i x0 y0
  -- sliding commutes with the flip
  have slide : ∀ l : List Cell, l.Perm (s.cells.map transpose) →
      (sortCells (l.map fun (x, y) => (x - y0, y - x0))).Perm
        ((sortCells (s.cells.map fun (x, y) => (x - x0, y - y0))).map transpose) := by
    intro l hl
    refine (sortCells_perm _).trans ?_
    refine ((hl.map _).trans (.of_eq ?_)).trans ((sortCells_perm _).map _).symm
    simp [Function.comp_def, transpose]
  refine ⟨slide _ h.cells, h.latch, h.pushed, ?_⟩
  -- a pin slides the same way as the cells
  have hp := h.pin
  cases hs : s.pin with
  | none =>
    cases ht : t.pin with
    | none => trivial
    | some q => rw [hs, ht] at hp; simp [PinRel] at hp
  | some p =>
    cases ht : t.pin with
    | none => rw [hs, ht] at hp; simp [PinRel] at hp
    | some q =>
      rw [hs, ht] at hp
      simp only [PinRel, Option.map] at hp ⊢
      refine (sortCells_perm _).trans ?_
      refine ((hp.map _).trans (.of_eq ?_)).trans ((sortCells_perm _).map _).symm
      simp [Function.comp_def, transpose]

theorem step_flipped {s t : State} (h : Flipped s t) (o : Op) :
    OptFlipped (step s o) (step t o.swap) := by
  cases o with
  | push d => exact ⟨h.cells, rfl, rfl, h.pin⟩
  | pin => exact ⟨h.cells, h.latch, h.pushed, h.cells⟩
  | mirror d =>
    apply normalize_flipped
    refine ⟨(h.cells.map _).trans (.of_eq (by simp [Function.comp_def])), h.latch, h.pushed, ?_⟩
    have hp := h.pin
    cases hs : s.pin with
    | none =>
      cases ht : t.pin with
      | none => trivial
      | some q => rw [hs, ht] at hp; simp [PinRel] at hp
    | some p =>
      cases ht : t.pin with
      | none => rw [hs, ht] at hp; simp [PinRel] at hp
      | some q =>
        rw [hs, ht] at hp
        simp only [PinRel, Option.map] at hp ⊢
        exact (hp.map _).trans (.of_eq (by simp [Function.comp_def]))
  | add u =>
    simp only [step, Op.swap, hit_eq h]
    cases hit s u with
    | none => trivial
    | some p =>
      obtain ⟨line, a⟩ := p
      apply normalize_flipped
      refine ⟨?_, h.latch, rfl, h.pin⟩
      simp only [cellAt_swap, List.map_cons]
      exact h.cells.cons _
  | sub u =>
    simp only [step, Op.swap, hit_eq h]
    cases hit s u with
    | none => trivial
    | some p =>
      obtain ⟨line, a⟩ := p
      apply normalize_flipped
      refine ⟨(h.cells.filter _).trans (.of_eq ?_), h.latch, rfl, h.pin⟩
      dsimp only
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro x _
      simp only [Function.comp_apply, cellAt_swap]
      rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, ne_eq, transpose_inj]

theorem strip_flipped (d : Dir) (j : Nat) : Flipped (strip d j) (strip d.swap j) := by
  apply normalize_flipped
  exact ⟨.of_eq (by simp [Function.comp_def]), rfl, rfl, trivial⟩

theorem run_flipped (w : List Op) :
    ∀ s t, Flipped s t → OptFlipped (w.foldlM step s) ((w.map Op.swap).foldlM step t) := by
  induction w with
  | nil => intro s t h; exact h
  | cons o w ih =>
    intro s t h
    simp only [List.map_cons, List.foldlM_cons]
    have := step_flipped h o
    revert this
    cases step s o <;> cases step t o.swap <;> intro hst
    · trivial
    · exact hst.elim
    · exact hst.elim
    · exact ih _ _ hst

/-- **Item 2.** Swapping `R` and `C` everywhere in a formula flips its result along
    the diagonal: same cells, with `x` and `y` exchanged. -/
theorem swap_symmetry (d : Dir) (j : Nat) (w : List Op) :
    OptFlipped (eval d j w) (eval d.swap j (w.map Op.swap)) :=
  run_flipped w _ _ (strip_flipped d j)

theorem swap_shape {d : Dir} {j : Nat} {w : List Op} {cs : List Cell} (h : shapeOf d j w = some cs) :
    ∃ cs', shapeOf d.swap j (w.map Op.swap) = some cs' ∧ cs'.Perm (cs.map transpose) := by
  have := swap_symmetry d j w
  simp only [shapeOf, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  rw [hs] at this
  cases he : eval d.swap j (w.map Op.swap) with
  | none => rw [he] at this; exact this.elim
  | some t => rw [he] at this; exact ⟨t.cells, by simp [shapeOf, he], this.cells⟩

-- Part 2's carving formula builds the upright shape; swapped, it builds the sideways one.
example : shapeOf R 3
    [add C, push C, add C, mirror C, add C, push C, pin, add C, push C, add C, add C,
     add C, add C, mirror C, sub R, pin, sub R, push C, add R, push C, add R]
    = some (pic ["###", "#.#", "#..", "#.#", "###"]) := by decide +kernel
example : shapeOf C 3
    ([add C, push C, add C, mirror C, add C, push C, pin, add C, push C, add C, add C,
      add C, add C, mirror C, sub R, pin, sub R, push C, add R, push C, add R].map Op.swap)
    = some (pic ["##.##", "#...#", "#####"]) := by decide +kernel
