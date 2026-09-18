import ShapeAlgebra.Basic

open Dir Op

/-! ## 8. Proofs about every formula -/

/-- `u` and `v` give the same result from any state. -/
def Equiv (u v : List Op) : Prop := ∀ s : State, u.foldlM step s = v.foldlM step s

/-- "If we see the LHS anywhere, we can substitute the RHS": any rule of the form
    `Equiv u v` holds inside any longer formula. -/
theorem Equiv.subst {u v : List Op} (h : Equiv u v) (p q : List Op) :
    Equiv (p ++ u ++ q) (p ++ v ++ q) := by
  intro s
  have h' : ∀ t, u.foldlM step t = v.foldlM step t := h
  simp only [List.foldlM_append, h']

theorem length_insertCell (c : Cell) (cs : List Cell) :
    (insertCell c cs).length = cs.length + 1 := by
  induction cs with
  | nil => rfl
  | cons d ds ih => simp only [insertCell]; split <;> simp [ih]

theorem length_sortCells (cs : List Cell) : (sortCells cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sortCells, length_insertCell, ih]

theorem length_normalize (s : State) : (normalize s).cells.length = s.cells.length := by
  unfold normalize
  split <;> simp [length_sortCells]

/-- A single step adds at most one cell. -/
theorem step_length {s t : State} {o : Op} (h : step s o = some t) :
    t.cells.length ≤ s.cells.length + 1 := by
  cases o with
  | push d => simp [step] at h; subst h; simp
  | pin => simp [step] at h; subst h; simp
  | mirror d => simp [step] at h; subst h; simp [length_normalize]
  | add u =>
    simp only [step, bind, Option.bind] at h
    split at h
    · contradiction
    · simp at h; subst h; simp [length_normalize]
  | sub u =>
    simp only [step, bind, Option.bind] at h
    split at h
    · contradiction
    · simp at h; subst h
      simp only [length_normalize]
      exact Nat.le_succ_of_le (List.length_filter_le _ _)

theorem run_length (w : List Op) : ∀ s t, w.foldlM step s = some t →
    t.cells.length ≤ s.cells.length + w.length := by
  induction w with
  | nil => intro s t h; simp at h; subst h; simp
  | cons o w ih =>
    intro s t h
    simp only [List.foldlM_cons, bind, Option.bind] at h
    split at h
    · contradiction
    · rename_i s' hs
      have h1 := step_length hs
      have h2 := ih s' t h
      simp
      omega

/-- Part 2's theorem `S ≥ N − j`: a formula with `S` steps starting from a strip of
    `j` cells ends with at most `j + S` cells. -/
theorem size_bound {d : Dir} {j : Nat} {w : List Op} {t : State} (h : eval d j w = some t) :
    t.cells.length ≤ j + w.length := by
  have := run_length w _ _ h
  simp [strip, length_normalize] at this
  omega
