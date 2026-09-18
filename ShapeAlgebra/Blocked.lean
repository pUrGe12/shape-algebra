import ShapeAlgebra.Basic

/-!
# Item 1: without subtraction, some cell could always have been added last

An addition puts the new cell right next to the far cell of a row or column, and
it never splits the shape. So if a formula has no `sub`, the shape it ends with has
a cell `c` with a neighbour `d` on the same row or column such that

* nothing lies beyond `c` on that line (looking from `d`), and
* removing `c` leaves the shape in one piece.

We prove this for every formula, then use it to show that specific shapes (such as
the 11-cell one from part 1) can't be built without subtraction, whatever the formula.
-/

open Dir Op

/-! ## Pieces of a shape -/

/-- Two cells share an edge. -/
def Adj (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 = b.2 + 1 ∨ b.2 = a.2 + 1)) ∨
  (a.2 = b.2 ∧ (a.1 = b.1 + 1 ∨ b.1 = a.1 + 1))

/-- A walk from `a` to another cell, through cells of `S`, one edge at a time. -/
inductive Path (S : Cell → Prop) (a : Cell) : Cell → Prop
  | here : S a → Path S a a
  | next {b c : Cell} : Path S a b → S c → Adj b c → Path S a c

/-- The shape is in one piece. -/
def Connected (S : Cell → Prop) : Prop := ∀ a b, S a → S b → Path S a b

/-- `e` lies beyond `c` on their shared row or column, looking from `c`'s neighbour `d`. -/
def Beyond (c d e : Cell) : Prop :=
  (c.2 = d.2 ∧ e.2 = c.2 ∧ ((d.1 < c.1 ∧ c.1 < e.1) ∨ (c.1 < d.1 ∧ e.1 < c.1))) ∨
  (c.1 = d.1 ∧ e.1 = c.1 ∧ ((d.2 < c.2 ∧ c.2 < e.2) ∨ (c.2 < d.2 ∧ e.2 < c.2)))

/-- Some cell of `S` could have been the last one added
    (or `S` has at most one cell, so there is nothing to add). -/
def AddableLast (S : Cell → Prop) : Prop :=
  (∀ a b, S a → S b → a = b) ∨
  ∃ c d, S c ∧ S d ∧ Adj c d ∧ (∀ e, S e → ¬ Beyond c d e) ∧ Connected (fun x => S x ∧ x ≠ c)

instance (a b : Cell) : Decidable (Adj a b) := by unfold Adj; infer_instance
instance (c d e : Cell) : Decidable (Beyond c d e) := by unfold Beyond; infer_instance

/-- What stays true at every step of a formula without subtraction. -/
def Good (S : Cell → Prop) : Prop := Connected S ∧ AddableLast S

theorem Adj.symm {a b : Cell} (h : Adj a b) : Adj b a := by
  unfold Adj at *; omega

theorem Path.trans {S : Cell → Prop} {a b c : Cell} (h₁ : Path S a b) (h₂ : Path S b c) :
    Path S a c := by
  induction h₂ with
  | here _ => exact h₁
  | next _ hc hadj ih => exact .next ih hc hadj

theorem Path.start {S : Cell → Prop} {a b : Cell} (h : Path S a b) : S a := by
  induction h with
  | here ha => exact ha
  | next _ _ _ ih => exact ih

theorem Path.mono {S T : Cell → Prop} (hST : ∀ x, S x → T x) {a b : Cell} (h : Path S a b) :
    Path T a b := by
  induction h with
  | here ha => exact .here (hST _ ha)
  | next _ hc hadj ih => exact .next ih (hST _ hc) hadj

/-! ## Moving and flipping a shape changes nothing

`Sym` is a reflection in either axis followed by a slide. Mirrors and `normalize`
are both of this kind. -/

structure Sym where
  fx : Bool
  fy : Bool
  tx : Int
  ty : Int

def Sym.app (g : Sym) (p : Cell) : Cell :=
  ((if g.fx then -p.1 else p.1) + g.tx, (if g.fy then -p.2 else p.2) + g.ty)

def Sym.inv (g : Sym) : Sym :=
  ⟨g.fx, g.fy, if g.fx then g.tx else -g.tx, if g.fy then g.ty else -g.ty⟩

def Sym.id : Sym := ⟨false, false, 0, 0⟩

theorem Sym.inv_app (g : Sym) (p : Cell) : g.inv.app (g.app p) = p := by
  obtain ⟨fx, fy, tx, ty⟩ := g; obtain ⟨x, y⟩ := p
  cases fx <;> cases fy <;> simp [Sym.app, Sym.inv] <;> omega

theorem Sym.app_inv (g : Sym) (p : Cell) : g.app (g.inv.app p) = p := by
  obtain ⟨fx, fy, tx, ty⟩ := g; obtain ⟨x, y⟩ := p
  cases fx <;> cases fy <;> simp [Sym.app, Sym.inv] <;> omega

theorem Sym.id_app (p : Cell) : Sym.id.app p = p := by
  simp [Sym.id, Sym.app]

theorem Sym.adj_iff (g : Sym) (a b : Cell) : Adj (g.app a) (g.app b) ↔ Adj a b := by
  obtain ⟨fx, fy, tx, ty⟩ := g
  cases fx <;> cases fy <;> simp [Sym.app, Adj] <;> omega

theorem Sym.beyond_iff (g : Sym) (c d e : Cell) :
    Beyond (g.app c) (g.app d) (g.app e) ↔ Beyond c d e := by
  obtain ⟨fx, fy, tx, ty⟩ := g
  cases fx <;> cases fy <;> simp [Sym.app, Beyond] <;> omega

/-- If `T` is `S` moved by `g`, walks in `S` give walks in `T`. -/
theorem Path.pull {S T : Cell → Prop} (g : Sym) (hT : ∀ x, T x ↔ S (g.app x)) {a b : Cell}
    (h : Path S (g.app a) b) : Path T a (g.inv.app b) := by
  induction h with
  | here _ =>
    rw [Sym.inv_app]; exact .here ((hT a).2 (by assumption))
  | next _ hc hadj ih =>
    refine .next ih ((hT _).2 (by rw [Sym.app_inv]; exact hc)) ?_
    exact (Sym.adj_iff g.inv _ _).2 hadj

theorem Connected.pull {S T : Cell → Prop} (g : Sym) (hT : ∀ x, T x ↔ S (g.app x))
    (h : Connected S) : Connected T := by
  intro a b ha hb
  have := Path.pull g hT (h _ _ ((hT a).1 ha) ((hT b).1 hb))
  rwa [Sym.inv_app] at this

theorem AddableLast.pull {S T : Cell → Prop} (g : Sym) (hT : ∀ x, T x ↔ S (g.app x))
    (h : AddableLast S) : AddableLast T := by
  rcases h with h | ⟨c, d, hc, hd, hadj, hfar, hconn⟩
  · left
    intro a b ha hb
    have := congrArg g.inv.app (h _ _ ((hT a).1 ha) ((hT b).1 hb))
    rwa [Sym.inv_app, Sym.inv_app] at this
  · right
    refine ⟨g.inv.app c, g.inv.app d, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hT, Sym.app_inv]; exact hc
    · rw [hT, Sym.app_inv]; exact hd
    · exact (Sym.adj_iff g.inv _ _).2 hadj
    · intro e he hb
      apply hfar (g.app e) ((hT e).1 he)
      have := (Sym.beyond_iff g _ _ _).2 hb
      rwa [Sym.app_inv, Sym.app_inv] at this
    · apply Connected.pull g _ hconn
      intro x
      constructor
      · rintro ⟨hx, hne⟩
        exact ⟨(hT x).1 hx, fun h => hne (by rw [← h, Sym.inv_app])⟩
      · rintro ⟨hx, hne⟩
        exact ⟨(hT x).2 hx, fun h => hne (by rw [h, Sym.app_inv])⟩

theorem Good.pull {S T : Cell → Prop} (g : Sym) (hT : ∀ x, T x ↔ S (g.app x)) (h : Good S) :
    Good T :=
  ⟨Connected.pull g hT h.1, AddableLast.pull g hT h.2⟩

theorem Good.congr {S T : Cell → Prop} (hT : ∀ x, T x ↔ S x) (h : Good S) : Good T :=
  Good.pull Sym.id (by simpa [Sym.id_app] using hT) h

/-! ## Adding a cell at the far end of a line keeps a shape good -/

theorem extend {S : Cell → Prop} {c d : Cell} (hS : Connected S) (hd : S d) (hadj : Adj c d)
    (hfar : ∀ e, S e → ¬ Beyond c d e) (hc : ¬ S c) : Good (fun x => S x ∨ x = c) := by
  let T := fun x => S x ∨ x = c
  have lift : ∀ {a b}, Path S a b → Path T a b := Path.mono (fun _ h => Or.inl h)
  -- every cell of S reaches c, and c reaches every cell of S
  have to_c : ∀ a, S a → Path T a c := fun a ha =>
    .next (lift (hS a d ha hd)) (Or.inr rfl) hadj.symm
  have from_c : ∀ b, S b → Path T c b := fun b hb =>
    Path.trans (.next (.here (Or.inr rfl)) (Or.inl hd) hadj) (lift (hS d b hd hb))
  constructor
  · rintro a b (ha | rfl) (hb | rfl)
    · exact lift (hS a b ha hb)
    · exact to_c a ha
    · exact from_c b hb
    · exact .here (Or.inr rfl)
  · right
    refine ⟨c, d, Or.inr rfl, Or.inl hd, hadj, ?_, ?_⟩
    · rintro e (he | rfl)
      · exact hfar e he
      · unfold Beyond; omega
    · apply Connected.pull Sym.id _ hS
      intro x
      simp only [Sym.id_app]
      constructor
      · rintro ⟨hx | hx, hne⟩
        · exact hx
        · exact absurd hx hne
      · intro hx
        exact ⟨Or.inl hx, fun h => hc (h ▸ hx)⟩

/-! ## Membership facts about the rules -/

theorem mem_insertCell {x c : Cell} {l : List Cell} : x ∈ insertCell c l ↔ x = c ∨ x ∈ l := by
  induction l with
  | nil => simp [insertCell]
  | cons d ds ih =>
    simp only [insertCell]
    split <;> simp [ih] <;> exact or_left_comm

theorem mem_sortCells {x : Cell} {l : List Cell} : x ∈ sortCells l ↔ x ∈ l := by
  induction l with
  | nil => simp [sortCells]
  | cons c cs ih => simp [sortCells, mem_insertCell, ih]

/-- `normalize` only slides the shape. -/
theorem normalize_mem (s : State) :
    ∃ g : Sym, ∀ x, x ∈ (normalize s).cells ↔ g.app x ∈ s.cells := by
  unfold normalize
  split
  · rename_i x0 y0 _ _
    refine ⟨⟨false, false, x0, y0⟩, fun x => ?_⟩
    simp only [mem_sortCells, List.mem_map, Sym.app]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩; simpa using hab
    · intro h; exact ⟨_, h, by simp⟩
  · exact ⟨Sym.id, fun x => by simp [Sym.id_app]⟩

def reflSym : Dir → Sym
  | R => ⟨false, true, 0, 0⟩
  | C => ⟨true, false, 0, 0⟩

theorem reflect_eq (d : Dir) (p : Cell) : reflect d p = (reflSym d).app p := by
  obtain ⟨x, y⟩ := p; cases d <;> simp [reflect, reflSym, Sym.app]

theorem mem_map_reflect (d : Dir) (l : List Cell) (x : Cell) :
    x ∈ l.map (reflect d) ↔ (reflSym d).app x ∈ l := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨p, q⟩ := a
    cases d <;> simpa [reflect, reflSym, Sym.app] using ha
  · intro h
    refine ⟨_, h, ?_⟩
    obtain ⟨p, q⟩ := x
    cases d <;> simp [reflect, reflSym, Sym.app]

/-- What `reach` tells us: the far cell exists, and nothing on the line is further. -/
theorem reach_spec {d : Dir} {cs : List Cell} {k a : Int} (h : reach d cs k = some a) :
    cellAt d k a ∈ cs ∧ ∀ e ∈ cs, lineOf d e = k → along d e ≤ a := by
  unfold reach at h
  rw [List.max?_eq_some_iff, List.mem_map] at h
  obtain ⟨⟨e, he, rfl⟩, hmax⟩ := h
  simp only [List.mem_filter, beq_iff_eq] at he
  obtain ⟨he, hk⟩ := he
  refine ⟨?_, fun e' he' hk' =>
    hmax _ (List.mem_map.2 ⟨e', List.mem_filter.2 ⟨he', by simp [hk']⟩, rfl⟩)⟩
  have : cellAt d k (along d e) = e := by
    obtain ⟨x, y⟩ := e
    cases d <;> simp_all [lineOf, along, cellAt]
  rw [this]; exact he

theorem hit_spec {s : State} {u : Dir} {line a : Int} (h : hit s u = some (line, a)) :
    reach u s.cells line = some a := by
  simp only [hit, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨k, _, h⟩ := h
  have key : ∀ o : Option Int,
      (o.bind fun line => (reach u s.cells line).bind fun a => some (line, a)) = some (line, a) →
      reach u s.cells line = some a := by
    intro o ho
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨l, _, a', ha', rfl, rfl⟩ := ho
    exact ha'
  split at h
  · exact key _ h
  · exact key _ h

/-! ## Every step without subtraction keeps the shape good -/

theorem step_good {s t : State} {o : Op} (hs : Good (· ∈ s.cells)) (ho : ∀ u, o ≠ sub u)
    (h : step s o = some t) : Good (· ∈ t.cells) := by
  cases o with
  | push d => simp [step] at h; subst h; exact hs
  | pin => simp [step] at h; subst h; exact hs
  | sub u => exact absurd rfl (ho u)
  | mirror d =>
    simp only [step, Option.some.injEq] at h; subst h
    obtain ⟨g, hg⟩ := normalize_mem
      { s with cells := s.cells.map (reflect d), pin := s.pin.map (·.map (reflect d)) }
    exact Good.pull g hg (Good.pull (reflSym d) (mem_map_reflect d s.cells) hs)
  | add u =>
    simp only [step, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨line, a⟩, hp, rfl⟩ := h
    obtain ⟨hd, hmax⟩ := reach_spec (hit_spec hp)
    -- the new cell c and the far cell d it lands next to
    have hadj : Adj (cellAt u line (a + 1)) (cellAt u line a) := by
      cases u <;> simp [Adj, cellAt] <;> omega
    have hfar : ∀ e, e ∈ s.cells → ¬ Beyond (cellAt u line (a + 1)) (cellAt u line a) e := by
      intro e he hb
      obtain ⟨x, y⟩ := e
      cases u <;> simp [Beyond, cellAt] at hb
      · have := hmax _ he (by simp [lineOf]; omega); simp [along] at this; omega
      · have := hmax _ he (by simp [lineOf]; omega); simp [along] at this; omega
    have hc : cellAt u line (a + 1) ∉ s.cells := by
      intro hc
      have := hmax _ hc (by cases u <;> simp [lineOf, cellAt])
      cases u <;> simp [along, cellAt] at this <;> omega
    have := extend hs.1 hd hadj hfar hc
    obtain ⟨g, hg⟩ := normalize_mem { s with cells := cellAt u line (a + 1) :: s.cells, pushed := false }
    refine Good.pull g hg (Good.congr ?_ this)
    intro x; simp [or_comm]

theorem strip_good (d : Dir) (j : Nat) : Good (· ∈ (strip d j).cells) := by
  obtain ⟨g, hg⟩ := normalize_mem
    { cells := (List.range j).map fun (i : Nat) => cellAt d 0 i, latch := d, pushed := false, pin := none }
  refine Good.pull g hg ?_
  simp only
  -- the strip's cells are cellAt d 0 i for i < j; grow it one cell at a time
  let S (n : Nat) : Cell → Prop := fun x => ∃ i : Nat, i < n ∧ cellAt d 0 i = x
  have hS : ∀ n x, x ∈ (List.range n).map (fun (i : Nat) => cellAt d 0 i) ↔ S n x := by
    intro n x; simp [S]
  have one : ∀ n, Good (S (n + 1)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, Or.inl ?_⟩
      · rintro a b ⟨i, hi, rfl⟩ ⟨k, hk, rfl⟩
        obtain rfl : i = 0 := by omega
        obtain rfl : k = 0 := by omega
        exact .here ⟨0, by omega, rfl⟩
      · rintro a b ⟨i, hi, rfl⟩ ⟨k, hk, rfl⟩
        obtain rfl : i = 0 := by omega
        obtain rfl : k = 0 := by omega
        rfl
    | succ n ih =>
      have hadj : Adj (cellAt d 0 ((n + 1 : Nat) : Int)) (cellAt d 0 (n : Int)) := by
        cases d <;> simp [Adj, cellAt] <;> omega
      have hfar : ∀ e, S (n + 1) e → ¬ Beyond (cellAt d 0 ((n + 1 : Nat) : Int)) (cellAt d 0 (n : Int)) e := by
        rintro e ⟨i, hi, rfl⟩ hb
        cases d <;> simp [Beyond, cellAt] at hb <;> omega
      have hc : ¬ S (n + 1) (cellAt d 0 ((n + 1 : Nat) : Int)) := by
        rintro ⟨i, hi, h⟩
        cases d <;> simp [cellAt] at h <;> omega
      refine Good.congr ?_ (extend ih.1 ⟨n, by omega, rfl⟩ hadj hfar hc)
      intro x
      constructor
      · rintro ⟨i, hi, rfl⟩
        by_cases h : i < n + 1
        · exact Or.inl ⟨i, h, rfl⟩
        · right; obtain rfl : i = n + 1 := by omega
          rfl
      · rintro (⟨i, hi, rfl⟩ | rfl)
        · exact ⟨i, by omega, rfl⟩
        · exact ⟨n + 1, by omega, rfl⟩
  cases j with
  | zero =>
    refine ⟨?_, Or.inl ?_⟩ <;> intro a <;> simp
  | succ n => exact Good.congr (hS (n + 1)) (one n)

theorem run_good (w : List Op) (hw : ∀ u, sub u ∉ w) :
    ∀ s t, Good (· ∈ s.cells) → w.foldlM step s = some t → Good (· ∈ t.cells) := by
  induction w with
  | nil => intro s t hs h; simp at h; subst h; exact hs
  | cons o w ih =>
    intro s t hs h
    simp only [List.foldlM_cons, bind, Option.bind] at h
    split at h; · contradiction
    rename_i s' hs'
    have ho : ∀ u, o ≠ sub u := fun u e => hw u (by simp [e])
    have hw' : ∀ u, sub u ∉ w := fun u m => hw u (by simp [m])
    exact ih hw' s' t (step_good hs ho hs') h

/-- **Item 1.** Whatever formula you write, if it has no subtraction, the shape it
    builds has a cell that could have been added last. -/
theorem addableLast_of_no_sub {d : Dir} {j : Nat} {w : List Op} {t : State}
    (hw : ∀ u, sub u ∉ w) (h : eval d j w = some t) : AddableLast (· ∈ t.cells) :=
  (run_good w hw _ _ (strip_good d j) h).2

/-! ## Checking that a concrete shape is blocked

`blocked cs` is a computation. `blocked_sound` proves that when it says `true`, no
cell of `cs` could have been added last. -/

/-- Grow a piece of `rest`, starting from `comp`, by adding touching cells. -/
def grow (rest : List Cell) : Nat → List Cell → List Cell
  | 0, comp => comp
  | n + 1, comp =>
    grow rest n (comp ++ rest.filter fun y => !comp.contains y && comp.any fun x => decide (Adj x y))

/-- Removing `c` splits `cs`: we exhibit a piece that nothing else touches. -/
def splits (cs : List Cell) (c : Cell) : Bool :=
  match cs.filter (· != c) with
  | [] => false
  | a :: rest =>
    let all := a :: rest
    let piece := grow all all.length [a]
    piece.all (all.contains ·) &&
    all.any (fun b => !piece.contains b) &&
    piece.all fun x => all.all fun y => !decide (Adj x y) || piece.contains y

def blocked (cs : List Cell) : Bool :=
  (cs.any fun a => cs.any fun b => a != b) &&
  cs.all fun c => cs.all fun d =>
    !decide (Adj c d) || cs.any (fun e => decide (Beyond c d e)) || splits cs c

theorem not_connected_of_piece {S A : Cell → Prop} {a b : Cell}
    (hclosed : ∀ x y, A x → S y → Adj x y → A y) (ha : A a) (hSb : S b) (hSa : S a) (hb : ¬ A b) :
    ¬ Connected S := by
  intro hc
  have : ∀ z, Path S a z → A z := by
    intro z p
    induction p with
    | here _ => exact ha
    | next _ hz hadj ih => exact hclosed _ _ ih hz hadj
  exact hb (this b (hc a b hSa hSb))

theorem splits_sound {cs : List Cell} {c : Cell} (h : splits cs c = true) :
    ¬ Connected (fun x => x ∈ cs ∧ x ≠ c) := by
  unfold splits at h
  split at h
  · contradiction
  · rename_i a rest hrest
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, List.contains_iff_mem] at h
    obtain ⟨⟨hsub, b, hb, hbp⟩, hclosed⟩ := h
    have mem : ∀ x, x ∈ a :: rest ↔ x ∈ cs ∧ x ≠ c := by
      intro x; rw [← hrest]; simp
    have hbp' : b ∉ grow (a :: rest) (a :: rest).length [a] := by simpa using hbp
    refine not_connected_of_piece (A := (· ∈ grow (a :: rest) (a :: rest).length [a])) ?_ ?_
      ((mem b).1 hb) ((mem a).1 (by simp)) hbp'
    · intro x y hx hy hadj
      rcases hclosed x hx y ((mem y).2 hy) with h | h
      · exact absurd hadj h
      · simpa using h
    · -- `a` is in the piece: `grow` only ever appends
      have : ∀ n (l : List Cell), a ∈ l → a ∈ grow (a :: rest) n l := by
        intro n
        induction n with
        | zero => intro l h; exact h
        | succ n ih => intro l h; exact ih _ (List.mem_append_left _ h)
      exact this _ _ (by simp)

theorem blocked_sound {cs : List Cell} (h : blocked cs = true) : ¬ AddableLast (· ∈ cs) := by
  simp only [blocked, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨a, ha, b, hb, hab⟩, hcells⟩ := h
  rintro (hall | ⟨c, d, hc, hd, hadj, hfar, hconn⟩)
  · exact hab (hall a b ha hb)
  · rcases hcells c hc d hd with ((h | ⟨e, he, hbey⟩) | h)
    · exact h hadj
    · exact hfar e he hbey
    · exact splits_sound h hconn

/-- A blocked shape can't come out of a formula without subtraction. -/
theorem needs_subtraction {cs : List Cell} (hb : blocked cs = true) {d : Dir} {j : Nat}
    {w : List Op} (hw : ∀ u, sub u ∉ w) : shapeOf d j w ≠ some cs := by
  intro h
  simp only [shapeOf, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact blocked_sound hb (addableLast_of_no_sub hw ht)

/-- The 11-cell shape from part 1: no formula without subtraction builds it. -/
theorem part1_shape_needs_subtraction {d : Dir} {j : Nat} {w : List Op} (hw : ∀ u, sub u ∉ w) :
    shapeOf d j w ≠ some (pic ["#####", "#...#", "##.##"]) :=
  needs_subtraction (by decide +kernel) hw
