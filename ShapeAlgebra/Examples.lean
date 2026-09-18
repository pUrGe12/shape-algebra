import ShapeAlgebra.Basic

open Dir Op

/-! ## 6. Every formula in the posts, against its picture

A bare `^M` is read as `M_R` (top-to-bottom); that's the reading that fits the posts. -/

structure Example where
  name : String
  base : Dir
  len  : Nat
  ops  : List Op
  want : List String

def examples : List Example := [
  -- A_R^(4)
  ⟨"tetromino 1", R, 4, [],
    ["####"]⟩,
  -- A_C^(4)
  ⟨"tetromino 2", C, 4, [],
    ["#", "#", "#", "#"]⟩,
  -- ((A_C^(2)+1_R)^M)_C+1_R
  ⟨"tetromino 3", C, 2, [add R, mirror R, push C, add R],
    ["##", "##"]⟩,
  -- (A_R^(2)+1_C)^M+1_R
  ⟨"tetromino 4", R, 2, [add C, mirror R, add R],
    ["###", ".#."]⟩,
  -- ((A_C^(2)+1_R)_C+1_C)^M_C
  ⟨"tetromino 5", C, 2, [add R, push C, add C, mirror C],
    [".#", "##", ".#"]⟩,
  -- ((A_R^(2)+1_C)^M+1_R)^M
  ⟨"tetromino 6", R, 2, [add C, mirror R, add R, mirror R],
    [".#.", "###"]⟩,
  -- (A_C^(2)+1_R)_C+1_C
  ⟨"tetromino 7", C, 2, [add R, push C, add C],
    ["#.", "##", "#."]⟩,
  -- (A_R^(3)+1_C)^M_C
  ⟨"tetromino 8", R, 3, [add C, mirror C],
    ["#..", "###"]⟩,
  -- A_C^(3)+1_R
  ⟨"tetromino 9", C, 3, [add R],
    ["##", "#.", "#."]⟩,
  -- (A_R^(3)+1_C)^M
  ⟨"tetromino 10", R, 3, [add C, mirror R],
    ["###", "..#"]⟩,
  -- ((A_C^(3)+1_R)^M)^M_C
  ⟨"tetromino 11", C, 3, [add R, mirror R, mirror C],
    [".#", ".#", "##"]⟩,
  -- (A_C^(3)+1_R)^M
  ⟨"tetromino 12", C, 3, [add R, mirror R],
    ["#.", "#.", "##"]⟩,
  -- ((A_R^(3)+1_C)^M)^M_C
  ⟨"tetromino 13", R, 3, [add C, mirror R, mirror C],
    ["###", "#.."]⟩,
  -- (A_C^(3)+1_R)^M_C
  ⟨"tetromino 14", C, 3, [add R, mirror C],
    ["##", ".#", ".#"]⟩,
  -- A_R^(3)+1_C
  ⟨"tetromino 15", R, 3, [add C],
    ["..#", "###"]⟩,
  -- (A_R^(2)+1_C)_C+1_R
  ⟨"tetromino 16", R, 2, [add C, push C, add R],
    [".##", "##."]⟩,
  -- ((A_C^(2)+1_R)_R+1_C)^M
  ⟨"tetromino 17", C, 2, [add R, push R, add C, mirror R],
    ["#.", "##", ".#"]⟩,
  -- ((A_R^(2)+1_C)_C+1_R)^M
  ⟨"tetromino 18", R, 2, [add C, push C, add R, mirror R],
    ["##.", ".##"]⟩,
  -- (A_C^(2)+1_R)_R+1_C
  ⟨"tetromino 19", C, 2, [add R, push R, add C],
    [".#", "##", "#."]⟩,
  -- (((((((A_C^(2)+1_R)^M)_C+1_R)_P+1_C)_R+1_R)^M)^M_C+1_C)+1_R
  ⟨"pin example", C, 2,
    [add R, mirror R, push C, add R, pin, add C, push R, add R, mirror R, mirror C,
     add C, add R],
    ["..#.", ".###", "###.", ".#.."]⟩,
  -- (((A_R^(2)+1_C)^M_R)_R+1_R)_C+1_C
  ⟨"plus pentomino", R, 2, [add C, mirror R, push R, add R, push C, add C],
    [".#.", "###", ".#."]⟩,
  -- (((A_R^(2)+1_C)_C+1_R)+1_C)^M
  ⟨"staircase", R, 2, [add C, push C, add R, add C, mirror R],
    ["##.", ".##", "..#"]⟩,
  -- (((((A_C^(3)+1_R)+1_R)^M)_C+1_R)+1_C)+1_C
  ⟨"3x3 ring", C, 3, [add R, add R, mirror R, push C, add R, add C, add C],
    ["###", "#.#", "###"]⟩,
  -- part 2's carving formula (subtraction + two pins)
  ⟨"part 2 carving", R, 3,
    [add C, push C, add C, mirror C, add C, push C, pin, add C, push C, add C, add C,
     add C, add C, mirror C, sub R, pin, sub R, push C, add R, push C, add R],
    ["###", "#.#", "#..", "#.#", "###"]⟩
]

def Example.ok (e : Example) : Bool := shapeOf e.base e.len e.ops == some (pic e.want)

theorem examples_ok : examples.all (·.ok) = true := by decide +kernel

-- Look at what a formula actually builds:
#eval IO.println (draw C 2 [add R, mirror R, push C, add R])   -- tetromino 3

/-! ## 7. Facts Lean checks by running the rules

`by decide` means: Lean evaluates both sides and confirms the statement. -/

-- A_R^(1) and A_C^(1) are the same cell but not the same starting point.
theorem strips_of_one_differ :
    shapeOf R 1 [add R, add C, mirror C, add C] ≠ shapeOf C 1 [add R, add C, mirror C, add C] := by
  decide +kernel

/-- Part 2's rule  `A_X^j (1_Y·(j-1)) M_Y  =  A_Y^j (1_X·(j-1)) M_X X`,  for X = C, Y = R. -/
def swapLeft  (j : Nat) (rest : List Op) := shapeOf C j (List.replicate (j - 1) (add R) ++ [mirror R] ++ rest)
def swapRight (j : Nat) (rest : List Op) := shapeOf R j (List.replicate (j - 1) (add C) ++ [mirror C, push C] ++ rest)

-- For every j from 2 to 9 both sides draw the same shape...
theorem swap_same_shape : ∀ j < 10, 2 ≤ j → swapLeft j [] = swapRight j [] := by
  decide +kernel
-- ...but one more `+1_C` lands in different places, so it can't be substituted.
-- The trailing push sets the latch to C and also arms "most cells" for the next ±1.
theorem swap_not_substitutable : ∀ j < 10, 2 ≤ j → swapLeft j [add C] ≠ swapRight j [add C] := by
  decide +kernel

/-- Pushing before the last `1_X` instead:
    `A_X^j (1_Y·(j-1)) M_Y  =  A_Y^j (1_X·(j-2)) X 1_X M_X`.
    The whole state matches (shape, latch, push, pin), so it substitutes anywhere. -/
theorem swap_fixed_C : ∀ j < 16, 2 ≤ j →
    eval C j (List.replicate (j - 1) (add R) ++ [mirror R]) =
    eval R j (List.replicate (j - 2) (add C) ++ [push C, add C, mirror C]) := by
  decide +kernel
theorem swap_fixed_R : ∀ j < 16, 2 ≤ j →
    eval R j (List.replicate (j - 1) (add C) ++ [mirror C]) =
    eval C j (List.replicate (j - 2) (add R) ++ [push R, add R, mirror R]) := by
  decide +kernel

-- Subtraction can split a shape in two.
#eval IO.println (draw C 3 [add R, push R, mirror C, sub R])

