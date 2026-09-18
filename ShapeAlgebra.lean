/-
  Shape algebra for polyominoes.

  ShapeAlgebra/Basic.lean       the rules
  ShapeAlgebra/Examples.lean    every formula in the posts, checked against its picture
  ShapeAlgebra/Size.lean        substitution, and S ≥ N − j
  ShapeAlgebra/Blocked.lean     item 1: without subtraction, some cell can always be added last
  ShapeAlgebra/Swap.lean        item 2: swapping R and C flips the shape along the diagonal
  ShapeAlgebra/Conjecture.lean  item 4: the open question, and why one orientation is enough
  ShapeAlgebra/Coverage.lean    item 3: every shape up to 7 cells, and the 100 blocked shapes
  ShapeAlgebra/Data/            formulas found by the Python search (generated)
-/
import ShapeAlgebra.Basic
import ShapeAlgebra.Examples
import ShapeAlgebra.Size
import ShapeAlgebra.Blocked
import ShapeAlgebra.Swap
import ShapeAlgebra.Conjecture
import ShapeAlgebra.Coverage
