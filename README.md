# Shape algebra in Lean

A formal model of the polyomino algebra from the blog posts
"Algebra for Polyominoes" and "Formula reduction for Polyominoes".

## Results

### Proved in Lean

`lake build` checks every one of these.

| Result | File |
|---|---|
| Every fixed polyomino with up to 7 cells (1,067 shapes) can be built without subtraction[^count] | `Coverage.lean` |
| If no cell of a shape could have been the last one added ("blocked"), every formula for it uses subtraction | `Blocked.lean` |
| 100 blocked shapes with 11–14 cells: each needs subtraction, and each has a formula that builds it | `Coverage.lean` |
| Part 2's swap rule is a perfect substitution when both sides are followed by a latch Z: `A_X^j(1_Y·(j−1))M_Y Z = A_Y^j(1_X·(j−1))M_X Z` leaves the same state for X, Z ∈ {R, C} (j = 1…15) | `Examples.lean` |
| It also substitutes anywhere with the push moved before the last `1_X`: `A_X^j(1_Y·(j−1))M_Y = A_Y^j(1_X·(j−2)) X 1_X M_X` (X ∈ {R, C}, j = 2…15) | `Examples.lean` |
| A shape can be built exactly when each of its 8 rotations and reflections can (swapping R and C in a formula flips its shape along the diagonal) | `Swap.lean`, `Conjecture.lean` |

[^count]: "Every" rests on one outside fact: the table sizes 1, 2, 6, 19, 63, 216, 760 are the known counts of fixed polyominoes (OEIS A001168).

### Inferred from Python

Exhaustive searches. Evidence, not proof.

| Result | Script |
|---|---|
| Every fixed polyomino with up to 10 cells (50,148 shapes) can be built without subtraction | `python/coverage.py` |
| Blocked shapes first appear at 11 cells: there are 4, 4, 36 and 56 with 11–14 cells, the 100 in the Lean table above | `python/peel.py` |
| Each of those 100 can be built with at most one cell outside the shape at any time | `python/experiment.py` |

Still open: whether every polyomino can be built. It is stated precisely in `Conjecture.lean`.

## Run the Lean proofs

    cd ~/Desktop/shape-algebra
    lake build          # about 3 minutes; "Build completed successfully" = every proof checked

Lean lives in `~/.elan`. If `lake` isn't found, add this to `~/.zshrc`:

    export PATH="$HOME/.elan/bin:$PATH"

## Rerun the Python experiments

From `python/`:

    python3 test.py            # the 24 formulas from the posts (seconds)
    python3 peel.py 14         # count blocked shapes up to 14 cells (~4 min)
    python3 experiment.py      # one-filler search on the 100 blocked shapes (~10 min)
    python3 coverage.py 10     # a formula for every shape up to 10 cells (~25 min)

Then, from the project root, regenerate the Lean data tables:

    python3 python/make_lean_data.py 7

## Files

    ShapeAlgebra/Basic.lean        the rules
    ShapeAlgebra/Examples.lean     the posts' formulas, checked against their pictures
    ShapeAlgebra/Size.lean         substitution works anywhere; S ≥ N − j
    ShapeAlgebra/Blocked.lean      without subtraction, some cell can always be added last
    ShapeAlgebra/Swap.lean         R↔C swap = diagonal flip
    ShapeAlgebra/Conjecture.lean   the open question; one orientation is enough
    ShapeAlgebra/Coverage.lean     shapes up to 7 cells, and the 100 blocked shapes
    ShapeAlgebra/Data/             formula tables generated from the Python search
    python/sim.py                  first simulator of the rules
    python/search.py               formula search
    python/check.py                re-checks a search result with sim.py
    python/polys.py                lists every polyomino
