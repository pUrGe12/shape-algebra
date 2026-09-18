# Shape algebra in Lean

A formal model of the polyomino algebra from the blog posts
"Algebra for Polyominoes" and "Formula reduction for Polyominoes".

## Results

| Claim | Status |
|---|---|
| All 24 formulas in the posts vs. their pictures | 21 match; 3 are typos in the posts (`ShapeAlgebra/Examples.lean`) |
| Part 2's rule `A_X^j(1_Y·(j−1))M_Y = A_Y^j(1_X·(j−1))M_X X` | False as a substitution rule (proved in `Examples.lean`) |
| Every shape up to 7 cells builds without subtraction | Proved in Lean (`Coverage.lean`) |
| Every shape up to 10 cells builds without subtraction | Checked in Python (`python/coverage.py`) |
| Shapes where no cell can be added last need subtraction | Proved for every formula (`Blocked.lean`) |
| Such "blocked" shapes: 0 up to 10 cells, then 4, 4, 36, 56 at 11–14 | Python (`python/peel.py`) |
| All 100 blocked shapes build with one filler cell | Search in Python, formulas checked in Lean (`Coverage.lean`) |
| Swapping R and C flips the shape along the diagonal | Proved for every formula (`Swap.lean`) |
| One orientation of a shape is enough (all 8 follow) | Proved (`Conjecture.lean`) |
| Every polyomino can be built | Open; stated precisely in `Conjecture.lean` |

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
