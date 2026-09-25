# Jittered Voronoi diagrams: which neighbourhood determines a cell?

A *jitter* puts one point (a *site*) in every square in a unit square grid `[a, a+1) × [b, b+1)`, `(a, b) ∈ ℤ²`. The Voronoi cell of a site is the set of points of the plane at least as close to it
as to every other site. 

A *jitter* is infinite, but the easiest way to compute it's Voronoi cells is to take a small 
neighborhood of sites and compute their Voronoi cells from a finite Voronoi digram. With the right
neighborhood, some of sites from finite diagram will match the infinite case.

So the question is, what is the smallest neighborhood you need to use to accurately compute
the Voronoi cell of the site for the (0, 0) square (wlog).

The answer is a `7 × 7` block around the origin with the three cells at each corner removed:

```
 .  .  X  X  X  .  .
 .  X  X  X  X  X  .
 X  X  X  X  X  X  X
 X  X  X  o  X  X  X
 X  X  X  X  X  X  X
 .  X  X  X  X  X  .
 .  .  X  X  X  .  .
```

This repo contains lean code that *proves* it.

## Statement

We define Voronoi cells in terms of points that are closed by squared euclidian distance. 
(see `voronoiDist_eq` which proves it doesn't matter if you square the distance or not).

```lean
/-- Squared Euclidean distance on `ℝ × ℝ`. -/
def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A jitter is a function picking a site in every square in an infite square grid  -/
def IsJitter (f : ℤ × ℤ → ℝ × ℝ) : Prop :=
  ∀ c : ℤ × ℤ, (f c).1 ∈ Set.Ico (c.1 : ℝ) (c.1 + 1) ∧ (f c).2 ∈ Set.Ico (c.2 : ℝ) (c.2 + 1)

variable {ι : Type*}

/-- Returns the voronoi diagram for a set of sites f filtered to neighborhood N
    Returns empty set sites outside N.

    ι will be the full square grid ℤ × ℤ, and  N will be the finite neighbourhood.
    --/
def voronoiOn (f : ι → ℝ × ℝ) (N : Set ι) (x : ι) : Set (ℝ × ℝ) :=
  {p | x ∈ N ∧ ∀ y ∈ N, sqDist p (f x) ≤ sqDist p (f y)}

/-- Returns the voronoi diagram for a set of sites, with no filter. -/
abbrev voronoi (f : ι → ℝ × ℝ) (x : ι) : Set (ℝ × ℝ) := voronoiOn f Set.univ x
```

Now we define what we're looking for

```lean
/-- A sufficient neighborhood is one where you always get the same Voronoi
site for (0, 0) when restricted to the neighborhood or not -/
def SufficientNbhd (N : Set (ℤ × ℤ)) : Prop :=
  ∀ f, IsJitter f → voronoiOn f N (0, 0) = voronoi f (0, 0)

/-- Here's our claimed answer --/
def Nbhd : Set (ℤ × ℤ) :=
  {c | c.1.natAbs ≤ 3 ∧ c.2.natAbs ≤ 3 ∧ c.1.natAbs + c.2.natAbs ≤ 4}

/-- Assert it is indeed sufficient, and minimal -/
theorem nbhd_isLeast : IsLeast {N | SufficientNbhd N} Nbhd
```

## Proof

*Sufficiency* (`Blocking.lean`). Fix the origin's site `(x₀, y₀)` and a test point `p = (u, v)`.
Say a cell *threatens* `p` if it contains a point strictly closer to `p` than `(x₀, y₀)`, and
*blocks* `p` if all its points are strictly closer. The key lemma `hasBlocker_of_threat` says
that if any cell outside `Nbhd` threatens `p`, some non-origin cell of `Nbhd` blocks `p`; so `p`
is already excluded from the local Voronoi cell.

* If `u ≥ 5/2` (or the mirror images), the column `x ∈ [2, 3]` in the row of `v` blocks,
  whatever the threat (`far_right`).
* Otherwise `p` lies in `(-3/2, 5/2)²` and the threatening cell is reduced, by monotonicity, to
  one of three frontier configurations: a threat from `x ≥ 4` in the rows `0 ≤ y ≤ 1` or
  `1 ≤ y ≤ 2` (`coreR0`, `coreR1`, blocked by `(2, 1)`, `(2, 0)` or `(2, -1)` depending on
  `v`), and a threat from the quadrant `x ≥ 3`, `y ≥ 2` (`coreD`, blocked by `(2, 1)`, `(1, 1)`
  or `(1, 2)`). Each case is a corner-by-corner bound followed by (non)linear arithmetic.

To use the reflections `x ↦ 1 - x`, `y ↦ 1 - y` and the swap `x ↔ y` legitimately despite the
half-open cells, the proof is carried out for an abstract cell convention (`CellStructure` in
`Cell.lean`): a family of sets `I a ⊆ [a, a+1]` with `x' - x > a' - a - 1` for `x ∈ I a`,
`x' ∈ I a'`, `a < a'`. Both half-open conventions satisfy this, and the axioms are stable under
reflection. The half-openness is essential — with closed cells the statement is false — and it
enters exactly through this separation axiom.

*Necessity* (`Witness.lean`).
We simply supply seven "witnesses" which are a specific assignment of sites and a point to test, which
break if you don't include a specific cell in the neighborhood. The finitely many comparisons in the window 
`|a|, |b| ≤ 5` are checked by `decide +kernel` for all 36 cells; cells farther out are trivially far.


These witnesses are mirrored to cover all 36 cells.

## Building

```
lake exe cache get   # Mathlib oleans
lake build
```
