# Jittered Voronoi diagrams: which neighbourhood determines a cell?

A *jitter* puts one point (a *site*) in every unit cell `[a, a+1) × [b, b+1)`, `(a, b) ∈ ℤ²`, of
the plane. The Voronoi cell of a site is the set of points of the plane at least as close to it
as to every other site. Computing the Voronoi cell of the origin's site from the sites in a
neighbourhood `N` of cells only gives a set that contains the true cell; when is it equal, for
every jitter?

**Answer (proved here):** exactly when `N` contains the 36 cells

```
|a| ≤ 3,  |b| ≤ 3,  |a| + |b| ≤ 4,  (a, b) ≠ (0, 0)
```

i.e. the `7 × 7` block around the origin with the three cells at each corner removed:

```
 .  .  X  X  X  .  .
 .  X  X  X  X  X  .
 X  X  X  X  X  X  X
 X  X  X  o  X  X  X
 X  X  X  X  X  X  X
 .  X  X  X  X  X  .
 .  .  X  X  X  .  .
```

In particular the `5 × 5` block is **not** enough: the site of the cell `(3, 0)` can be a
Voronoi neighbour of the origin's site (`three_zero_needed`). The `7 × 7` block is more than
needed: the cell `(3, 2)` never matters (`three_two_not_needed`).

## Statement

`JitteredVoronoi/Voronoi.lean` defines

* `sqDist p q` – squared Euclidean distance on `ℝ × ℝ`;
* `IsJitter f` – `f c ∈ [c.1, c.1+1) × [c.2, c.2+1)` for all `c : ℤ × ℤ`;
* `voronoi f x = {p | ∀ y, sqDist p (f x) ≤ sqDist p (f y)}` – the Voronoi cell of the site `f x`;
* `voronoiOn f N x` – the same with `y` ranging over `N` only; `voronoi_restrict` shows it is the
  Voronoi cell of the restricted family `f ∘ Subtype.val : N → ℝ × ℝ`;

and `JitteredVoronoi/Nbhd.lean` defines `Nbhd = {(a, b) | |a| ≤ 3, |b| ≤ 3, |a| + |b| ≤ 4}`
(37 cells including the origin). The main results are

```lean
theorem voronoiOn_eq_voronoi_iff (N : Set (ℤ × ℤ)) :
    (∀ f, IsJitter f → voronoiOn f N (0, 0) = voronoi f (0, 0)) ↔ Nbhd \ {(0, 0)} ⊆ N

theorem voronoi_restrict_eq_iff (N : Set (ℤ × ℤ)) (h0 : (0, 0) ∈ N) :
    (∀ f, IsJitter f → voronoi (fun y : N => f y) ⟨(0, 0), h0⟩ = voronoi f (0, 0)) ↔ Nbhd ⊆ N

theorem voronoi_eq_voronoiOn_Nbhd (hf : IsJitter f) : voronoi f (0, 0) = voronoiOn f Nbhd (0, 0)

theorem exists_jitter_voronoiOn_ne (hc : c ∈ Nbhd) (h0 : c ≠ (0, 0)) :
    ∃ f, IsJitter f ∧ ∃ p, p ∈ voronoiOn f {c}ᶜ (0, 0) ∧ p ∉ voronoi f (0, 0)

theorem voronoiDist_eq (f : ι → ℝ × ℝ) (x : ι) : voronoiDist f x = voronoi f x
```

The last one says that using the genuine Euclidean distance on `EuclideanSpace ℝ (Fin 2)`
instead of `sqDist` gives the same cells. Everything depends only on `propext`,
`Classical.choice`, `Quot.sound` (no `sorry`, no `native_decide`).

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

*Necessity* (`Witness.lean`). For each of the 36 cells an explicit rational jitter and test point
are listed in `table`. The site in the cell under test is the point of that cell nearest to the
test point; every other cell gets its corner farthest from the test point (moved inside the
half-open cell by `1/100` if needed). The finitely many comparisons in the window `|a|, |b| ≤ 5`
are checked by `decide +kernel`; cells farther out are trivially far.

## Building

```
lake exe cache get   # Mathlib oleans
lake build
```
