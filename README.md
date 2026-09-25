# Jittered grids: what is the local neighborhood

A [Jittered Voronoi grid](https://www.boristhebrave.com/docs/sylves/1/articles/grids/jitteredsquaregrid.html) is 
constructed by starting with a square grid, picking a random point for each cell, and constructing an
infinite Voronoi diagram.

To construct an infinite Voronoi diagram, one typically builds it cell by cell. To get one cell of the output,
consider a neighborhood of the input point, build a finite Voronoi diagram on that, and copy the central polygon
of the diagram into the output.

With a sufficiently neighborhood, this always gives an accurate result. But what is that neighborhood? This lean repo
proves that it's the following circle of 21 points (a 5 × 5 without corners).

```
 .  X  X  X  .
 X  X  X  X  X
 X  X  o  X  X
 X  X  X  X  X
 .  X  X  X  .
```


We define a *jitter* as a function that puts one point in every unit cell `[a, a+1) × [b, b+1)` (`a, b : ℤ`) of the plane.


From the point of the origin cell `(0, 0)`, which other cells `(A, B)` can contain the point
nearest to it, over all jitters?


**Answer (proved here):** exactly the `5 × 5` block around the origin with the origin and the
four corners `(±2, ±2)` removed. Twenty cells:


So the `3 × 3` neighbourhood is not enough (`(2, 1)` can be nearest), and the full `5 × 5`
block is more than needed (`(2, 2)` never is).

## Statement

`JitteredVoronoi/Basic.lean` defines

* `sqDist p q` – squared Euclidean distance on `ℝ × ℝ`;
* `IsJitter f` – `f a b ∈ [a, a+1) × [b, b+1)` for all `a b : ℤ`;
* `IsNearest f A B` – `(A, B) ≠ (0, 0)` and `sqDist (f A B) (f 0 0) ≤ sqDist (f a b) (f 0 0)`
  for every `(a, b) ≠ (0, 0)` (ties allowed);
* `NearestCells = {c | ∃ f, IsJitter f ∧ IsNearest f c.1 c.2}`;
* `Answer = {c | c ≠ (0, 0) ∧ |c.1| ≤ 2 ∧ |c.2| ≤ 2 ∧ ¬(|c.1| = 2 ∧ |c.2| = 2)}`.

`JitteredVoronoi/Main.lean` proves

```lean
theorem nearestCells_eq_answer : NearestCells = Answer
theorem nearestCells_eq_finset : NearestCells = ↑Construction.answerList.toFinset
theorem card_answer : Construction.answerList.toFinset.card = 20
theorem two_one_mem : (2, 1) ∈ NearestCells
theorem two_two_not_mem : (2, 2) ∉ NearestCells
theorem threeBox_subset : (A, B) ≠ (0, 0) → |A| ≤ 1 → |B| ≤ 1 → (A, B) ∈ NearestCells
theorem subset_fiveBox : (A, B) ∈ NearestCells → |A| ≤ 2 ∧ |B| ≤ 2
theorem nearestCells_dist_eq_answer :
    {c | ∃ f, IsJitter f ∧ IsNearestDist f c.1 c.2} = Answer
```

The last one restates the result with the genuine Euclidean distance on
`EuclideanSpace ℝ (Fin 2)` instead of `sqDist`.

All theorems depend only on `propext`, `Classical.choice`, `Quot.sound` (no `sorry`, no
`native_decide`).

## Proof

*Necessity* (`Necessity.lean`). Write `(x₀, y₀) = f 0 0 ∈ [0, 1)²`. Every point of cell `(1, 0)`
has squared distance `< (2 − x₀)² + 1`, every point of cell `(−1, 0)` has squared distance
`< (x₀ + 1)² + 1`, and symmetrically for `(0, ±1)`. If `A ≥ 3`, or `A = 2` and `|B| = 2`, every
point of cell `(A, B)` has squared distance `≥ (2 − x₀)² + 1`, so `(A, B)` is beaten by `(1, 0)`.
The remaining cases are mirror images (`nlinarith` does the algebra).

*Sufficiency* (`Construction.lean`). For a target `(A, B)` in `Answer`, the origin point is
`(1/2 + sgn A/10, 1/2 + sgn B/10)`, the target point is the corner of its cell nearest to the
origin point (moved inward by `1/100` when that corner is excluded by half-openness), and every
other cell gets a point as far from the origin point as its half-open cell allows (again up to
`1/100`). All coordinates are rational, so the `20 × 23` comparisons inside the `5 × 5` block are
checked by `decide +kernel`; cells outside the block are at squared distance `≥ 4`, while the
target is at squared distance `≤ 4`.

## Remarks

* The grid is indexed by `ℤ × ℤ`, not `ℕ × ℕ`, since the plane is tiled in every direction.
* Because cells are half-open, the answer is sensitive to the convention: with closed cells and
  ties allowed, `(2, 2)` would tie with `(1, 0)` for the origin point `(1, 1)`. With the
  half-open convention there is no such tie, and allowing or forbidding ties gives the same set.
* This is the nearest-neighbour question only. The Voronoi cell of a point is determined by all
  its Voronoi neighbours, which can be farther away than its nearest neighbour, so the fact that
  `5 × 5` suffices for the Voronoi cell is a separate (stronger) statement not proved here.

## Building

```
lake exe cache get   # Mathlib oleans
lake build
```
