import Mathlib

/-!
# Jittered grids: which cells can hold the nearest neighbour?

A *jitter* places one point in every unit cell `[a, a+1) × [b, b+1)` of the integer grid
(`a b : ℤ`).  Looking from the point of the origin cell `(0, 0)`, we ask which other cells
`(A, B)` can contain the point nearest to it, over all possible jitters.

This file holds the definitions; `Necessity.lean` proves that only cells in the `5 × 5` block
minus its four corners can occur, `Construction.lean` shows every such cell does occur, and
`Main.lean` combines both into the characterisation `NearestCells = Answer`.
-/

namespace JitteredVoronoi

/-- Squared Euclidean distance on `ℝ × ℝ`.  (The product metric Mathlib installs on `ℝ × ℝ` is
the sup metric, so we spell out the Euclidean one; `Main.lean` relates it to the Euclidean
distance on `EuclideanSpace ℝ (Fin 2)`.) -/
def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- `f` is a jitter: cell `(a, b)` is assigned a point of `[a, a+1) × [b, b+1)`. -/
def IsJitter (f : ℤ → ℤ → ℝ × ℝ) : Prop :=
  ∀ a b : ℤ, (f a b).1 ∈ Set.Ico (a : ℝ) (a + 1) ∧ (f a b).2 ∈ Set.Ico (b : ℝ) (b + 1)

/-- Under the jitter `f`, the (non-origin) cell `(A, B)` holds a point at least as close to
`f 0 0` as the point of any other non-origin cell.  Ties are allowed. -/
def IsNearest (f : ℤ → ℤ → ℝ × ℝ) (A B : ℤ) : Prop :=
  (A, B) ≠ (0, 0) ∧
    ∀ a b : ℤ, (a, b) ≠ (0, 0) → sqDist (f A B) (f 0 0) ≤ sqDist (f a b) (f 0 0)

/-- The cells that can hold the nearest neighbour of the origin cell's point, over all jitters. -/
def NearestCells : Set (ℤ × ℤ) :=
  {c | ∃ f : ℤ → ℤ → ℝ × ℝ, IsJitter f ∧ IsNearest f c.1 c.2}

/-- The claimed answer: the `5 × 5` block around the origin, minus the origin and the four
corners `(±2, ±2)`.  Twenty cells. -/
def Answer : Set (ℤ × ℤ) :=
  {c | c ≠ (0, 0) ∧ |c.1| ≤ 2 ∧ |c.2| ≤ 2 ∧ ¬ (|c.1| = 2 ∧ |c.2| = 2)}

lemma sqDist_nonneg (p q : ℝ × ℝ) : 0 ≤ sqDist p q := by
  unfold sqDist; positivity

end JitteredVoronoi
