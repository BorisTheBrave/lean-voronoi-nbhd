import Mathlib

/-!
# Basic definitions

Jitters, the squared Euclidean distance, and Voronoi cells (global and relative to a set of
sites).  The Voronoi cell of a site is the set of points of the plane at least as close to it as
to every other site; `voronoiOn f N x` uses only the sites `f y` with `y ∈ N`, and is the Voronoi
cell of the restricted family `f ∘ Subtype.val : N → ℝ × ℝ` (`voronoi_restrict`).

Squared distances are used throughout because Mathlib's metric on `ℝ × ℝ` is the sup metric;
`voronoiDist_eq` shows that the genuine Euclidean distance gives the same cells.
-/

namespace JitteredVoronoi

/-- Squared Euclidean distance on `ℝ × ℝ`. -/
def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Squared Euclidean distance over `ℚ`. -/
def sqQ (p q : ℚ × ℚ) : ℚ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

lemma sqQ_eq_sqDist (p q : ℚ × ℚ) : sqQ p q = sqDist (p.1, p.2) (q.1, q.2) := by
  unfold sqDist sqQ
  simp

/-- `f` is a jitter: the site of cell `c` lies in side the square cell `[c.1, c.1 + 1) × [c.2, c.2 + 1)`. -/
def IsJitter (f : ℤ × ℤ → ℝ × ℝ) : Prop :=
  ∀ c : ℤ × ℤ, (f c).1 ∈ Set.Ico (c.1 : ℝ) (c.1 + 1) ∧ (f c).2 ∈ Set.Ico (c.2 : ℝ) (c.2 + 1)

section Voronoi

variable {ι : Type*}

/-- The Voronoi cell of the site `f x` computed from the sites `f y`, `y ∈ N`, only: the points
at least as close to `f x` as to every such `f y`. -/
def voronoiOn (f : ι → ℝ × ℝ) (N : Set ι) (x : ι) : Set (ℝ × ℝ) :=
  {p | ∀ y ∈ N, sqDist p (f x) ≤ sqDist p (f y)}

/-- The Voronoi cell of the site `f x` among all sites. -/
abbrev voronoi (f : ι → ℝ × ℝ) (x : ι) : Set (ℝ × ℝ) := voronoiOn f Set.univ x

theorem mem_voronoi_iff {f : ι → ℝ × ℝ} {x : ι} {p : ℝ × ℝ} :
    p ∈ voronoi f x ↔ ∀ y, sqDist p (f x) ≤ sqDist p (f y) := by
  simp [voronoiOn]

/-- The local Voronoi cell is the Voronoi cell of the restricted family. -/
theorem voronoi_restrict (f : ι → ℝ × ℝ) (N : Set ι) (x : N) :
    voronoi (fun y : N => f y) x = voronoiOn f N x := by
  ext p
  simp [voronoi, voronoiOn]

theorem voronoiOn_anti (f : ι → ℝ × ℝ) {N M : Set ι} (h : N ⊆ M) (x : ι) :
    voronoiOn f M x ⊆ voronoiOn f N x :=
  fun _ hp y hy => hp y (h hy)

theorem voronoi_subset_voronoiOn (f : ι → ℝ × ℝ) (N : Set ι) (x : ι) :
    voronoi f x ⊆ voronoiOn f N x :=
  voronoiOn_anti f (Set.subset_univ N) x

end Voronoi

/-! ### Euclidean distance instead of squared distance -/

theorem sqDist_nonneg (p q : ℝ × ℝ) : 0 ≤ sqDist p q := by
  unfold sqDist; positivity

/-- Embed `ℝ × ℝ` into the Euclidean plane. -/
def toE (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![p.1, p.2]

theorem dist_toE (p q : ℝ × ℝ) : dist (toE p) (toE q) = Real.sqrt (sqDist p q) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [toE, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.dist_eq, sq_abs, sqDist]

/-- The Voronoi cell defined with the genuine Euclidean distance. -/
def voronoiDist {ι : Type*} (f : ι → ℝ × ℝ) (x : ι) : Set (ℝ × ℝ) :=
  {p | ∀ y, dist (toE p) (toE (f x)) ≤ dist (toE p) (toE (f y))}

/-- Squared and genuine Euclidean distance give the same Voronoi cells. -/
theorem voronoiDist_eq {ι : Type*} (f : ι → ℝ × ℝ) (x : ι) : voronoiDist f x = voronoi f x := by
  ext p
  simp only [voronoiDist, Set.mem_ofPred_eq, dist_toE, mem_voronoi_iff]
  exact forall_congr' fun y => Real.sqrt_le_sqrt_iff (sqDist_nonneg _ _)

end JitteredVoronoi
