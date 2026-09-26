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

/-- `f` is a jitter: the site of cell `c` lies in the closed square cell
`[c.1, c.1 + 1] × [c.2, c.2 + 1]`, and distinct cells get distinct sites. -/
structure IsJitter (f : ℤ × ℤ → ℝ × ℝ) : Prop where
  mem : ∀ c : ℤ × ℤ, (f c).1 ∈ Set.Icc (c.1 : ℝ) (c.1 + 1) ∧ (f c).2 ∈ Set.Icc (c.2 : ℝ) (c.2 + 1)
  injective : Function.Injective f

/-- The usual half-open model: one site in each cell `[c.1, c.1 + 1) × [c.2, c.2 + 1)`. -/
def IsJitterIco (f : ℤ × ℤ → ℝ × ℝ) : Prop :=
  ∀ c : ℤ × ℤ, (f c).1 ∈ Set.Ico (c.1 : ℝ) (c.1 + 1) ∧ (f c).2 ∈ Set.Ico (c.2 : ℝ) (c.2 + 1)

/-- A half-open jitter is a jitter: the half-open cells are disjoint, so its sites are distinct. -/
theorem IsJitterIco.isJitter {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitterIco f) : IsJitter f where
  mem c := ⟨Set.Ico_subset_Icc_self (hf c).1, Set.Ico_subset_Icc_self (hf c).2⟩
  injective c d e := by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hf c
    obtain ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩ := hf d
    rw [e] at h1 h2 h3 h4
    have e1 : c.1 < d.1 + 1 := by exact_mod_cast (show (c.1 : ℝ) < d.1 + 1 by linarith)
    have e2 : d.1 < c.1 + 1 := by exact_mod_cast (show (d.1 : ℝ) < c.1 + 1 by linarith)
    have e3 : c.2 < d.2 + 1 := by exact_mod_cast (show (c.2 : ℝ) < d.2 + 1 by linarith)
    have e4 : d.2 < c.2 + 1 := by exact_mod_cast (show (d.2 : ℝ) < c.2 + 1 by linarith)
    exact Prod.ext (by omega) (by omega)

section Voronoi

variable {ι : Type*}

/-- The Voronoi cell of the site `f x` computed from the sites `f y`, `y ∈ N`, only: the points
at least as close to `f x` as to every such `f y`.  It is empty unless `x ∈ N`. -/
def voronoiOn (f : ι → ℝ × ℝ) (N : Set ι) (x : ι) : Set (ℝ × ℝ) :=
  {p | x ∈ N ∧ ∀ y ∈ N, sqDist p (f x) ≤ sqDist p (f y)}

/-- The Voronoi cell of the site `f x` among all sites. -/
abbrev voronoi (f : ι → ℝ × ℝ) (x : ι) : Set (ℝ × ℝ) := voronoiOn f Set.univ x

theorem mem_voronoiOn_iff {f : ι → ℝ × ℝ} {N : Set ι} {x : ι} {p : ℝ × ℝ} :
    p ∈ voronoiOn f N x ↔ x ∈ N ∧ ∀ y ∈ N, sqDist p (f x) ≤ sqDist p (f y) := Iff.rfl

theorem mem_voronoi_iff {f : ι → ℝ × ℝ} {x : ι} {p : ℝ × ℝ} :
    p ∈ voronoi f x ↔ ∀ y, sqDist p (f x) ≤ sqDist p (f y) := by
  simp [voronoiOn]

theorem voronoiOn_eq_empty (f : ι → ℝ × ℝ) {N : Set ι} {x : ι} (hx : x ∉ N) :
    voronoiOn f N x = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hp => hx hp.1

/-- The site itself lies in its Voronoi cell. -/
theorem site_mem_voronoiOn (f : ι → ℝ × ℝ) {N : Set ι} {x : ι} (hx : x ∈ N) :
    f x ∈ voronoiOn f N x :=
  ⟨hx, fun y _ => by
    unfold sqDist
    nlinarith [sq_nonneg ((f x).1 - (f y).1), sq_nonneg ((f x).2 - (f y).2)]⟩

theorem voronoi_nonempty (f : ι → ℝ × ℝ) (x : ι) : (voronoi f x).Nonempty :=
  ⟨f x, site_mem_voronoiOn f (Set.mem_univ x)⟩

/-- The local Voronoi cell is the Voronoi cell of the restricted family. -/
theorem voronoi_restrict (f : ι → ℝ × ℝ) (N : Set ι) (x : N) :
    voronoi (fun y : N => f y) x = voronoiOn f N x := by
  ext p
  simp [voronoi, voronoiOn, x.property]

theorem voronoiOn_anti (f : ι → ℝ × ℝ) {N M : Set ι} (h : N ⊆ M) {x : ι} (hx : x ∈ N) :
    voronoiOn f M x ⊆ voronoiOn f N x :=
  fun _ hp => ⟨hx, fun y hy => hp.2 y (h hy)⟩

theorem voronoi_subset_voronoiOn (f : ι → ℝ × ℝ) {N : Set ι} {x : ι} (hx : x ∈ N) :
    voronoi f x ⊆ voronoiOn f N x :=
  voronoiOn_anti f (Set.subset_univ N) hx

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
