import JitteredVoronoi.Blocking
import JitteredVoronoi.Witness

/-!
# Jittered Voronoi diagrams: which neighbourhood determines the origin's cell?

A *jitter* `f : ℤ × ℤ → ℝ × ℝ` puts one point in every unit cell `[a, a+1) × [b, b+1)`.  The
Voronoi cell of the site `f x` is the set of points of the plane at least as close to `f x` as
to every other site.  Computing it from a neighbourhood `N` of cells only (ignoring the sites
outside `N`) gives a possibly larger set `voronoiOn f N x`.

**Main theorem** (`voronoiOn_eq_voronoi_iff`): the local computation is exact for the origin
cell and *every* jitter if and only if `N` contains the 36 cells
`{(a, b) ≠ (0, 0) | |a| ≤ 3, |b| ≤ 3, |a| + |b| ≤ 4}` — the `7 × 7` block minus the three cells
at each corner.  In particular the `5 × 5` block is not enough (the cell `(3, 0)` can be a
Voronoi neighbour of the origin's point), and the `7 × 7` block is more than needed.
-/

namespace JitteredVoronoi

/-- Squared Euclidean distance on `ℝ × ℝ`. -/
def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- `f` is a jitter: the site of cell `c` lies in `[c.1, c.1 + 1) × [c.2, c.2 + 1)`. -/
def IsJitter (f : ℤ × ℤ → ℝ × ℝ) : Prop :=
  ∀ c : ℤ × ℤ, (f c).1 ∈ Set.Ico (c.1 : ℝ) (c.1 + 1) ∧ (f c).2 ∈ Set.Ico (c.2 : ℝ) (c.2 + 1)

section Voronoi

variable {ι : Type*}

/-- The Voronoi cell of the site `f x` among all sites: the points at least as close to `f x` as
to every `f y`. -/
def voronoi (f : ι → ℝ × ℝ) (x : ι) : Set (ℝ × ℝ) :=
  {p | ∀ y, sqDist p (f x) ≤ sqDist p (f y)}

/-- The Voronoi cell of `f x` computed from the sites in `N` only. -/
def voronoiOn (f : ι → ℝ × ℝ) (N : Set ι) (x : ι) : Set (ℝ × ℝ) :=
  {p | ∀ y ∈ N, sqDist p (f x) ≤ sqDist p (f y)}

theorem voronoiOn_univ (f : ι → ℝ × ℝ) (x : ι) : voronoiOn f Set.univ x = voronoi f x := by
  ext p
  simp [voronoiOn, voronoi]

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
  fun _ hp y _ => hp y

end Voronoi

/-! ### Sufficiency -/

/-- **Sufficiency.**  For every jitter, the Voronoi cell of the origin's point is determined by
the sites in `Nbhd`. -/
theorem voronoi_eq_voronoiOn_Nbhd {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) :
    voronoi f (0, 0) = voronoiOn f Nbhd (0, 0) := by
  apply Set.Subset.antisymm (voronoi_subset_voronoiOn f Nbhd (0, 0))
  intro p hp c
  by_contra hlt
  rw [not_le] at hlt
  by_cases hc : c ∈ Nbhd
  · exact absurd (hp c hc) (not_le.2 hlt)
  · have hx0 : (f (0, 0)).1 ∈ CellStructure.ico.I 0 := (hf (0, 0)).1
    have hy0 : (f (0, 0)).2 ∈ CellStructure.ico.I 0 := (hf (0, 0)).2
    obtain ⟨a', b', hN, -, hB⟩ :=
      hasBlocker_of_threat (Cx := CellStructure.ico) (Cy := CellStructure.ico) (u := p.1) (v := p.2)
        hx0 hy0 (a := c.1) (b := c.2) hc (hf c).1 (hf c).2 hlt
    have h1 := hp (a', b') hN
    have h2 := hB (f (a', b')).1 (hf (a', b')).1 (f (a', b')).2 (hf (a', b')).2
    unfold sqDist at h1
    linarith

/-- Any neighbourhood containing the 36 cells works. -/
theorem voronoiOn_eq_voronoi_of_subset {N : Set (ℤ × ℤ)} (hN : Nbhd \ {(0, 0)} ⊆ N)
    {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) : voronoiOn f N (0, 0) = voronoi f (0, 0) := by
  apply Set.Subset.antisymm _ (voronoi_subset_voronoiOn f N (0, 0))
  intro p hp
  rw [voronoi_eq_voronoiOn_Nbhd hf]
  intro c hc
  by_cases h0 : c = (0, 0)
  · subst h0; exact le_refl _
  · exact hp c (hN ⟨hc, h0⟩)

/-! ### Necessity -/

namespace Witness

theorem wit_isJitter {c : ℤ × ℤ} (hc : c ∈ nbhdList) : IsJitter (wit c) := by
  intro d
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩, -⟩ := data_check c hc
  unfold wit
  split_ifs with hd hd'
  · subst hd
    simp only [Set.mem_Ico]
    push_cast
    exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩⟩
  · subst hd'
    simp only [Set.mem_Ico]
    exact ⟨⟨by exact_mod_cast h5, by exact_mod_cast h6⟩, ⟨by exact_mod_cast h7, by exact_mod_cast h8⟩⟩
  · simp only [Set.mem_Ico]
    have hx := far_mem (pt c).1 d.1
    have hy := far_mem (pt c).2 d.2
    exact ⟨⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩, ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩⟩

theorem sqDist_ptR (c : ℤ × ℤ) (s : ℚ × ℚ) :
    sqDist (ptR c) (((s.1 : ℚ) : ℝ), ((s.2 : ℚ) : ℝ)) = ((sqQ (pt c) s : ℚ) : ℝ) := by
  simp only [sqDist, sqQ, ptR]
  push_cast
  ring

/-- The test point lies in the local Voronoi cell computed without `c`. -/
theorem ptR_mem {c : ℤ × ℤ} (hc : c ∈ nbhdList) :
    ptR c ∈ voronoiOn (wit c) {c}ᶜ (0, 0) := by
  intro d hd
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hd
  obtain ⟨-, -, -, ⟨hu1, hu2, hv1, hv2⟩, hr⟩ := data_check c hc
  have e0 : wit c (0, 0) = (((p0 c).1 : ℝ), ((p0 c).2 : ℝ)) := by simp [wit]
  rw [e0]
  by_cases hd0 : d = (0, 0)
  · subst hd0; rw [e0]
  have ed : wit c d = ((far (pt c).1 d.1 : ℝ), (far (pt c).2 d.2 : ℝ)) := by
    rw [wit, if_neg hd0, if_neg hd]
  rw [ed, sqDist_ptR c (p0 c), sqDist_ptR c (far (pt c).1 d.1, far (pt c).2 d.2)]
  rw [Rat.cast_le]
  by_cases hwin : d.1.natAbs ≤ 5 ∧ d.2.natAbs ≤ 5
  · obtain ⟨a, b⟩ := d
    exact far_check c hc a (mem_window (by omega) (by omega)) b (mem_window (by omega) (by omega)) hd0 hd
  · have h6 : 6 ≤ d.1.natAbs ∨ 6 ≤ d.2.natAbs := by omega
    simp only [sqQ] at hr ⊢
    rcases h6 with h6 | h6
    · have := far_big (pt c).1 hu1 hu2 d.1 h6
      nlinarith [mul_self_nonneg ((pt c).2 - far (pt c).2 d.2)]
    · have := far_big (pt c).2 hv1 hv2 d.2 h6
      nlinarith [mul_self_nonneg ((pt c).1 - far (pt c).1 d.1)]

/-- The test point is not in the true Voronoi cell: the site in `c` is strictly closer. -/
theorem ptR_not_mem {c : ℤ × ℤ} (hc : c ∈ nbhdList) (h0 : c ≠ (0, 0)) :
    ptR c ∉ voronoi (wit c) (0, 0) := by
  intro hp
  have h := hp c
  obtain ⟨-, -, hlt, -⟩ := data_check c hc
  have e0 : wit c (0, 0) = (((p0 c).1 : ℝ), ((p0 c).2 : ℝ)) := by simp [wit]
  have ec : wit c c = (((q c).1 : ℝ), ((q c).2 : ℝ)) := by rw [wit, if_neg h0, if_pos rfl]
  rw [e0, ec, sqDist_ptR, sqDist_ptR, Rat.cast_le] at h
  exact absurd hlt (not_lt.2 h)

end Witness

/-- **Necessity.**  Every non-origin cell of `Nbhd` is needed: dropping it changes the Voronoi
cell of the origin's point for some jitter. -/
theorem exists_jitter_voronoiOn_ne {c : ℤ × ℤ} (hc : c ∈ Nbhd) (h0 : c ≠ (0, 0)) :
    ∃ f : ℤ × ℤ → ℝ × ℝ, IsJitter f ∧
      ∃ p, p ∈ voronoiOn f {c}ᶜ (0, 0) ∧ p ∉ voronoi f (0, 0) :=
  have hc' := Witness.mem_nbhdList hc h0
  ⟨Witness.wit c, Witness.wit_isJitter hc', Witness.ptR c, Witness.ptR_mem hc',
    Witness.ptR_not_mem hc' h0⟩

/-! ### The characterisation -/

/-- **Main theorem.**  Computing the Voronoi cell of the origin's point from the sites in `N`
is exact for every jitter if and only if `N` contains every non-origin cell of `Nbhd`. -/
theorem voronoiOn_eq_voronoi_iff (N : Set (ℤ × ℤ)) :
    (∀ f : ℤ × ℤ → ℝ × ℝ, IsJitter f → voronoiOn f N (0, 0) = voronoi f (0, 0)) ↔
      Nbhd \ {(0, 0)} ⊆ N := by
  constructor
  · intro h c ⟨hc, h0⟩
    simp only [Set.mem_singleton_iff] at h0
    by_contra hcN
    obtain ⟨f, hf, p, hp1, hp2⟩ := exists_jitter_voronoiOn_ne hc h0
    apply hp2
    rw [← h f hf]
    exact voronoiOn_anti f (fun d hd => (show d ≠ c from fun e => hcN (e ▸ hd))) (0, 0) hp1
  · intro hN f hf
    exact voronoiOn_eq_voronoi_of_subset hN hf

/-- The same statement for the restricted family `f ∘ Subtype.val : N → ℝ × ℝ`, as in the
question "when is `Voronoi f origin = Voronoi (f.restrict N) origin`?". -/
theorem voronoi_restrict_eq_iff (N : Set (ℤ × ℤ)) (h0 : (0, 0) ∈ N) :
    (∀ f : ℤ × ℤ → ℝ × ℝ, IsJitter f →
        voronoi (fun y : N => f y) ⟨(0, 0), h0⟩ = voronoi f (0, 0)) ↔ Nbhd ⊆ N := by
  have key : Nbhd \ {(0, 0)} ⊆ N ↔ Nbhd ⊆ N := by
    constructor
    · intro h c hc
      by_cases hc0 : c = (0, 0)
      · subst hc0; exact h0
      · exact h ⟨hc, hc0⟩
    · intro h c hc
      exact h hc.1
  rw [← key, ← voronoiOn_eq_voronoi_iff]
  simp only [voronoi_restrict]

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
  simp only [voronoiDist, voronoi, Set.mem_ofPred_eq, dist_toE]
  exact forall_congr' fun y => Real.sqrt_le_sqrt_iff (sqDist_nonneg _ _)

/-! ### Concrete consequences -/

/-- The neighbourhood has 37 cells (36 without the origin). -/
theorem card_nbhdList : Witness.nbhdList.length = 36 := by decide

/-- The `5 × 5` block is not enough: the cell `(3, 0)` is needed. -/
theorem three_zero_needed :
    ∃ f : ℤ × ℤ → ℝ × ℝ, IsJitter f ∧
      ∃ p, p ∈ voronoiOn f {(3, 0)}ᶜ (0, 0) ∧ p ∉ voronoi f (0, 0) :=
  exists_jitter_voronoiOn_ne (mem_Nbhd_of (by decide) (by decide) (by decide)) (by decide)

/-- The `7 × 7` block is more than needed: the cell `(3, 2)` never matters. -/
theorem three_two_not_needed {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) :
    voronoiOn f {(3, 2)}ᶜ (0, 0) = voronoi f (0, 0) :=
  voronoiOn_eq_voronoi_of_subset (fun c ⟨hc, _⟩ => by
    have h : c.1.natAbs ≤ 3 ∧ c.2.natAbs ≤ 3 ∧ c.1.natAbs + c.2.natAbs ≤ 4 := hc
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp at h) hf

end JitteredVoronoi
