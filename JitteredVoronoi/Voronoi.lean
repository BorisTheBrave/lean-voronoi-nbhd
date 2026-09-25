import JitteredVoronoi.Basic
import JitteredVoronoi.Blocking
import JitteredVoronoi.Witness

/-!
# Jittered Voronoi diagrams: which neighbourhood determines the origin's cell?

A *jitter* `f : ℤ × ℤ → ℝ × ℝ` puts one point in every unit cell `[a, a+1) × [b, b+1)`.  The
Voronoi cell of the site `f x` is the set of points of the plane at least as close to `f x` as
to every other site.  Computing it from a neighbourhood `N` of cells only (ignoring the sites
outside `N`) gives a possibly larger set `voronoiOn f N x`.

**Main theorem** (`sufficientNbhd_iff`, `nbhd_isLeast`): the local computation is exact for the origin
cell and *every* jitter if and only if `N` contains the 36 cells
`{(a, b) ≠ (0, 0) | |a| ≤ 3, |b| ≤ 3, |a| + |b| ≤ 4}` — the `7 × 7` block minus the three cells
at each corner.  In particular the `5 × 5` block is not enough (the cell `(3, 0)` can be a
Voronoi neighbour of the origin's point), and the `7 × 7` block is more than needed.
-/

namespace JitteredVoronoi

/-! ### Sufficiency -/

/-- **Sufficiency.**  For every jitter, the Voronoi cell of the origin's point is determined by
the sites in `Nbhd`. -/
theorem voronoi_eq_voronoiOn_Nbhd {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) :
    voronoi f (0, 0) = voronoiOn f Nbhd (0, 0) := by
  apply Set.Subset.antisymm (voronoi_subset_voronoiOn f origin_mem_Nbhd)
  intro p hp
  refine ⟨Set.mem_univ _, fun c _ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  by_cases hc : c ∈ Nbhd
  · exact absurd (hp.2 c hc) (not_le.2 hlt)
  · have hx0 : (f (0, 0)).1 ∈ CellStructure.ico.I 0 := (hf (0, 0)).1
    have hy0 : (f (0, 0)).2 ∈ CellStructure.ico.I 0 := (hf (0, 0)).2
    obtain ⟨a', b', hN, -, hB⟩ :=
      hasBlocker_of_threat (Cx := CellStructure.ico) (Cy := CellStructure.ico) (u := p.1) (v := p.2)
        hx0 hy0 (a := c.1) (b := c.2) hc (hf c).1 (hf c).2 hlt
    have h1 := hp.2 (a', b') hN
    have h2 := hB (f (a', b')).1 (hf (a', b')).1 (f (a', b')).2 (hf (a', b')).2
    unfold sqDist at h1
    linarith

/-- Any neighbourhood containing `Nbhd` works. -/
theorem voronoiOn_eq_voronoi_of_subset {N : Set (ℤ × ℤ)} (hN : Nbhd ⊆ N)
    {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) : voronoiOn f N (0, 0) = voronoi f (0, 0) :=
  Set.Subset.antisymm ((voronoi_eq_voronoiOn_Nbhd hf).symm ▸ voronoiOn_anti f hN origin_mem_Nbhd)
    (voronoi_subset_voronoiOn f (hN origin_mem_Nbhd))

/-! ### Necessity -/

namespace Witness


private theorem sqDist_testR (c : ℤ × ℤ) (s : ℚ × ℚ) :
    sqDist (testR c) (((s.1 : ℚ) : ℝ), ((s.2 : ℚ) : ℝ)) = ((sqQ (data c).test s : ℚ) : ℝ) := by
  simp only [sqQ_eq_sqDist]

/-- The test point lies in the local Voronoi cell computed without `c`. -/
theorem testR_mem {c : ℤ × ℤ} (hc : c ∈ nbhdList) (h0 : c ≠ (0, 0)) :
    testR c ∈ voronoiOn (wit c) {c}ᶜ (0, 0) := by
  refine ⟨Set.mem_compl_singleton_iff.2 h0.symm, fun d hd => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hd
  obtain ⟨-, -, -, ⟨hu1, hu2, hv1, hv2⟩, hr⟩ := data_check c hc
  have e0 : wit c (0, 0) = (data c).originR := by simp [wit]
  rw [e0]
  by_cases hd0 : d = (0, 0)
  · subst hd0; rw [e0]
  have ed : wit c d = ((far (data c).test.1 d.1 : ℝ), (far (data c).test.2 d.2 : ℝ)) := by
    rw [wit, if_neg hd0, if_neg hd]
  rw [ed, sqDist_testR c (data c).origin, sqDist_testR c (far (data c).test.1 d.1, far (data c).test.2 d.2)]
  rw [Rat.cast_le]
  by_cases hwin : d.1.natAbs ≤ 5 ∧ d.2.natAbs ≤ 5
  · obtain ⟨a, b⟩ := d
    exact far_check c hc a (mem_window (by omega) (by omega)) b (mem_window (by omega) (by omega)) hd0 hd
  · have h6 : 6 ≤ d.1.natAbs ∨ 6 ≤ d.2.natAbs := by omega
    simp only [sqQ] at hr ⊢
    rcases h6 with h6 | h6
    · have := far_big (data c).test.1 hu1 hu2 d.1 h6
      nlinarith [mul_self_nonneg ((data c).test.2 - far (data c).test.2 d.2)]
    · have := far_big (data c).test.2 hv1 hv2 d.2 h6
      nlinarith [mul_self_nonneg ((data c).test.1 - far (data c).test.1 d.1)]

/-- The test point is not in the true Voronoi cell: the site in `c` is strictly closer. -/
theorem testR_not_mem {c : ℤ × ℤ} (hc : c ∈ nbhdList) (h0 : c ≠ (0, 0)) :
    testR c ∉ voronoi (wit c) (0, 0) := by
  intro hp
  have h := hp.2 c (Set.mem_univ c)
  obtain ⟨-, -, hlt, -⟩ := data_check c hc
  have e0 : wit c (0, 0) = (data c).originR := by simp [wit]
  have ec : wit c c = (data c).siteR := by rw [wit, if_neg h0, if_pos rfl]
  rw [e0, ec, sqDist_testR, sqDist_testR, Rat.cast_le] at h
  exact absurd hlt (not_lt.2 h)

end Witness

/-- **Necessity.**  Every non-origin cell of `Nbhd` is needed: dropping it changes the Voronoi
cell of the origin's point for some jitter. -/
theorem exists_jitter_voronoiOn_ne {c : ℤ × ℤ} (hc : c ∈ Nbhd) (h0 : c ≠ (0, 0)) :
    ∃ f : ℤ × ℤ → ℝ × ℝ, IsJitter f ∧
      ∃ p, p ∈ voronoiOn f {c}ᶜ (0, 0) ∧ p ∉ voronoi f (0, 0) :=
  have hc' := mem_nbhdList hc h0
  ⟨Witness.wit c, Witness.wit_isJitter hc', Witness.testR c, Witness.testR_mem hc' h0,
    Witness.testR_not_mem hc' h0⟩

/-! ### The characterisation -/

/-- `N` is a sufficient neighbourhood
 if computing voronoi on N gives the same result for the origin's cell as computing voronoi on the full plane-/
def SufficientNbhd (N : Set (ℤ × ℤ)) : Prop :=
  ∀ f : ℤ × ℤ → ℝ × ℝ, IsJitter f → voronoiOn f N (0, 0) = voronoi f (0, 0)

/-- A sufficient neighbourhood contains the origin cell: otherwise the local Voronoi cell is
empty while the true one contains the origin's site. -/
theorem origin_mem_of_sufficientNbhd {N : Set (ℤ × ℤ)} (h : SufficientNbhd N) : (0, 0) ∈ N := by
  by_contra h0
  -- any jitter will do, e.g. the one placing every site at the corner of its cell
  have hf : IsJitter fun c : ℤ × ℤ => ((c.1 : ℝ), (c.2 : ℝ)) := fun c =>
    ⟨⟨le_refl _, by linarith⟩, ⟨le_refl _, by linarith⟩⟩
  have := voronoi_nonempty (fun c : ℤ × ℤ => ((c.1 : ℝ), (c.2 : ℝ))) (0, 0)
  rw [← h _ hf, voronoiOn_eq_empty _ h0] at this
  exact Set.not_nonempty_empty this

/-- `N` is a sufficient neighbourhood if and only if it contains `Nbhd`. -/
theorem sufficientNbhd_iff (N : Set (ℤ × ℤ)) : SufficientNbhd N ↔ Nbhd ⊆ N := by
  constructor
  · intro h c hc
    have h0N := origin_mem_of_sufficientNbhd h
    by_cases h0 : c = (0, 0)
    · exact h0 ▸ h0N
    by_contra hcN
    obtain ⟨f, hf, p, hp1, hp2⟩ := exists_jitter_voronoiOn_ne hc h0
    apply hp2
    rw [← h f hf]
    exact voronoiOn_anti f (fun d hd => (show d ≠ c from fun e => hcN (e ▸ hd))) h0N hp1
  · intro hN f hf
    exact voronoiOn_eq_voronoi_of_subset hN hf

/-- *Main Theorem*
`Nbhd` is the least sufficient neighbourhood.
-/
theorem nbhd_isLeast : IsLeast {N | SufficientNbhd N} Nbhd :=
  ⟨(sufficientNbhd_iff Nbhd).2 le_rfl, fun _ hN => (sufficientNbhd_iff _).1 hN⟩


/-! ### Concrete consequences -/

/-- The `5 × 5` block is not enough: the cell `(3, 0)` is needed. -/
theorem three_zero_needed :
    ∃ f : ℤ × ℤ → ℝ × ℝ, IsJitter f ∧
      ∃ p, p ∈ voronoiOn f {(3, 0)}ᶜ (0, 0) ∧ p ∉ voronoi f (0, 0) :=
  exists_jitter_voronoiOn_ne (mem_Nbhd_of (by decide) (by decide) (by decide)) (by decide)

/-- The `7 × 7` block is more than needed: the cell `(3, 2)` never matters. -/
theorem three_two_not_needed {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) :
    voronoiOn f {(3, 2)}ᶜ (0, 0) = voronoi f (0, 0) :=
  voronoiOn_eq_voronoi_of_subset (fun c hc => by
    have h : c.1.natAbs ≤ 3 ∧ c.2.natAbs ≤ 3 ∧ c.1.natAbs + c.2.natAbs ≤ 4 := hc
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp at h) hf

end JitteredVoronoi
