import JitteredVoronoi.Basic
import JitteredVoronoi.Blocking
import JitteredVoronoi.Mirror
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

/-- A test point with a blocker is not in the local Voronoi cell: the blocking cell's site is
strictly closer than the origin's site. -/
theorem HasBlocker.not_mem_voronoiOn {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) {p : ℝ × ℝ}
    (h : HasBlocker p.1 p.2 (f (0, 0)).1 (f (0, 0)).2) : p ∉ voronoiOn f Nbhd (0, 0) := by
  intro hp
  obtain ⟨a', b', hN, h0, hB⟩ := h
  have h1 := hp.2 (a', b') hN
  have hne : f (a', b') ≠ f (0, 0) := fun e => h0 (hf.injective e)
  have h2 := hB (f (a', b')).1 (hf.mem (a', b')).1 (f (a', b')).2 (hf.mem (a', b')).2
    fun e => hne (Prod.ext (congrArg Prod.fst e) (congrArg Prod.snd e))
  unfold sqDist at h1
  linarith

/-- The site of the square containing `p` is within distance `√2` of `p`. -/
theorem sqDist_floor_le_two {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) (p : ℝ × ℝ) :
    sqDist p (f (⌊p.1⌋, ⌊p.2⌋)) ≤ 2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hf.mem (⌊p.1⌋, ⌊p.2⌋)
  have f1 := Int.floor_le p.1
  have f2 := Int.lt_floor_add_one p.1
  have f3 := Int.floor_le p.2
  have f4 := Int.lt_floor_add_one p.2
  simp only at h1 h2 h3 h4
  have e1 : (p.1 - (f (⌊p.1⌋, ⌊p.2⌋)).1) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - (p.1 - (f (⌊p.1⌋, ⌊p.2⌋)).1) by linarith)
      (show 0 ≤ 1 + (p.1 - (f (⌊p.1⌋, ⌊p.2⌋)).1) by linarith)]
  have e2 : (p.2 - (f (⌊p.1⌋, ⌊p.2⌋)).2) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - (p.2 - (f (⌊p.1⌋, ⌊p.2⌋)).2) by linarith)
      (show 0 ≤ 1 + (p.2 - (f (⌊p.1⌋, ⌊p.2⌋)).2) by linarith)]
  unfold sqDist
  linarith

/-- **Sufficiency.**  For every jitter, the Voronoi cell of the origin's point is determined by
the sites in `Nbhd`.

By the symmetries of the square (`Mirror.lean`) the test point may be assumed to lie in the
octant `1/2 ≤ v ≤ u`.  Far test points (`u ≥ 5/2`) are excluded by `far_right`; otherwise the
square containing the test point is in `Nbhd`, so the test point is within `√2` of the origin's
site, and by `threat_cases` only the cells `(3, 2)` and `(2, 3)` could contradict membership,
which `block_three_two` rules out. -/
theorem voronoi_eq_voronoiOn_Nbhd {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) :
    voronoi f (0, 0) = voronoiOn f Nbhd (0, 0) := by
  apply Set.Subset.antisymm (voronoi_subset_voronoiOn f origin_mem_Nbhd)
  intro p hp
  refine ⟨Set.mem_univ _, ?_⟩
  intro c hcu
  clear hcu
  -- without loss of generality the test point lies in the octant `1/2 ≤ v ≤ u`
  wlog hu : 1 / 2 ≤ p.1 generalizing f p c
  · have := this (f := mirrorX f) (p := mx p) (c := (-c.1, c.2)) hf.mirrorX
      (mem_voronoiOn_mirrorX Nbhd_mirrorX hp) (by simp [m]; linarith)
    simpa [mirrorX] using this
  wlog hv : 1 / 2 ≤ p.2 generalizing f p c
  · have := this (f := mirrorY f) (p := my p) (c := (c.1, -c.2)) hf.mirrorY
      (mem_voronoiOn_mirrorY Nbhd_swap Nbhd_mirrorX hp) (by simpa using hu) (by simp [m]; linarith)
    simpa [mirrorY_apply] using this
  wlog huv : p.2 ≤ p.1 generalizing f p c
  · have := this (f := swapXY f) (p := p.swap) (c := c.swap) hf.swapXY
      (mem_voronoiOn_swapXY Nbhd_swap hp) (by simpa using hv) (by simpa using hu)
      (by simp; linarith)
    simpa [swapXY] using this
  by_cases hc : c ∈ Nbhd
  · exact hp.2 c hc
  by_contra hlt
  rw [not_le] at hlt
  have hx0 : 0 ≤ (f (0, 0)).1 ∧ (f (0, 0)).1 ≤ 1 := by simpa using (hf.mem (0, 0)).1
  have hy0 : 0 ≤ (f (0, 0)).2 ∧ (f (0, 0)).2 ≤ 1 := by simpa using (hf.mem (0, 0)).2
  -- radius bound: far test points are blocked, the others have their own square in `Nbhd`
  have hr : sqDist p (f (0, 0)) ≤ 2 := by
    rcases le_or_gt (5 / 2) p.1 with hu5 | hu5
    · exact absurd hp (HasBlocker.not_mem_voronoiOn hf (far_right hx0 hy0 hu5 hv))
    have f1 := Int.floor_le p.1
    have f2 := Int.lt_floor_add_one p.1
    have f3 := Int.floor_le p.2
    have f4 := Int.lt_floor_add_one p.2
    have hdN : (⌊p.1⌋, ⌊p.2⌋) ∈ Nbhd := by
      have a1 : -1 < ⌊p.1⌋ := by exact_mod_cast (show (-1 : ℝ) < ⌊p.1⌋ by linarith)
      have a2 : ⌊p.1⌋ < 3 := by exact_mod_cast (show (⌊p.1⌋ : ℝ) < 3 by linarith)
      have b1 : -1 < ⌊p.2⌋ := by exact_mod_cast (show (-1 : ℝ) < ⌊p.2⌋ by linarith)
      have b2 : ⌊p.2⌋ < 3 := by exact_mod_cast (show (⌊p.2⌋ : ℝ) < 3 by linarith)
      exact mem_Nbhd_of (by omega) (by omega) (by omega)
    exact le_trans (hp.2 _ hdN) (sqDist_floor_le_two hf p)
  have hu2 : p.1 ≤ 5 / 2 := by unfold sqDist at hr; nlinarith [sq_nonneg (p.2 - (f (0, 0)).2)]
  have hv2 : p.2 ≤ 5 / 2 := by linarith
  obtain ⟨a, b⟩ := c
  obtain ⟨hqx, hqy⟩ := hf.mem (a, b)
  unfold sqDist at hlt hr
  rcases threat_cases hx0 hy0 hu hv hr hc hqx hqy hlt with h32 | h23
  · -- the cell `(3, 2)`
    simp only [Prod.mk.injEq] at h32
    obtain ⟨rfl, rfl⟩ := h32
    obtain ⟨hx1, hx2⟩ := hqx
    obtain ⟨hy1, hy2⟩ := hqy
    norm_num at hx1 hx2 hy1 hy2
    exact HasBlocker.not_mem_voronoiOn hf
      (block_three_two hx0 hy0 hu2 hv2 ⟨⟨hx1, by linarith⟩, ⟨hy1, by linarith⟩⟩ hlt) hp
  · -- the cell `(2, 3)`: the same with the axes swapped
    simp only [Prod.mk.injEq] at h23
    obtain ⟨rfl, rfl⟩ := h23
    obtain ⟨hx1, hx2⟩ := hqx
    obtain ⟨hy1, hy2⟩ := hqy
    norm_num at hx1 hx2 hy1 hy2
    refine HasBlocker.not_mem_voronoiOn hf.swapXY ?_ (mem_voronoiOn_swapXY Nbhd_swap hp)
    show HasBlocker p.2 p.1 (f (0, 0)).2 (f (0, 0)).1
    exact block_three_two hy0 hx0 hv2 hu2 ⟨⟨hy1, by linarith⟩, ⟨hx1, by linarith⟩⟩ (by linarith)

/-- **Radius bound.**  A point of the Voronoi cell of the origin's site computed from `Nbhd` is
within distance `√2` of that site. -/
theorem sqDist_le_two_of_mem_voronoiOn_Nbhd {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) {p : ℝ × ℝ}
    (hp : p ∈ voronoiOn f Nbhd (0, 0)) : sqDist p (f (0, 0)) ≤ 2 :=
  have hp' : p ∈ voronoi f (0, 0) := (voronoi_eq_voronoiOn_Nbhd hf).symm ▸ hp
  le_trans (hp'.2 _ (Set.mem_univ _)) (sqDist_floor_le_two hf p)

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
  have hf : IsJitter fun c : ℤ × ℤ => ((c.1 : ℝ), (c.2 : ℝ)) :=
    IsJitterIco.isJitter fun c => ⟨⟨le_refl _, by linarith⟩, ⟨le_refl _, by linarith⟩⟩
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
