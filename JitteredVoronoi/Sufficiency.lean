import JitteredVoronoi.Blocking
import JitteredVoronoi.Mirror

/-!
# Sufficiency: the neighbourhood determines the origin's Voronoi cell

For every jitter, the Voronoi cell of the origin's site computed from the sites in `Nbhd` is
the true Voronoi cell (`voronoi_eq_voronoiOn_Nbhd`).  The proof uses the symmetries of the
square (`Mirror.lean`) to place the test point in the octant `1/2 ≤ v ≤ u`, then the
octant lemmas of `Blocking.lean`.
-/

namespace JitteredVoronoi

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

/--
  If voronoi_eq_voronoiOn_Nbhd was false, then there must be a set of values as follow:
  * jitter f
  * test point p aka (u, v), wlog in the octant 1/2 ≤ v ≤ u
  * cell c aka (a,b) outside Nbhd
  Such that:
  * p ∈ voronoiOn f Nbhd (0, 0)
  * sqDist p (f c) < sqDist p (f (0, 0))

  (i.e. if we added f c to the voronoi diagram, then p would no longer be in the (0, 0) Voronoi cell)

  This theorem shows that this is impossible.

  threat_cases proves that (a, b) can only be (3, 2) or (2, 3)

  Then block_three_two eliminates these last two cases.
 -/
theorem contra_voronoi_eq_voronoiOn_Nbhd {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) {p : ℝ × ℝ}
    (hp : p ∈ voronoiOn f Nbhd (0, 0)) (hu : 1 / 2 ≤ p.1) (hv : 1 / 2 ≤ p.2) (huv : p.2 ≤ p.1)
    {c : ℤ × ℤ} (hc : c ∉ Nbhd) (hlt : sqDist p (f c) < sqDist p (f (0, 0))) : False := by
  have hx0 : 0 ≤ (f (0, 0)).1 ∧ (f (0, 0)).1 ≤ 1 := by simpa using (hf.mem (0, 0)).1
  have hy0 : 0 ≤ (f (0, 0)).2 ∧ (f (0, 0)).2 ≤ 1 := by simpa using (hf.mem (0, 0)).2
  -- radius bound: far test points are blocked, the others have their own square in `Nbhd`
  have hr : sqDist p (f (0, 0)) ≤ 2 := by
    rcases le_or_gt (5 / 2) p.1 with hu5 | hu5
    · exact absurd hp (HasBlocker.not_mem_voronoiOn hf (far_right hx0 hy0 hu5 hv))
    · exact le_trans (hp.2 _ (floor_mem_Nbhd (by linarith) (by linarith) (by linarith) (by linarith)))
        (sqDist_floor_le_two hf p)
  have hu2 : p.1 ≤ 5 / 2 := by unfold sqDist at hr; nlinarith [sq_nonneg (p.2 - (f (0, 0)).2)]
  have hv2 : p.2 ≤ 5 / 2 := by linarith
  obtain ⟨a, b⟩ := c
  obtain ⟨hqx, hqy⟩ := hf.mem (a, b)
  unfold sqDist at hlt hr
  rcases threat_cases hx0 hy0 hu hv hr hc hqx hqy hlt with h32 | h23
  · -- the cell `(3, 2)`
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h32
    norm_num at hqx hqy
    exact HasBlocker.not_mem_voronoiOn hf (block_three_two hx0 hy0 hu2 hv2 ⟨hqx, hqy⟩ hlt) hp
  · -- the cell `(2, 3)`: the same with the axes swapped
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h23
    norm_num at hqx hqy
    refine HasBlocker.not_mem_voronoiOn hf.swapXY ?_ (mem_voronoiOn_swapXY Nbhd_swap hp)
    show HasBlocker p.2 p.1 (f (0, 0)).2 (f (0, 0)).1
    exact block_three_two hy0 hx0 hv2 hu2 ⟨hqy, hqx⟩ (by linarith)

/-- **Sufficiency.**  For every jitter, the Voronoi cell of the origin's point is determined by
the sites in `Nbhd`.
 -/
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
  /-
    At this point, we've unpacked the defitions to show if the theorem was false, then there must be a set of values as follow:
    * jitter f
    * test point p aka (u, v), wlog 1/2 ≤ v ≤ u
    * cell c aka (a,b) outside Nbhd
    Such that:
    * p ∈ voronoiOn f Nbhd (0, 0)
    * sqDist p (f c) < sqDist p (f (0, 0)) -/
  exact le_of_not_gt fun hlt => contra_voronoi_eq_voronoiOn_Nbhd hf hp hu hv huv hc hlt

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

end JitteredVoronoi
