import JitteredVoronoi.Basic
import JitteredVoronoi.Nbhd

/-!
# Blocking: cells outside the neighbourhood never cut the origin's Voronoi cell

Fix the origin's point `(x0, y0)` (in the closed cell `[0, 1]²`) and a test point `p = (u, v)`.
A cell `(a, b)` *threatens* `p` if it contains a point strictly closer to `p` than `(x0, y0)`
is.


A cell `(a', b')` *blocks* `p` if *every* point of it other than `(x0, y0)` itself is
strictly closer to `p` than `(x0, y0)`.
In other words, if you draw a circle around `p` with (x0, y0) on the edge, then the cell `(a', b')`
is completely inside the circle.

We use this notion of blocking to eliminate possibile threats - if there is a blocking cell `(a', b')`
in Nbhd, then the site `f (a', b')` is strictly closer to `p` than `f (0, 0)`, so p cannot be in `voronoiOn f Nbhd (0, 0)`,
an assumption of contra_voronoi_eq_voronoiOn_Nbhd.

Using wlogs in Sufficiency, we can assume the test point lies in the quadrant `u, v ≥ 1/2` and the threatening cell `(a, b)` to satisfy `b ≤ a`.

There are three main theorems:

* `far_right`: if `u ≥ 5/2` the cell `(2, b')` in the row of `v` blocks.
   This is used in contra_voronoi_eq_voronoiOn_Nbhd to establish a radius bound on p.
* `threat_cases`: given that radius bound, eliminate all possible threats except for `(3, 2)`.
* `block_three_two`: a threat from the cell `(3, 2)` is blocked by `(2, 1)`, `(1, 1)` or
  `(1, 2)`, depending on where the test point is.

Each case is settled by choosing the blocking cell explicitly, bounding the squared distances
corner by corner, and finishing with linear arithmetic.
-/

namespace JitteredVoronoi

/-- Every point of the closed cell `(a', b')` other than `(x0, y0)` is strictly closer to
`(u, v)` than `(x0, y0)` is. -/
def Blocked (u v x0 y0 : ℝ) (a' b' : ℤ) : Prop :=
  ∀ x ∈ Set.Icc (a' : ℝ) (a' + 1), ∀ y ∈ Set.Icc (b' : ℝ) (b' + 1), (x, y) ≠ (x0, y0) →
    (u - x) ^ 2 + (v - y) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2

/-- Some non-origin cell of `Nbhd` blocks `(u, v)`. -/
def HasBlocker (u v x0 y0 : ℝ) : Prop :=
  ∃ a' b' : ℤ, (a', b') ∈ Nbhd ∧ (a', b') ≠ (0, 0) ∧ Blocked u v x0 y0 a' b'

variable {u v x0 y0 qx qy : ℝ}

theorem HasBlocker.mk (a' b' : ℤ) (h : Blocked u v x0 y0 a' b')
    (hN : a'.natAbs ≤ 3 ∧ b'.natAbs ≤ 3 ∧ a'.natAbs + b'.natAbs ≤ 4 := by decide)
    (h0 : (a', b') ≠ (0, 0) := by decide) : HasBlocker u v x0 y0 :=
  ⟨a', b', hN, h0, h⟩

/-- A test point with a blocker is not in the local Voronoi cell: the blocking cell's site is
strictly closer than the origin's site (it differs from the origin's site because sites are
distinct). -/
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

/-! ### Far centres: `u ≥ 5/2` -/

/-- If the test point is far to the right, the column `x ∈ [2, 3]` blocks it whatever the
threat. -/
theorem far_right (hx0 : 0 ≤ x0 ∧ x0 ≤ 1) (hy0 : 0 ≤ y0 ∧ y0 ≤ 1) (hu : 5 / 2 ≤ u)
    (hv : 1 / 2 ≤ v) : HasBlocker u v x0 y0 := by
  obtain ⟨hx01, hx02⟩ := hx0
  obtain ⟨hy01, hy02⟩ := hy0
  -- strict slack in the `x` direction for every point of column `2`
  have hcol : ∀ x ∈ Set.Icc ((2 : ℤ) : ℝ) ((2 : ℤ) + 1), (u - x) ^ 2 + 1 < (u - x0) ^ 2 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    push_cast at h1 h2
    nlinarith [mul_nonneg (show 0 ≤ x - x0 - 1 by linarith) (show 0 ≤ 2 * u - x - x0 - 1 by linarith)]
  -- the row containing `v` blocks
  have row : ∀ b' : ℤ, (b' : ℝ) ≤ v → v ≤ b' + 1 → Blocked u v x0 y0 2 b' := by
    intro b' hv1 hv2 x hx y hy _
    obtain ⟨h1, h2⟩ := hy
    have h3 : (v - y) ^ 2 ≤ 1 := by nlinarith
    have := hcol x hx
    nlinarith [sq_nonneg (v - y0)]
  rcases le_or_gt 3 v with hv3 | hv3
  · refine HasBlocker.mk 2 2 ?_
    intro x hx y hy _
    obtain ⟨h1, h2⟩ := hy
    push_cast at h1 h2
    have := hcol x hx
    have h3 : (v - y) ^ 2 ≤ (v - 2) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h4 : (v - 2) ^ 2 ≤ (v - y0) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    linarith
  rcases le_or_gt 2 v with hv2 | hv2
  · exact HasBlocker.mk 2 2 (row 2 (by push_cast; linarith) (by push_cast; linarith))
  rcases le_or_gt 1 v with hv1 | hv1
  · exact HasBlocker.mk 2 1 (row 1 (by push_cast; linarith) (by push_cast; linarith))
  · exact HasBlocker.mk 2 0 (row 0 (by push_cast; linarith) (by push_cast; linarith))

/-! ### The cell `(3, 2)` -/

/-- A threat from the cell `(3, 2)`: a point of `[3, 4] × [2, 3]` strictly closer to `(u, v)`
than the origin's site.  The blocking cell is `(2, 1)`, `(1, 1)` or `(1, 2)` depending on where
`(u, v)` is. -/
theorem block_three_two (hx0 : 0 ≤ x0 ∧ x0 ≤ 1) (hy0 : 0 ≤ y0 ∧ y0 ≤ 1)
    (hu : u ≤ 5 / 2) (hv : v ≤ 5 / 2)
    (hq : qx ∈ Set.Icc (3 : ℝ) 4 ∧ qy ∈ Set.Icc (2 : ℝ) 3)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker u v x0 y0 := by
  obtain ⟨⟨hqx, -⟩, ⟨hqy, -⟩⟩ := hq
  have hQx : (3 - u) ^ 2 ≤ (u - qx) ^ 2 := by nlinarith
  rcases le_or_gt v (3 / 2) with hv1 | hv1
  · -- the cell `(2, 1)` dominates
    refine HasBlocker.mk 2 1 ?_
    intro x hx y hy _
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨h3, h4⟩ := hy
    push_cast at h1 h2 h3 h4
    have hX : (u - x) ^ 2 ≤ (3 - u) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hY : (v - y) ^ 2 ≤ (2 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hQy : (2 - v) ^ 2 ≤ (v - qy) ^ 2 := by nlinarith
    linarith
  rcases le_or_gt u (3 / 2) with hu1 | hu1
  · rcases le_or_gt v 2 with hv2 | hv2
    · -- the cell `(1, 1)` dominates
      refine HasBlocker.mk 1 1 ?_
      intro x hx y hy _
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      push_cast at h1 h2 h3 h4
      have hX : (u - x) ^ 2 ≤ (2 - u) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hY : (v - y) ^ 2 ≤ (v - 1) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hQy : (2 - v) ^ 2 ≤ (v - qy) ^ 2 := by nlinarith
      nlinarith
    · -- the cell `(1, 2)` dominates
      refine HasBlocker.mk 1 2 ?_
      intro x hx y hy _
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      push_cast at h1 h2 h3 h4
      have hX : (u - x) ^ 2 ≤ (2 - u) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hY : (v - y) ^ 2 ≤ (3 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hY1 : (3 - v) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (v - qy)]
  · -- `u > 3/2`, `v > 3/2`: every point of the cell `(1, 1)` other than the origin's site is
    -- closer than the origin's site, whatever the threat
    refine HasBlocker.mk 1 1 ?_
    intro x hx y hy hne
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨h3, h4⟩ := hy
    push_cast at h1 h2 h3 h4
    obtain ⟨hx01, hx02⟩ := hx0
    obtain ⟨hy01, hy02⟩ := hy0
    have hX : (u - x) ^ 2 ≤ (u - x0) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ x - x0 by linarith) (show 0 ≤ 2 * u - x - x0 by linarith)]
    have hY : (v - y) ^ 2 ≤ (v - y0) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ y - y0 by linarith) (show 0 ≤ 2 * v - y - y0 by linarith)]
    rcases lt_or_eq_of_le (show x0 ≤ x by linarith) with hlt | heq
    · have : (u - x) ^ 2 < (u - x0) ^ 2 := by
        nlinarith [mul_pos (sub_pos.2 hlt) (show 0 < 2 * u - x - x0 by linarith)]
      linarith
    rcases lt_or_eq_of_le (show y0 ≤ y by linarith) with hlt' | heq'
    · have : (v - y) ^ 2 < (v - y0) ^ 2 := by
        nlinarith [mul_pos (sub_pos.2 hlt') (show 0 < 2 * v - y - y0 by linarith)]
      linarith
    · exact absurd (by rw [heq, heq']) hne

/-! ### Which cells can threaten -/

/-- If the threat point is at least `k` cells away in the `x` direction, its squared distance to
the origin's site in that direction is at least `(k - 1)²`. -/
theorem sq_le_of_far {a : ℤ} (hqx : qx ∈ Set.Icc (a : ℝ) (a + 1)) (hx0 : 0 ≤ x0 ∧ x0 ≤ 1)
    {k : ℤ} (hk : 1 ≤ k) (h : k ≤ a ∨ a ≤ -k) : ((k : ℝ) - 1) ^ 2 ≤ (qx - x0) ^ 2 := by
  obtain ⟨h1, h2⟩ := hqx
  obtain ⟨h3, h4⟩ := hx0
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases h with h | h
  · have : (k : ℝ) ≤ a := by exact_mod_cast h
    exact sq_le_sq' (by linarith) (by linarith)
  · have : (a : ℝ) ≤ -k := by exact_mod_cast h
    have := sq_le_sq' (a := (k : ℝ) - 1) (b := x0 - qx) (by linarith) (by linarith)
    nlinarith

/-- **Only one cell can threaten.**  Suppose the test point lies in the quadrant
`u, v ≥ 1/2` and within squared distance `2` of the origin's site (as it does whenever it lies
in the local Voronoi cell, up to symmetry).  If a cell `(a, b)` with `b ≤ a` outside `Nbhd`
contains a point strictly closer to `(u, v)` than the origin's site, then that cell is `(3, 2)`.

A point within `√2` of `(u, v)`, which is within `√2` of the origin's site, is within `2√2` of
the unit square, and only the `7 × 7` block minus its corners comes that close; in the quadrant
`u, v ≥ 1/2` the negative rows and columns are too far as well. -/
theorem threat_cases (hx0 : 0 ≤ x0 ∧ x0 ≤ 1) (hy0 : 0 ≤ y0 ∧ y0 ≤ 1)
    (hu : 1 / 2 ≤ u) (hv : 1 / 2 ≤ v) (hr : (u - x0) ^ 2 + (v - y0) ^ 2 ≤ 2) {a b : ℤ}
    (hc : (a, b) ∉ Nbhd) (hab : b ≤ a)
    (hqx : qx ∈ Set.Icc (a : ℝ) (a + 1)) (hqy : qy ∈ Set.Icc (b : ℝ) (b + 1))
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    (a, b) = (3, 2) := by

  -- (a,b) is in the 7x7 block
  have hA : a.natAbs ≤ 3 := by
    by_contra h
    have := sq_le_of_far hqx hx0 (k := 4) (by norm_num) (by omega)
    norm_num at this
    nlinarith [sq_nonneg (qy - y0)]
  have hB : b.natAbs ≤ 3 := by
    by_contra h
    have := sq_le_of_far hqy hy0 (k := 4) (by norm_num) (by omega)
    norm_num at this
    nlinarith [sq_nonneg (qx - x0)]
  -- the threat point is within `2√2` of the origin's site
  -- which let's us eliminate (3,3)
  have h8 : (qx - x0) ^ 2 + (qy - y0) ^ 2 < 8 := by
    nlinarith [sq_nonneg (qx - u - (u - x0)), sq_nonneg (qy - v - (v - y0))]
  have hcorner : ¬ (a.natAbs = 3 ∧ b.natAbs = 3) := by
    rintro ⟨ha, hb⟩
    have := sq_le_of_far hqx hx0 (k := 3) (by norm_num) (by omega)
    have := sq_le_of_far hqy hy0 (k := 3) (by norm_num) (by omega)
    norm_num at *
    linarith
  -- We're in the top right quadrant, so can eliminate negative columns and rows
  have ha : -1 ≤ a := by
    by_contra h
    have : (a : ℝ) ≤ -2 := by exact_mod_cast (by omega : a ≤ -2)
    obtain ⟨-, hq2⟩ := hqx
    nlinarith [sq_nonneg (v - qy)]
  have hb : -1 ≤ b := by
    by_contra h
    have : (b : ℝ) ≤ -2 := by exact_mod_cast (by omega : b ≤ -2)
    obtain ⟨-, hq2⟩ := hqy
    nlinarith [sq_nonneg (u - qx)]
  -- Also, eliminate (a,b) in Nbhd, but assumption
  have hc' : ¬ (a.natAbs ≤ 3 ∧ b.natAbs ≤ 3 ∧ a.natAbs + b.natAbs ≤ 4) := hc
  have : a = 3 ∧ b = 2 := by omega
  obtain ⟨rfl, rfl⟩ := this
  rfl

end JitteredVoronoi
