import Mathlib
import JitteredVoronoi.Nbhd

/-!
# Blocking: cells outside the neighbourhood never cut the origin's Voronoi cell

Fix the origin's point `(x0, y0)` (in the closed cell `[0, 1]²`) and a test point `p = (u, v)`.
A cell `(a, b)` *threatens* `p` if it contains a point strictly closer to `p` than `(x0, y0)`
is; a cell `(a', b')` *blocks* `p` if *every* point of it other than `(x0, y0)` itself is
strictly closer to `p` than `(x0, y0)` is.  Cells are closed squares throughout; the exception
for the point `(x0, y0)` is what a jitter's distinct sites provide.

The main result of this file, `hasBlocker_of_threat`, says: if a cell outside `Nbhd` threatens
`p`, then some non-origin cell of `Nbhd` blocks `p`.  Consequently, for any jitter, `p` is not in
the Voronoi cell of the origin's point computed from `Nbhd` alone, so the cells outside `Nbhd`
are irrelevant.

Closed cells are symmetric under the reflections `x ↦ 1 - x`, `y ↦ 1 - y` and the swap
`x ↔ y`, which reduce everything to three frontier configurations:

* `far_right`: if `u ≥ 5/2` some cell `(2, b')` blocks — no threat is needed.  This is what
  bounds the local Voronoi cell (`sqDist_le_two_of_mem_voronoiOn_Nbhd`): a test point of the
  local cell is within `√2` of the origin's site.
* `block_three_two`: a threat from the cell `(3, 2)`.  Given the radius bound, only the eight
  cells `(±3, ±2)`, `(±2, ±3)` can threaten a test point, and the symmetries reduce them to
  this one cell.

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

/-- The reflection `x ↦ 1 - x` sends the cell `a` to the cell `-a`. -/
theorem mem_reflect {a : ℤ} {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (a + 1)) :
    1 - x ∈ Set.Icc ((-a : ℤ) : ℝ) ((-a : ℤ) + 1) := by
  obtain ⟨h1, h2⟩ := hx
  push_cast
  constructor <;> linarith

theorem reflect01 {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : 0 ≤ 1 - x ∧ 1 - x ≤ 1 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-! ### Symmetries -/

theorem sq_reflect (s t : ℝ) : ((1 - s) - (1 - t)) ^ 2 = (s - t) ^ 2 := by ring

theorem Blocked.of_reflectX {a' b' : ℤ} (h : Blocked (1 - u) v (1 - x0) y0 a' b') :
    Blocked u v x0 y0 (-a') b' := by
  intro x hx y hy hne
  have hx' := mem_reflect hx
  rw [neg_neg] at hx'
  have hne' : (1 - x, y) ≠ (1 - x0, y0) := by
    intro e
    apply hne
    simp only [Prod.mk.injEq] at e ⊢
    exact ⟨by linarith [e.1], e.2⟩
  have := h (1 - x) hx' y hy hne'
  simp only [sq_reflect] at this
  exact this

theorem Blocked.of_reflectY {a' b' : ℤ} (h : Blocked u (1 - v) x0 (1 - y0) a' b') :
    Blocked u v x0 y0 a' (-b') := by
  intro x hx y hy hne
  have hy' := mem_reflect hy
  rw [neg_neg] at hy'
  have hne' : (x, 1 - y) ≠ (x0, 1 - y0) := by
    intro e
    apply hne
    simp only [Prod.mk.injEq] at e ⊢
    exact ⟨e.1, by linarith [e.2]⟩
  have := h x hx (1 - y) hy' hne'
  simp only [sq_reflect] at this
  exact this

theorem Blocked.of_swap {a' b' : ℤ} (h : Blocked v u y0 x0 b' a') : Blocked u v x0 y0 a' b' := by
  intro x hx y hy hne
  have hne' : (y, x) ≠ (y0, x0) := by
    intro e
    apply hne
    simp only [Prod.mk.injEq] at e ⊢
    exact ⟨e.2, e.1⟩
  have := h y hy x hx hne'
  linarith

theorem HasBlocker.of_reflectX (h : HasBlocker (1 - u) v (1 - x0) y0) : HasBlocker u v x0 y0 := by
  obtain ⟨a', b', hN, h0, hB⟩ := h
  refine ⟨-a', b', mem_Nbhd_neg_fst.2 hN, ?_, hB.of_reflectX⟩
  intro e
  apply h0
  simp only [Prod.mk.injEq] at e ⊢
  omega

theorem HasBlocker.of_reflectY (h : HasBlocker u (1 - v) x0 (1 - y0)) : HasBlocker u v x0 y0 := by
  obtain ⟨a', b', hN, h0, hB⟩ := h
  refine ⟨a', -b', mem_Nbhd_neg_snd.2 hN, ?_, hB.of_reflectY⟩
  intro e
  apply h0
  simp only [Prod.mk.injEq] at e ⊢
  omega

theorem HasBlocker.of_swap (h : HasBlocker v u y0 x0) : HasBlocker u v x0 y0 := by
  obtain ⟨a', b', hN, h0, hB⟩ := h
  refine ⟨b', a', mem_Nbhd_swap.2 hN, ?_, hB.of_swap⟩
  intro e
  apply h0
  simp only [Prod.mk.injEq] at e ⊢
  exact ⟨e.2, e.1⟩

/-! ### Far centres: `u ≥ 5/2` -/

/-- If the test point is far to the right, the column `x ∈ [2, 3]` blocks it whatever the
threat. -/
theorem far_right (hx0 : 0 ≤ x0 ∧ x0 ≤ 1) (hy0 : 0 ≤ y0 ∧ y0 ≤ 1) (hu : 5 / 2 ≤ u) :
    HasBlocker u v x0 y0 := by
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
  rcases le_or_gt 3 v with hv | hv
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
  rcases le_or_gt 1 v with hv3 | hv3
  · exact HasBlocker.mk 2 1 (row 1 (by push_cast; linarith) (by push_cast; linarith))
  rcases le_or_gt 0 v with hv4 | hv4
  · exact HasBlocker.mk 2 0 (row 0 (by push_cast; linarith) (by push_cast; linarith))
  rcases le_or_gt (-1) v with hv5 | hv5
  · exact HasBlocker.mk 2 (-1) (row (-1) (by push_cast; linarith) (by push_cast; linarith))
  rcases le_or_gt (-2) v with hv6 | hv6
  · exact HasBlocker.mk 2 (-2) (row (-2) (by push_cast; linarith) (by push_cast; linarith))
  · refine HasBlocker.mk 2 (-2) ?_
    intro x hx y hy _
    obtain ⟨h1, h2⟩ := hy
    push_cast at h1 h2
    have := hcol x hx
    have h3 : (v - y) ^ 2 ≤ (-1 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h4 : (-1 - v) ^ 2 ≤ (y0 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith

/-! ### The cell `(3, 2)` and its mirror images -/

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

/-- A threat from one of the cells `(±3, ±2)`, reduced to `(3, 2)` by the reflections. -/
theorem block_three_two_all (hx0 : 0 ≤ x0 ∧ x0 ≤ 1) (hy0 : 0 ≤ y0 ∧ y0 ≤ 1)
    (hu1 : -3 / 2 ≤ u) (hu2 : u ≤ 5 / 2) (hv1 : -3 / 2 ≤ v) (hv2 : v ≤ 5 / 2)
    {a b : ℤ} (ha : a = 3 ∨ a = -3) (hb : b = 2 ∨ b = -2)
    (hqx : qx ∈ Set.Icc (a : ℝ) (a + 1)) (hqy : qy ∈ Set.Icc (b : ℝ) (b + 1))
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker u v x0 y0 := by
  obtain ⟨hx1, hx2⟩ := hqx
  obtain ⟨hy1, hy2⟩ := hqy
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> push_cast at hx1 hx2 hy1 hy2
  · exact block_three_two hx0 hy0 hu2 hv2 ⟨⟨hx1, by linarith⟩, ⟨hy1, by linarith⟩⟩ ht
  · apply HasBlocker.of_reflectY
    refine block_three_two hx0 (reflect01 hy0) hu2 (by linarith) (qy := 1 - qy)
      ⟨⟨hx1, by linarith⟩, ⟨by linarith, by linarith⟩⟩ ?_
    simp only [sq_reflect]
    exact ht
  · apply HasBlocker.of_reflectX
    refine block_three_two (reflect01 hx0) hy0 (by linarith) hv2 (qx := 1 - qx)
      ⟨⟨by linarith, by linarith⟩, ⟨hy1, by linarith⟩⟩ ?_
    simp only [sq_reflect]
    exact ht
  · apply HasBlocker.of_reflectX
    apply HasBlocker.of_reflectY
    refine block_three_two (reflect01 hx0) (reflect01 hy0) (by linarith) (by linarith)
      (qx := 1 - qx) (qy := 1 - qy) ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩ ?_
    simp only [sq_reflect]
    exact ht

/-! ### The blocking theorem -/

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

/-- **Blocking.**  Suppose the origin's site is within squared distance `2` of `(u, v)` (as it is
whenever `(u, v)` lies in the local Voronoi cell, `sqDist_le_two_of_mem_voronoiOn_Nbhd`).  If a
cell other than the origin's and outside `Nbhd` contains a point strictly closer to `(u, v)`
than the origin's site, then some non-origin cell of `Nbhd` consists entirely of points strictly
closer to `(u, v)` than the origin's site.

The radius bound confines the threatening cell to the eight cells `(±3, ±2)`, `(±2, ±3)`:
a point within `√2` of `(u, v)`, which is within `√2` of the origin's site, is within `2√2` of
the unit square, and only the `7 × 7` block minus its corners comes that close.  Those eight
cells are the images of `(3, 2)` under the symmetries of the square (`block_three_two_all`). -/
theorem hasBlocker_of_threat (hx0 : 0 ≤ x0 ∧ x0 ≤ 1) (hy0 : 0 ≤ y0 ∧ y0 ≤ 1)
    (hr : (u - x0) ^ 2 + (v - y0) ^ 2 ≤ 2) {a b : ℤ}
    (hc : (a, b) ∉ Nbhd) (hqx : qx ∈ Set.Icc (a : ℝ) (a + 1)) (hqy : qy ∈ Set.Icc (b : ℝ) (b + 1))
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker u v x0 y0 := by
  -- the test point lies in the box `[-3/2, 5/2]²`
  have hu1 : -3 / 2 ≤ u := by nlinarith [sq_nonneg (v - y0)]
  have hu2 : u ≤ 5 / 2 := by nlinarith [sq_nonneg (v - y0)]
  have hv1 : -3 / 2 ≤ v := by nlinarith [sq_nonneg (u - x0)]
  have hv2 : v ≤ 5 / 2 := by nlinarith [sq_nonneg (u - x0)]
  -- the threat point is within `2√2` of the origin's site
  have h8 : (qx - x0) ^ 2 + (qy - y0) ^ 2 < 8 := by
    nlinarith [sq_nonneg (qx - u - (u - x0)), sq_nonneg (qy - v - (v - y0))]
  -- hence the threatening cell is one of the eight diagonal frontier cells
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
  have hcorner : ¬ (a.natAbs = 3 ∧ b.natAbs = 3) := by
    rintro ⟨ha, hb⟩
    have := sq_le_of_far hqx hx0 (k := 3) (by norm_num) (by omega)
    have := sq_le_of_far hqy hy0 (k := 3) (by norm_num) (by omega)
    norm_num at *
    linarith
  have hc' : ¬ (a.natAbs ≤ 3 ∧ b.natAbs ≤ 3 ∧ a.natAbs + b.natAbs ≤ 4) := hc
  obtain ⟨hqa1, hqa2⟩ := hqx
  obtain ⟨hqb1, hqb2⟩ := hqy
  have ht' : (v - qy) ^ 2 + (u - qx) ^ 2 < (v - y0) ^ 2 + (u - x0) ^ 2 := by linarith
  have cases : ((a = 3 ∨ a = -3) ∧ (b = 2 ∨ b = -2)) ∨ ((a = 2 ∨ a = -2) ∧ (b = 3 ∨ b = -3)) := by
    omega
  rcases cases with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact block_three_two_all hx0 hy0 hu1 hu2 hv1 hv2 ha hb ⟨hqa1, hqa2⟩ ⟨hqb1, hqb2⟩ ht
  · exact HasBlocker.of_swap
      (block_three_two_all hy0 hx0 hv1 hv2 hu1 hu2 hb ha ⟨hqb1, hqb2⟩ ⟨hqa1, hqa2⟩ ht')

end JitteredVoronoi
