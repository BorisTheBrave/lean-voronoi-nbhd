import JitteredVoronoi.Cell
import JitteredVoronoi.Nbhd

/-!
# Blocking: cells outside the neighbourhood never cut the origin's Voronoi cell

Fix the origin's point `(x0, y0)` (in cell `(0, 0)`) and a test point `p = (u, v)`.  A cell
`(a, b)` *threatens* `p` if it contains a point strictly closer to `p` than `(x0, y0)` is; a cell
`(a', b')` *blocks* `p` if *every* point of it is strictly closer to `p` than `(x0, y0)` is.

The main result of this file, `hasBlocker_of_threat`, says: if a cell outside `Nbhd` threatens
`p`, then some non-origin cell of `Nbhd` blocks `p`.  Consequently, for any jitter, `p` is not in
the Voronoi cell of the origin's point computed from `Nbhd` alone, so the cells outside `Nbhd`
are irrelevant.

The proof works with abstract cell conventions (`CellStructure`) so that the reflections
`x ↦ 1 - x`, `y ↦ 1 - y` and the swap `x ↔ y` can be used to reduce to three frontier
configurations:

* `far_right`: if `u ≥ 5/2` some cell `(2, b')` blocks — no threat is needed;
* `coreR0`, `coreR1`: threats from `x ≥ 4` in the rows `0 ≤ y ≤ 1`, `1 ≤ y ≤ 2`;
* `coreD`: threats from the quadrant `x ≥ 3`, `y ≥ 2`.

Each case is settled by choosing the blocking cell explicitly, bounding the squared distances
corner by corner, and finishing with linear arithmetic.
-/

namespace JitteredVoronoi

open CellStructure

variable (Cx Cy : CellStructure)

/-- Every point of cell `(a', b')` is strictly closer to `(u, v)` than `(x0, y0)` is. -/
def Blocked (u v x0 y0 : ℝ) (a' b' : ℤ) : Prop :=
  ∀ x ∈ Cx.I a', ∀ y ∈ Cy.I b', (u - x) ^ 2 + (v - y) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2

/-- Some non-origin cell of `Nbhd` blocks `(u, v)`. -/
def HasBlocker (u v x0 y0 : ℝ) : Prop :=
  ∃ a' b' : ℤ, (a', b') ∈ Nbhd ∧ (a', b') ≠ (0, 0) ∧ Blocked Cx Cy u v x0 y0 a' b'

variable {Cx Cy}
variable {u v x0 y0 qx qy : ℝ}

theorem HasBlocker.mk (a' b' : ℤ) (h : Blocked Cx Cy u v x0 y0 a' b')
    (hN : a'.natAbs ≤ 3 ∧ b'.natAbs ≤ 3 ∧ a'.natAbs + b'.natAbs ≤ 4 := by decide)
    (h0 : (a', b') ≠ (0, 0) := by decide) : HasBlocker Cx Cy u v x0 y0 :=
  ⟨a', b', hN, h0, h⟩

/-! ### Symmetries -/

theorem sq_reflect (s t : ℝ) : ((1 - s) - (1 - t)) ^ 2 = (s - t) ^ 2 := by ring

theorem Blocked.of_reflectX {a' b' : ℤ}
    (h : Blocked Cx.reflect Cy (1 - u) v (1 - x0) y0 a' b') :
    Blocked Cx Cy u v x0 y0 (-a') b' := by
  intro x hx y hy
  have hx' : 1 - x ∈ Cx.reflect.I a' := by
    have := Cx.mem_reflect_of_mem hx
    rwa [neg_neg] at this
  have := h (1 - x) hx' y hy
  simp only [sq_reflect] at this
  exact this

theorem Blocked.of_reflectY {a' b' : ℤ}
    (h : Blocked Cx Cy.reflect u (1 - v) x0 (1 - y0) a' b') :
    Blocked Cx Cy u v x0 y0 a' (-b') := by
  intro x hx y hy
  have hy' : 1 - y ∈ Cy.reflect.I b' := by
    have := Cy.mem_reflect_of_mem hy
    rwa [neg_neg] at this
  have := h x hx (1 - y) hy'
  simp only [sq_reflect] at this
  exact this

theorem Blocked.of_swap {a' b' : ℤ} (h : Blocked Cy Cx v u y0 x0 b' a') :
    Blocked Cx Cy u v x0 y0 a' b' := by
  intro x hx y hy
  have := h y hy x hx
  linarith

theorem HasBlocker.of_reflectX (h : HasBlocker Cx.reflect Cy (1 - u) v (1 - x0) y0) :
    HasBlocker Cx Cy u v x0 y0 := by
  obtain ⟨a', b', hN, h0, hB⟩ := h
  refine ⟨-a', b', mem_Nbhd_neg_fst.2 hN, ?_, hB.of_reflectX⟩
  intro e
  apply h0
  simp only [Prod.mk.injEq] at e ⊢
  omega

theorem HasBlocker.of_reflectY (h : HasBlocker Cx Cy.reflect u (1 - v) x0 (1 - y0)) :
    HasBlocker Cx Cy u v x0 y0 := by
  obtain ⟨a', b', hN, h0, hB⟩ := h
  refine ⟨a', -b', mem_Nbhd_neg_snd.2 hN, ?_, hB.of_reflectY⟩
  intro e
  apply h0
  simp only [Prod.mk.injEq] at e ⊢
  omega

theorem HasBlocker.of_swap (h : HasBlocker Cy Cx v u y0 x0) : HasBlocker Cx Cy u v x0 y0 := by
  obtain ⟨a', b', hN, h0, hB⟩ := h
  refine ⟨b', a', mem_Nbhd_swap.2 hN, ?_, hB.of_swap⟩
  intro e
  apply h0
  simp only [Prod.mk.injEq] at e ⊢
  exact ⟨e.2, e.1⟩

/-! ### Bounds for the origin cell -/

theorem CellStructure.bounds0 (C : CellStructure) {x : ℝ} (hx : x ∈ C.I 0) : 0 ≤ x ∧ x ≤ 1 := by
  have := C.le_of_mem 0 x hx
  push_cast at this
  simpa using this

/-! ### Far centres: `u ≥ 5/2` -/

/-- If the test point is far to the right, the column `x ∈ [2, 3]` blocks it whatever the
threat. -/
theorem far_right (hx0 : x0 ∈ Cx.I 0) (hy0 : y0 ∈ Cy.I 0) (hu : 5 / 2 ≤ u) :
    HasBlocker Cx Cy u v x0 y0 := by
  obtain ⟨hx01, hx02⟩ := Cx.bounds0 hx0
  obtain ⟨hy01, hy02⟩ := Cy.bounds0 hy0
  -- strict slack in the `x` direction for every point of column `2`
  have hcol : ∀ x ∈ Cx.I 2, (u - x) ^ 2 + 1 < (u - x0) ^ 2 := by
    intro x hx
    obtain ⟨h1, h2⟩ := Cx.le_of_mem 2 x hx
    have h3 := Cx.sep 0 2 (by norm_num) x0 hx0 x hx
    push_cast at h1 h2 h3
    nlinarith [mul_pos (show 0 < x - x0 - 1 by linarith) (show 0 < 2 * u - x - x0 by linarith)]
  -- the row containing `v` blocks
  have row : ∀ b' : ℤ, (b' : ℝ) ≤ v → v ≤ b' + 1 → Blocked Cx Cy u v x0 y0 2 b' := by
    intro b' hv1 hv2 x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem b' y hy
    have h3 : (v - y) ^ 2 ≤ 1 := by nlinarith
    have := hcol x hx
    nlinarith [sq_nonneg (v - y0)]
  rcases le_or_gt 3 v with hv | hv
  · refine HasBlocker.mk 2 2 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem 2 y hy
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
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem (-2) y hy
    push_cast at h1 h2
    have := hcol x hx
    have h3 : (v - y) ^ 2 ≤ (-1 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h4 : (-1 - v) ^ 2 ≤ (y0 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith

/-! ### Frontier threats from the right -/

/-- A threat from `x ≥ 4`, `0 ≤ y ≤ 1` (any cell `(a, 0)` with `a ≥ 4`). -/
theorem coreR0 (hu : u ≤ 5 / 2)
    (hqx : 4 ≤ qx) (hqy1 : 0 ≤ qy) (hqy2 : qy ≤ 1)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker Cx Cy u v x0 y0 := by
  have hX : ∀ x ∈ Cx.I 2, (u - x) ^ 2 ≤ (3 - u) ^ 2 := fun x hx => by
    obtain ⟨h1, h2⟩ := Cx.le_of_mem 2 x hx
    push_cast at h1 h2
    exact sq_le_sq' (by linarith) (by linarith)
  have hQ : (4 - u) ^ 2 ≤ (u - qx) ^ 2 := by nlinarith
  rcases le_or_gt (3 / 2) v with hv | hv
  · refine HasBlocker.mk 2 1 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem 1 y hy
    push_cast at h1 h2
    have h3 : (v - y) ^ 2 ≤ (v - 1) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h4 : (v - 1) ^ 2 ≤ (v - qy) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [hX x hx]
  rcases le_or_gt (-1 / 2) v with hv' | hv'
  · refine HasBlocker.mk 2 0 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem 0 y hy
    push_cast at h1 h2
    have key : (v - y) ^ 2 - (v - qy) ^ 2 ≤ 2 := by
      have e : (v - y) ^ 2 - (v - qy) ^ 2 = (qy - y) * (2 * v - y - qy) := by ring
      rw [e]
      rcases le_total y qy with h | h
      · nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 h) h1,
          mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hqy2)]
      · nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 h) hqy1,
          mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h2)]
    nlinarith [hX x hx]
  · refine HasBlocker.mk 2 (-1) ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem (-1) y hy
    push_cast at h1 h2
    have h3 : (v - y) ^ 2 ≤ (-v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h4 : (-v) ^ 2 ≤ (qy - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [hX x hx]

/-- A threat from `x ≥ 4`, `1 ≤ y ≤ 2` (any cell `(a, 1)` with `a ≥ 4`). -/
theorem coreR1 (hu : u ≤ 5 / 2)
    (hqx : 4 ≤ qx) (hqy1 : 1 ≤ qy) (hqy2 : qy ≤ 2)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker Cx Cy u v x0 y0 := by
  have hX : ∀ x ∈ Cx.I 2, (u - x) ^ 2 ≤ (3 - u) ^ 2 := fun x hx => by
    obtain ⟨h1, h2⟩ := Cx.le_of_mem 2 x hx
    push_cast at h1 h2
    exact sq_le_sq' (by linarith) (by linarith)
  have hQ : (4 - u) ^ 2 ≤ (u - qx) ^ 2 := by nlinarith
  rcases le_or_gt (5 / 2) v with hv | hv
  · refine HasBlocker.mk 2 2 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem 2 y hy
    push_cast at h1 h2
    have h3 : (v - y) ^ 2 ≤ (v - 2) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h4 : (v - 2) ^ 2 ≤ (v - qy) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [hX x hx]
  rcases le_or_gt (1 / 2) v with hv' | hv'
  · refine HasBlocker.mk 2 1 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem 1 y hy
    push_cast at h1 h2
    have key : (v - y) ^ 2 - (v - qy) ^ 2 ≤ 2 := by
      have e : (v - y) ^ 2 - (v - qy) ^ 2 = (qy - y) * (2 * v - y - qy) := by ring
      rw [e]
      rcases le_total y qy with h | h
      · nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h),
          mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h1),
          mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hqy2)]
      · nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h),
          mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hqy1),
          mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h2)]
    nlinarith [hX x hx]
  · refine HasBlocker.mk 2 0 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cy.le_of_mem 0 y hy
    push_cast at h1 h2
    have h3 : (v - y) ^ 2 ≤ (1 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h4 : (1 - v) ^ 2 ≤ (qy - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [hX x hx]

/-- A threat from `x ≥ 4`, `-1 ≤ y ≤ 2` (any cell `(a, b)` with `a ≥ 4`, `|b| ≤ 1`). -/
theorem coreR (hu : u ≤ 5 / 2)
    (hqx : 4 ≤ qx) (hqy1 : -1 ≤ qy) (hqy2 : qy ≤ 2)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker Cx Cy u v x0 y0 := by
  rcases le_or_gt 1 qy with h | h
  · exact coreR1 hu hqx h hqy2 ht
  rcases le_or_gt 0 qy with h' | h'
  · exact coreR0 hu hqx h' h.le ht
  · apply HasBlocker.of_reflectY
    refine coreR1 (Cy := Cy.reflect) hu hqx (qy := 1 - qy) (by linarith) (by linarith) ?_
    simp only [sq_reflect]
    exact ht

/-- Threats from the right or from the left, in the rows `|b| ≤ 1`. -/
theorem coreR_all (hu1 : -3 / 2 ≤ u) (hu2 : u ≤ 5 / 2)
    (hqx : 4 ≤ qx ∨ qx ≤ -3) (hqy1 : -1 ≤ qy) (hqy2 : qy ≤ 2)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker Cx Cy u v x0 y0 := by
  rcases hqx with h | h
  · exact coreR hu2 h hqy1 hqy2 ht
  · apply HasBlocker.of_reflectX
    refine coreR (Cx := Cx.reflect) (by linarith) (qx := 1 - qx) (by linarith) hqy1 hqy2 ?_
    simp only [sq_reflect]
    exact ht

/-! ### Frontier threats from a diagonal quadrant -/

/-- A threat from the quadrant `x ≥ 3`, `y ≥ 2` (any cell `(a, b)` with `a ≥ 3`, `b ≥ 2`). -/
theorem coreD (hx0 : x0 ∈ Cx.I 0) (hy0 : y0 ∈ Cy.I 0) (hu : u ≤ 5 / 2) (hv : v ≤ 5 / 2)
    (hqx : 3 ≤ qx) (hqy : 2 ≤ qy)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker Cx Cy u v x0 y0 := by
  have hQx : (3 - u) ^ 2 ≤ (u - qx) ^ 2 := by nlinarith
  rcases le_or_gt v (3 / 2) with hv1 | hv1
  · -- the cell `(2, 1)` dominates
    refine HasBlocker.mk 2 1 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cx.le_of_mem 2 x hx
    obtain ⟨h3, h4⟩ := Cy.le_of_mem 1 y hy
    push_cast at h1 h2 h3 h4
    have hX : (u - x) ^ 2 ≤ (3 - u) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hY : (v - y) ^ 2 ≤ (2 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hQy : (2 - v) ^ 2 ≤ (v - qy) ^ 2 := by nlinarith
    linarith
  rcases le_or_gt u (3 / 2) with hu1 | hu1
  · rcases le_or_gt v 2 with hv2 | hv2
    · -- the cell `(1, 1)` dominates
      refine HasBlocker.mk 1 1 ?_
      intro x hx y hy
      obtain ⟨h1, h2⟩ := Cx.le_of_mem 1 x hx
      obtain ⟨h3, h4⟩ := Cy.le_of_mem 1 y hy
      push_cast at h1 h2 h3 h4
      have hX : (u - x) ^ 2 ≤ (2 - u) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hY : (v - y) ^ 2 ≤ (v - 1) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hQy : (2 - v) ^ 2 ≤ (v - qy) ^ 2 := by nlinarith
      nlinarith
    · -- the cell `(1, 2)` dominates
      refine HasBlocker.mk 1 2 ?_
      intro x hx y hy
      obtain ⟨h1, h2⟩ := Cx.le_of_mem 1 x hx
      obtain ⟨h3, h4⟩ := Cy.le_of_mem 2 y hy
      push_cast at h1 h2 h3 h4
      have hX : (u - x) ^ 2 ≤ (2 - u) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hY : (v - y) ^ 2 ≤ (3 - v) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have hY1 : (3 - v) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (v - qy)]
  · -- `u > 3/2`, `v > 3/2`: the cell `(1, 1)` is closer than the origin's point can ever be
    refine HasBlocker.mk 1 1 ?_
    intro x hx y hy
    obtain ⟨h1, h2⟩ := Cx.le_of_mem 1 x hx
    obtain ⟨h3, h4⟩ := Cy.le_of_mem 1 y hy
    push_cast at h1 h2 h3 h4
    have hx' := Cx.lt_of_mem (by norm_num : (0 : ℤ) < 1) hx0 hx
    have hy' := Cy.lt_of_mem (by norm_num : (0 : ℤ) < 1) hy0 hy
    obtain ⟨hx01, hx02⟩ := Cx.bounds0 hx0
    obtain ⟨hy01, hy02⟩ := Cy.bounds0 hy0
    nlinarith [mul_pos (sub_pos.2 hx') (show 0 < 2 * u - x - x0 by linarith),
      mul_nonneg (sub_pos.2 hy').le (show 0 ≤ 2 * v - y - y0 by linarith)]

/-- Threats from any of the four diagonal quadrants `|x| ≥ 3`-ish, `|y| ≥ 2`-ish. -/
theorem coreD_all (hx0 : x0 ∈ Cx.I 0) (hy0 : y0 ∈ Cy.I 0)
    (hu1 : -3 / 2 ≤ u) (hu2 : u ≤ 5 / 2) (hv1 : -3 / 2 ≤ v) (hv2 : v ≤ 5 / 2)
    (hqx : 3 ≤ qx ∨ qx ≤ -2) (hqy : 2 ≤ qy ∨ qy ≤ -1)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker Cx Cy u v x0 y0 := by
  rcases hqx with hx | hx <;> rcases hqy with hy | hy
  · exact coreD hx0 hy0 hu2 hv2 hx hy ht
  · apply HasBlocker.of_reflectY
    refine coreD hx0 (Cy.mem_reflect_zero hy0) hu2 (by linarith) hx (qy := 1 - qy) (by linarith) ?_
    simp only [sq_reflect]
    exact ht
  · apply HasBlocker.of_reflectX
    refine coreD (Cx.mem_reflect_zero hx0) hy0 (by linarith) hv2 (qx := 1 - qx) (by linarith) hy ?_
    simp only [sq_reflect]
    exact ht
  · apply HasBlocker.of_reflectX
    apply HasBlocker.of_reflectY
    refine coreD (Cx.mem_reflect_zero hx0) (Cy.mem_reflect_zero hy0) (by linarith) (by linarith)
      (qx := 1 - qx) (by linarith) (qy := 1 - qy) (by linarith) ?_
    simp only [sq_reflect]
    exact ht

/-! ### The blocking theorem -/

/-- **Blocking.**  If a cell outside `Nbhd` contains a point strictly closer to `(u, v)` than the
origin's point `(x0, y0)`, then some non-origin cell of `Nbhd` consists entirely of points
strictly closer to `(u, v)` than `(x0, y0)`. -/
theorem hasBlocker_of_threat (hx0 : x0 ∈ Cx.I 0) (hy0 : y0 ∈ Cy.I 0) {a b : ℤ}
    (hc : (a, b) ∉ Nbhd) (hqx : qx ∈ Cx.I a) (hqy : qy ∈ Cy.I b)
    (ht : (u - qx) ^ 2 + (v - qy) ^ 2 < (u - x0) ^ 2 + (v - y0) ^ 2) :
    HasBlocker Cx Cy u v x0 y0 := by
  -- Step 1: far centres are blocked whatever the threat.
  rcases le_or_gt (5 / 2) u with hu1 | hu1
  · exact far_right hx0 hy0 hu1
  rcases le_or_gt u (-3 / 2) with hu2 | hu2
  · exact HasBlocker.of_reflectX (far_right (Cx.mem_reflect_zero hx0) hy0 (by linarith))
  rcases le_or_gt (5 / 2) v with hv1 | hv1
  · exact HasBlocker.of_swap (far_right hy0 hx0 hv1)
  rcases le_or_gt v (-3 / 2) with hv2 | hv2
  · exact HasBlocker.of_swap
      (HasBlocker.of_reflectX (far_right (Cy.mem_reflect_zero hy0) hx0 (by linarith)))
  -- Step 2: the threat comes from one of four frontier regions.
  obtain ⟨hqa1, hqa2⟩ := Cx.le_of_mem a qx hqx
  obtain ⟨hqb1, hqb2⟩ := Cy.le_of_mem b qy hqy
  have hc' : ¬ (a.natAbs ≤ 3 ∧ b.natAbs ≤ 3 ∧ a.natAbs + b.natAbs ≤ 4) := hc
  have ht' : (v - qy) ^ 2 + (u - qx) ^ 2 < (v - y0) ^ 2 + (u - x0) ^ 2 := by linarith
  have cases : (4 ≤ a.natAbs ∧ b.natAbs ≤ 1) ∨ (4 ≤ b.natAbs ∧ a.natAbs ≤ 1) ∨
      (3 ≤ a.natAbs ∧ 2 ≤ b.natAbs) ∨ (2 ≤ a.natAbs ∧ 3 ≤ b.natAbs) := by omega
  rcases cases with ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- rows `|b| ≤ 1`, columns `|a| ≥ 4`
    have hb1 : (-1 : ℝ) ≤ b := by exact_mod_cast (by omega : (-1 : ℤ) ≤ b)
    have hb2 : (b : ℝ) ≤ 1 := by exact_mod_cast (by omega : b ≤ 1)
    refine coreR_all hu2.le hu1.le ?_ (by linarith) (by linarith) ht
    rcases (by omega : 4 ≤ a ∨ a ≤ -4) with h | h
    · left; have : (4 : ℝ) ≤ a := by exact_mod_cast h
      linarith
    · right; have : (a : ℝ) ≤ -4 := by exact_mod_cast h
      linarith
  · -- columns `|a| ≤ 1`, rows `|b| ≥ 4`: swap the roles of the axes
    have ha1 : (-1 : ℝ) ≤ a := by exact_mod_cast (by omega : (-1 : ℤ) ≤ a)
    have ha2 : (a : ℝ) ≤ 1 := by exact_mod_cast (by omega : a ≤ 1)
    apply HasBlocker.of_swap
    refine coreR_all hv2.le hv1.le ?_ (by linarith) (by linarith) ht'
    rcases (by omega : 4 ≤ b ∨ b ≤ -4) with h | h
    · left; have : (4 : ℝ) ≤ b := by exact_mod_cast h
      linarith
    · right; have : (b : ℝ) ≤ -4 := by exact_mod_cast h
      linarith
  · -- `|a| ≥ 3`, `|b| ≥ 2`
    refine coreD_all hx0 hy0 hu2.le hu1.le hv2.le hv1.le ?_ ?_ ht
    · rcases (by omega : 3 ≤ a ∨ a ≤ -3) with h | h
      · left; have : (3 : ℝ) ≤ a := by exact_mod_cast h
        linarith
      · right; have : (a : ℝ) ≤ -3 := by exact_mod_cast h
        linarith
    · rcases (by omega : 2 ≤ b ∨ b ≤ -2) with h | h
      · left; have : (2 : ℝ) ≤ b := by exact_mod_cast h
        linarith
      · right; have : (b : ℝ) ≤ -2 := by exact_mod_cast h
        linarith
  · -- `|a| ≥ 2`, `|b| ≥ 3`: swap the roles of the axes
    apply HasBlocker.of_swap
    refine coreD_all hy0 hx0 hv2.le hv1.le hu2.le hu1.le ?_ ?_ ht'
    · rcases (by omega : 3 ≤ b ∨ b ≤ -3) with h | h
      · left; have : (3 : ℝ) ≤ b := by exact_mod_cast h
        linarith
      · right; have : (b : ℝ) ≤ -3 := by exact_mod_cast h
        linarith
    · rcases (by omega : 2 ≤ a ∨ a ≤ -2) with h | h
      · left; have : (2 : ℝ) ≤ a := by exact_mod_cast h
        linarith
      · right; have : (a : ℝ) ≤ -2 := by exact_mod_cast h
        linarith

end JitteredVoronoi
