import JitteredVoronoi.Basic
import JitteredVoronoi.Nbhd

/-!
# Witnesses: every non-origin cell of the neighbourhood is needed

For each of the 36 non-origin cells `c ∈ Nbhd` we give a jitter `wit c` and a test point `p`
such that `p` is at least as close to the origin's point as to every other site *except* the one
in `c`, which is strictly closer.  So dropping `c` from the neighbourhood changes the Voronoi
cell of the origin's point.

The data (origin point, test point, site in `c`) are given in decimal notation for the seven
cells with `a ≥ b ≥ 0` (`base`) and transported to the other cells by the symmetries of the
square (`transform`); every other cell `d` gets the corner of `d` farthest from `p` (pulled
inside the half-open cell by `0.01` when that corner is excluded).  The finitely many comparisons with cells in the window
`|a|, |b| ≤ 5` are checked by `decide`; cells farther out are at squared distance at least `16`
from `p`, which exceeds every squared radius that occurs.
-/

namespace JitteredVoronoi

namespace Witness

section Data

/-- Each Data is a witness for a given `cell`. -/
structure Data where
  /-- The cell under test. -/
  cell : ℤ × ℤ
  /-- The origin's point (in the cell `(0, 0)`). -/
  origin : ℚ × ℚ
  /-- The test point. -/
  test : ℚ × ℚ
  /-- The site placed in the cell under test. -/
  site : ℚ × ℚ


/-- The origin's point, as a real point. -/
abbrev Data.originR (w : Data) : ℝ × ℝ := ((w.origin.1 : ℝ), (w.origin.2 : ℝ))
/-- The test point, as a real point. -/
abbrev Data.testR (w : Data) : ℝ × ℝ := ((w.test.1 : ℝ), (w.test.2 : ℝ))
/-- The site placed in the cell under test, as a real point. -/
abbrev Data.siteR (w : Data) : ℝ × ℝ := ((w.site.1 : ℝ), (w.site.2 : ℝ))

/-- The perturbation used to stay inside half-open cells. -/
def eps : ℚ := 0.01

/-- The end of the cell `[a, a+1)` farthest from `u` (as a point of the half-open cell). -/
def far (u : ℚ) (a : ℤ) : ℚ := if u ≤ a + 1 / 2 then a + 1 - eps else a

/-- The full jitter for the data-/
abbrev Data.wit (w : Data) (d : ℤ × ℤ) : ℝ × ℝ :=
  if d = (0, 0) then w.originR
  else if d = w.cell then w.siteR
  else ((far w.test.1 d.1 : ℝ), (far w.test.2 d.2 : ℝ))

end Data

/-- Witness data for the seven cells `(a, b)` with `a ≥ b ≥ 0` in `Nbhd`.  All coordinates of
`origin` and `site` lie strictly inside their cells, so the dihedral images below are valid
witnesses too. -/
def base : ℤ × ℤ → Data
  | (1, 0) => ⟨(1, 0), (0.1, 0.9), (1.05, 0.45), (1.05, 0.45)⟩
  | (1, 1) => ⟨(1, 1), (0.9, 0.85), (1.55, 1.55), (1.55, 1.55)⟩
  | (2, 0) => ⟨(2, 0), (0.9, 0.9), (1.8, 1), (2.01, 0.99)⟩
  | (2, 1) => ⟨(2, 1), (0.9, 0.9), (1.8, 1), (2.01, 1.01)⟩
  | (2, 2) => ⟨(2, 2), (0.99, 0.9), (2, 1.2), (2.01, 2.01)⟩
  | (3, 0) => ⟨(3, 0), (0.9, 0.25), (2.05, 0), (3.01, 0.01)⟩
  | (3, 1) => ⟨(3, 1), (0.95, 0.99), (2.1, 1), (3.01, 1.01)⟩
  | _ => ⟨(0, 0), (0, 0), (0, 0), (0, 0)⟩


/-- The representative `(max |a| |b|, min |a| |b|)` of the cell `(a, b)` under the symmetries of
the square. -/
def rep (c : ℤ × ℤ) : ℤ × ℤ := (max c.1.natAbs c.2.natAbs, min c.1.natAbs c.2.natAbs)

/-- The symmetry of the plane taking the cell `rep c` to the cell `c`: swap the coordinates if
`|a| < |b|`, then reflect `x ↦ 1 - x` if `a < 0` and `y ↦ 1 - y` if `b < 0`. -/
def transform (c : ℤ × ℤ) (pt : ℚ × ℚ) : ℚ × ℚ :=
  let pt' := if c.1.natAbs < c.2.natAbs then (pt.2, pt.1) else pt
  (if c.1 < 0 then 1 - pt'.1 else pt'.1, if c.2 < 0 then 1 - pt'.2 else pt'.2)

/-- The witness data of an arbitrary cell, by symmetry from its representative. -/
def data (c : ℤ × ℤ) : Data :=
  let d := base (rep c)
  ⟨c, transform c d.origin, transform c d.test, transform c d.site⟩

/-- The integers `-5, …, 5`. -/
def window : List ℤ := (List.range 11).map fun n => (n : ℤ) - 5

/-! ### The decidable checks -/

/-- Basic sanity of the data -/
theorem data_check : ∀ c ∈ nbhdList,
    let d := data c
    /-  `origin ∈ [0,1)² -/
    (0 ≤ d.origin.1 ∧ d.origin.1 < 1 ∧ 0 ≤ d.origin.2 ∧ d.origin.2 < 1) ∧
    /- `site ∈ c` -/
    ((c.1 : ℚ) ≤ d.site.1 ∧ d.site.1 < c.1 + 1 ∧ (c.2 : ℚ) ≤ d.site.2 ∧ d.site.2 < c.2 + 1) ∧
    /- `site` strictly closer than `origin` -/
    sqQ d.test d.site < sqQ d.test d.origin ∧
    /- the test point lies in `[-3/2, 5/2]²` -/
    (-3 / 2 ≤ d.test.1 ∧ d.test.1 ≤ 5 / 2 ∧ -3 / 2 ≤ d.test.2 ∧ d.test.2 ≤ 5 / 2) ∧
    /- the squared radius is at most `16` -/
    sqQ d.test d.origin ≤ 16 := by
  decide +kernel

/-- Inside the window, every other cell's far corner is at least as far from the test point as
the origin's point. -/
theorem far_check : ∀ c ∈ nbhdList, ∀ a ∈ window, ∀ b ∈ window, (a, b) ≠ (0, 0) → (a, b) ≠ c →
    sqQ (data c).test (data c).origin ≤ sqQ (data c).test (far (data c).test.1 a, far (data c).test.2 b) := by
  decide +kernel

theorem mem_window {a : ℤ} (h1 : -5 ≤ a) (h2 : a ≤ 5) : a ∈ window := by
  interval_cases a <;> decide

/-! ### Symbolic facts -/

theorem far_mem (u : ℚ) (a : ℤ) : (a : ℚ) ≤ far u a ∧ far u a < a + 1 := by
  unfold far eps
  split_ifs <;> constructor <;> linarith

/-- A cell six or more columns away is at squared distance at least `16` in that coordinate. -/
theorem far_big (u : ℚ) (hu1 : -3 / 2 ≤ u) (hu2 : u ≤ 5 / 2) (a : ℤ) (h : 6 ≤ a.natAbs) :
    16 ≤ (u - far u a) * (u - far u a) := by
  unfold far eps
  rcases (by omega : 6 ≤ a ∨ a ≤ -6) with h | h
  · have ha : (6 : ℚ) ≤ a := by exact_mod_cast h
    rw [if_pos (by linarith)]
    nlinarith
  · have ha : (a : ℚ) ≤ -6 := by exact_mod_cast h
    rw [if_neg (not_le.2 (by linarith))]
    nlinarith

/-! ### The jitter -/

/-- The witnessing jitter for the cell `c`. -/
def wit (c : ℤ × ℤ) (d : ℤ × ℤ) : ℝ × ℝ :=
  if d = (0, 0) then (data c).originR
  else if d = c then (data c).siteR
  else ((far (data c).test.1 d.1 : ℝ), (far (data c).test.2 d.2 : ℝ))

/-- The witnessing jitter is a jitter. -/
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
    have hx := far_mem (data c).test.1 d.1
    have hy := far_mem (data c).test.2 d.2
    exact ⟨⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩, ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩⟩

/-- The test point, as a real point. -/
abbrev testR (c : ℤ × ℤ) : ℝ × ℝ := (data c).testR

end Witness

end JitteredVoronoi
