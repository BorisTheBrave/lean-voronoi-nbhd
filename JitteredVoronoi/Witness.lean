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

/-- The perturbation used to stay inside half-open cells. -/
def eps : ℚ := 0.01

/-- The end of the cell `[a, a+1)` farthest from `u` (as a point of the half-open cell). -/
def far (u : ℚ) (a : ℤ) : ℚ := if u ≤ a + 1 / 2 then a + 1 - eps else a

/-- Squared Euclidean distance over `ℚ`. -/
def sqQ (p q : ℚ × ℚ) : ℚ := (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)

/-- Witness data for the seven cells `(a, b)` with `a ≥ b ≥ 0` in `Nbhd`: the origin's point
`p0`, the test point `p`, and the site `q` placed in the cell.  All coordinates of `p0` and `q`
lie strictly inside their cells, so the dihedral images below are valid witnesses too. -/
def base : ℤ × ℤ → (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ)
  | (1, 0) => ((0.1, 0.9), (1.05, 0.45), (1.05, 0.45))
  | (1, 1) => ((0.9, 0.85), (1.55, 1.55), (1.55, 1.55))
  | (2, 0) => ((0.9, 0.9), (1.8, 1), (2.01, 0.99))
  | (2, 1) => ((0.9, 0.9), (1.8, 1), (2.01, 1.01))
  | (2, 2) => ((0.99, 0.9), (2, 1.2), (2.01, 2.01))
  | (3, 0) => ((0.9, 0.25), (2.05, 0), (3.01, 0.01))
  | (3, 1) => ((0.95, 0.99), (2.1, 1), (3.01, 1.01))
  | _ => ((0, 0), (0, 0), (0, 0))

/-- The representative `(max |a| |b|, min |a| |b|)` of the cell `(a, b)` under the symmetries of
the square. -/
def rep (c : ℤ × ℤ) : ℤ × ℤ := (max c.1.natAbs c.2.natAbs, min c.1.natAbs c.2.natAbs)

/-- The symmetry of the plane taking the cell `rep c` to the cell `c`: swap the coordinates if
`|a| < |b|`, then reflect `x ↦ 1 - x` if `a < 0` and `y ↦ 1 - y` if `b < 0`. -/
def transform (c : ℤ × ℤ) (pt : ℚ × ℚ) : ℚ × ℚ :=
  let pt' := if c.1.natAbs < c.2.natAbs then (pt.2, pt.1) else pt
  (if c.1 < 0 then 1 - pt'.1 else pt'.1, if c.2 < 0 then 1 - pt'.2 else pt'.2)

/-- The witness data of an arbitrary cell, by symmetry from its representative. -/
def data (c : ℤ × ℤ) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) :=
  (transform c (base (rep c)).1, transform c (base (rep c)).2.1, transform c (base (rep c)).2.2)

/-- The origin's point. -/
def p0 (c : ℤ × ℤ) : ℚ × ℚ := (data c).1
/-- The test point. -/
def pt (c : ℤ × ℤ) : ℚ × ℚ := (data c).2.1
/-- The site placed in `c`. -/
def q (c : ℤ × ℤ) : ℚ × ℚ := (data c).2.2

/-- The 36 non-origin cells of `Nbhd`. -/
def nbhdList : List (ℤ × ℤ) :=
  let r := (List.range 7).map fun n => (n : ℤ) - 3
  (r ×ˢ r).filter fun c => c ≠ (0, 0) ∧ c.1.natAbs + c.2.natAbs ≤ 4

/-- The integers `-5, …, 5`. -/
def window : List ℤ := (List.range 11).map fun n => (n : ℤ) - 5

/-! ### The decidable checks -/

/-- Basic sanity of the data: `p0 ∈ [0,1)²`, `q ∈ c`, `q` strictly closer than `p0`, the test
point lies in `[-3/2, 5/2]²`, and the squared radius is at most `16`. -/
theorem data_check : ∀ c ∈ nbhdList,
    (0 ≤ (p0 c).1 ∧ (p0 c).1 < 1 ∧ 0 ≤ (p0 c).2 ∧ (p0 c).2 < 1) ∧
    ((c.1 : ℚ) ≤ (q c).1 ∧ (q c).1 < c.1 + 1 ∧ (c.2 : ℚ) ≤ (q c).2 ∧ (q c).2 < c.2 + 1) ∧
    sqQ (pt c) (q c) < sqQ (pt c) (p0 c) ∧
    (-3 / 2 ≤ (pt c).1 ∧ (pt c).1 ≤ 5 / 2 ∧ -3 / 2 ≤ (pt c).2 ∧ (pt c).2 ≤ 5 / 2) ∧
    sqQ (pt c) (p0 c) ≤ 16 := by
  decide +kernel

/-- Inside the window, every other cell's far corner is at least as far from the test point as
the origin's point. -/
theorem far_check : ∀ c ∈ nbhdList, ∀ a ∈ window, ∀ b ∈ window, (a, b) ≠ (0, 0) → (a, b) ≠ c →
    sqQ (pt c) (p0 c) ≤ sqQ (pt c) (far (pt c).1 a, far (pt c).2 b) := by
  decide +kernel

theorem mem_window {a : ℤ} (h1 : -5 ≤ a) (h2 : a ≤ 5) : a ∈ window := by
  interval_cases a <;> decide

theorem mem_nbhdList {c : ℤ × ℤ} (hc : c ∈ Nbhd) (h0 : c ≠ (0, 0)) : c ∈ nbhdList := by
  obtain ⟨a, b⟩ := c
  have h : a.natAbs ≤ 3 ∧ b.natAbs ≤ 3 ∧ a.natAbs + b.natAbs ≤ 4 := hc
  have ha : -3 ≤ a ∧ a ≤ 3 := by omega
  have hb : -3 ≤ b ∧ b ≤ 3 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> first | decide | (exfalso; revert h h0; decide)

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
  if d = (0, 0) then (((p0 c).1 : ℝ), ((p0 c).2 : ℝ))
  else if d = c then (((q c).1 : ℝ), ((q c).2 : ℝ))
  else ((far (pt c).1 d.1 : ℝ), (far (pt c).2 d.2 : ℝ))

/-- The test point, as a real point. -/
def ptR (c : ℤ × ℤ) : ℝ × ℝ := (((pt c).1 : ℝ), ((pt c).2 : ℝ))

end Witness

end JitteredVoronoi
