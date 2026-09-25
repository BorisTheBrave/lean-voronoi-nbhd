import JitteredVoronoi.Nbhd

/-!
# Witnesses: every non-origin cell of the neighbourhood is needed

For each of the 36 non-origin cells `c ∈ Nbhd` we give a jitter `wit c` and a test point `p`
such that `p` is at least as close to the origin's point as to every other site *except* the one
in `c`, which is strictly closer.  So dropping `c` from the neighbourhood changes the Voronoi
cell of the origin's point.

The data (origin point, test point, site in `c`) are rational and listed in `table`; every other
cell `d` gets the corner of `d` farthest from `p` (pulled inside the half-open cell by `1/100`
when that corner is excluded).  The finitely many comparisons with cells in the window
`|a|, |b| ≤ 5` are checked by `decide`; cells farther out are at squared distance at least `16`
from `p`, which exceeds every squared radius in the table.
-/

namespace JitteredVoronoi

namespace Witness

/-- The perturbation used to stay inside half-open cells. -/
def eps : ℚ := 1 / 100

/-- The end of the cell `[a, a+1)` farthest from `u` (as a point of the half-open cell). -/
def far (u : ℚ) (a : ℤ) : ℚ := if u ≤ a + 1 / 2 then a + 1 - eps else a

/-- Squared Euclidean distance over `ℚ`. -/
def sqQ (p q : ℚ × ℚ) : ℚ := (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)

/-- For each cell: the origin's point `p0`, the test point `p`, and the site `q` placed in the
cell. -/
def table : List ((ℤ × ℤ) × (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ)) := [
  ((-3, -1), (((1 : ℚ) / 20, (1 : ℚ) / 10), (((-11 : ℚ) / 10), (0 : ℚ)), (((-201 : ℚ) / 100), ((-1 : ℚ) / 100)))),
  ((-3, 0), (((1 : ℚ) / 20, (1 : ℚ) / 10), (((-11 : ℚ) / 10), (0 : ℚ)), (((-201 : ℚ) / 100), (0 : ℚ)))),
  ((-3, 1), (((1 : ℚ) / 10, (3 : ℚ) / 4), (((-21 : ℚ) / 20), (1 : ℚ)), (((-201 : ℚ) / 100), (1 : ℚ)))),
  ((-2, -2), (((0 : ℚ), (0 : ℚ)), (((-1 : ℚ) / 4), (-1 : ℚ)), (((-101 : ℚ) / 100), ((-101 : ℚ) / 100)))),
  ((-2, -1), (((1 : ℚ) / 10, (1 : ℚ) / 10), (((-4 : ℚ) / 5), (0 : ℚ)), (((-101 : ℚ) / 100), ((-1 : ℚ) / 100)))),
  ((-2, 0), (((1 : ℚ) / 10, (9 : ℚ) / 10), (((-4 : ℚ) / 5), (1 : ℚ)), (((-101 : ℚ) / 100), (99 : ℚ) / 100))),
  ((-2, 1), (((1 : ℚ) / 10, (9 : ℚ) / 10), (((-4 : ℚ) / 5), (1 : ℚ)), (((-101 : ℚ) / 100), (1 : ℚ)))),
  ((-2, 2), (((0 : ℚ), (19 : ℚ) / 20), (((-1 : ℚ) / 5), (2 : ℚ)), (((-101 : ℚ) / 100), (2 : ℚ)))),
  ((-1, -3), (((0 : ℚ), (1 : ℚ) / 20), ((0 : ℚ), ((-11 : ℚ) / 10)), (((-1 : ℚ) / 100), ((-201 : ℚ) / 100)))),
  ((-1, -2), (((1 : ℚ) / 10, (1 : ℚ) / 10), ((0 : ℚ), ((-4 : ℚ) / 5)), (((-1 : ℚ) / 100), ((-101 : ℚ) / 100)))),
  ((-1, -1), (((1 : ℚ) / 10, (3 : ℚ) / 20), (((-11 : ℚ) / 20), ((-11 : ℚ) / 20)), (((-11 : ℚ) / 20), ((-11 : ℚ) / 20)))),
  ((-1, 0), (((19 : ℚ) / 20, (11 : ℚ) / 20), (((-1 : ℚ) / 20), (9 : ℚ) / 20), (((-1 : ℚ) / 20), (9 : ℚ) / 20))),
  ((-1, 1), (((1 : ℚ) / 10, (9 : ℚ) / 10), (((-11 : ℚ) / 20), (31 : ℚ) / 20), (((-11 : ℚ) / 20), (31 : ℚ) / 20))),
  ((-1, 2), (((1 : ℚ) / 10, (9 : ℚ) / 10), ((0 : ℚ), (9 : ℚ) / 5), (((-1 : ℚ) / 100), (2 : ℚ)))),
  ((-1, 3), (((0 : ℚ), (19 : ℚ) / 20), ((0 : ℚ), (21 : ℚ) / 10), (((-1 : ℚ) / 100), (3 : ℚ)))),
  ((0, -3), (((0 : ℚ), (1 : ℚ) / 20), ((0 : ℚ), ((-11 : ℚ) / 10)), ((0 : ℚ), ((-201 : ℚ) / 100)))),
  ((0, -2), (((1 : ℚ) / 10, (1 : ℚ) / 10), ((0 : ℚ), ((-4 : ℚ) / 5)), ((0 : ℚ), ((-101 : ℚ) / 100)))),
  ((0, -1), (((7 : ℚ) / 20, (19 : ℚ) / 20), ((11 : ℚ) / 20, ((-1 : ℚ) / 20)), ((11 : ℚ) / 20, ((-1 : ℚ) / 20)))),
  ((0, 1), (((3 : ℚ) / 5, (1 : ℚ) / 20), ((9 : ℚ) / 20, (21 : ℚ) / 20), ((9 : ℚ) / 20, (21 : ℚ) / 20))),
  ((0, 2), (((9 : ℚ) / 10, (9 : ℚ) / 10), ((1 : ℚ), (9 : ℚ) / 5), ((99 : ℚ) / 100, (2 : ℚ)))),
  ((0, 3), (((19 : ℚ) / 20, (19 : ℚ) / 20), ((1 : ℚ), (21 : ℚ) / 10), ((99 : ℚ) / 100, (3 : ℚ)))),
  ((1, -3), (((99 : ℚ) / 100, (1 : ℚ) / 20), ((1 : ℚ), ((-11 : ℚ) / 10)), ((1 : ℚ), ((-201 : ℚ) / 100)))),
  ((1, -2), (((9 : ℚ) / 10, (1 : ℚ) / 10), ((1 : ℚ), ((-4 : ℚ) / 5)), ((1 : ℚ), ((-101 : ℚ) / 100)))),
  ((1, -1), (((17 : ℚ) / 20, (1 : ℚ) / 10), ((31 : ℚ) / 20, ((-11 : ℚ) / 20)), ((31 : ℚ) / 20, ((-11 : ℚ) / 20)))),
  ((1, 0), (((1 : ℚ) / 10, (9 : ℚ) / 10), ((21 : ℚ) / 20, (9 : ℚ) / 20), ((21 : ℚ) / 20, (9 : ℚ) / 20))),
  ((1, 1), (((9 : ℚ) / 10, (17 : ℚ) / 20), ((31 : ℚ) / 20, (31 : ℚ) / 20), ((31 : ℚ) / 20, (31 : ℚ) / 20))),
  ((1, 2), (((9 : ℚ) / 10, (9 : ℚ) / 10), ((1 : ℚ), (9 : ℚ) / 5), ((1 : ℚ), (2 : ℚ)))),
  ((1, 3), (((19 : ℚ) / 20, (19 : ℚ) / 20), ((1 : ℚ), (21 : ℚ) / 10), ((1 : ℚ), (3 : ℚ)))),
  ((2, -2), (((19 : ℚ) / 20, (1 : ℚ) / 2), ((2 : ℚ), ((-1 : ℚ) / 20)), ((2 : ℚ), ((-101 : ℚ) / 100)))),
  ((2, -1), (((9 : ℚ) / 10, (1 : ℚ) / 10), ((9 : ℚ) / 5, (0 : ℚ)), ((2 : ℚ), ((-1 : ℚ) / 100)))),
  ((2, 0), (((9 : ℚ) / 10, (9 : ℚ) / 10), ((9 : ℚ) / 5, (1 : ℚ)), ((2 : ℚ), (99 : ℚ) / 100))),
  ((2, 1), (((9 : ℚ) / 10, (9 : ℚ) / 10), ((9 : ℚ) / 5, (1 : ℚ)), ((2 : ℚ), (1 : ℚ)))),
  ((2, 2), (((99 : ℚ) / 100, (9 : ℚ) / 10), ((2 : ℚ), (6 : ℚ) / 5), ((2 : ℚ), (2 : ℚ)))),
  ((3, -1), (((9 : ℚ) / 10, (1 : ℚ) / 4), ((41 : ℚ) / 20, (0 : ℚ)), ((3 : ℚ), ((-1 : ℚ) / 100)))),
  ((3, 0), (((9 : ℚ) / 10, (1 : ℚ) / 4), ((41 : ℚ) / 20, (0 : ℚ)), ((3 : ℚ), (0 : ℚ)))),
  ((3, 1), (((19 : ℚ) / 20, (99 : ℚ) / 100), ((21 : ℚ) / 10, (1 : ℚ)), ((3 : ℚ), (1 : ℚ))))]

/-- The 36 non-origin cells of `Nbhd`. -/
def nbhdList : List (ℤ × ℤ) := [(-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1)]

/-- Look up the data of a cell (the default is never used). -/
def data (c : ℤ × ℤ) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) :=
  ((table.find? fun e => e.1 = c).map (·.2)).getD ((0, 0), (0, 0), (0, 0))

/-- The origin's point. -/
def p0 (c : ℤ × ℤ) : ℚ × ℚ := (data c).1
/-- The test point. -/
def pt (c : ℤ × ℤ) : ℚ × ℚ := (data c).2.1
/-- The site placed in `c`. -/
def q (c : ℤ × ℤ) : ℚ × ℚ := (data c).2.2

/-- The integers `-5, …, 5`. -/
def window : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

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
