import JitteredVoronoi.Basic

/-!
# Necessity: the nearest cell lies in the `5 × 5` block, and is not a corner

The argument compares the target cell `(A, B)` with one of the four axis neighbours
`(±1, 0)`, `(0, ±1)`.  Writing `(x₀, y₀) = f 0 0 ∈ [0,1)²`:

* every point of cell `(1, 0)` has squared distance `< (2 - x₀)² + 1` from `(x₀, y₀)`,
* every point of cell `(-1, 0)` has squared distance `< (x₀ + 1)² + 1`,

and symmetrically for `(0, ±1)`.  If `A ≥ 3`, or `A = 2` and `|B| = 2`, every point of cell
`(A, B)` is at squared distance `≥ (2 - x₀)² + 1`, so cell `(1, 0)` beats it; the other cases
are mirror images.
-/

namespace JitteredVoronoi

variable {f : ℤ → ℤ → ℝ × ℝ} {A B : ℤ}

lemma sq_le_sq_of_le' {c u : ℝ} (hc : 0 ≤ c) (h : c ≤ u) : c ^ 2 ≤ u ^ 2 := by nlinarith
lemma sq_lt_sq_of_lt' {c u : ℝ} (hc : 0 ≤ c) (h : c < u) : c ^ 2 < u ^ 2 := by nlinarith
lemma sq_lt_one_of_abs_lt {v : ℝ} (h1 : -1 < v) (h2 : v < 1) : v ^ 2 < 1 := by nlinarith

/-- Unpack the jitter condition for a cell with concrete integer coordinates. -/
lemma IsJitter.bounds (hf : IsJitter f) (a b : ℤ) :
    (a : ℝ) ≤ (f a b).1 ∧ (f a b).1 < a + 1 ∧ (b : ℝ) ≤ (f a b).2 ∧ (f a b).2 < b + 1 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hf a b
  exact ⟨h1, h2, h3, h4⟩

section AxisNeighbours

variable (hf : IsJitter f)
include hf

lemma sqDist_right_lt : sqDist (f 1 0) (f 0 0) < (2 - (f 0 0).1) ^ 2 + 1 := by
  have h0 := hf.bounds 0 0
  have h1 := hf.bounds 1 0
  push_cast at h0 h1
  have hx := sq_lt_sq_of_lt' (c := (f 1 0).1 - (f 0 0).1) (u := 2 - (f 0 0).1)
    (by linarith) (by linarith)
  have hy := sq_lt_one_of_abs_lt (v := (f 1 0).2 - (f 0 0).2) (by linarith) (by linarith)
  unfold sqDist; linarith

lemma sqDist_left_lt : sqDist (f (-1) 0) (f 0 0) < ((f 0 0).1 + 1) ^ 2 + 1 := by
  have h0 := hf.bounds 0 0
  have h1 := hf.bounds (-1) 0
  push_cast at h0 h1
  have hx := sq_le_sq_of_le' (c := (f 0 0).1 - (f (-1) 0).1) (u := (f 0 0).1 + 1)
    (by linarith) (by linarith)
  have hy := sq_lt_one_of_abs_lt (v := (f (-1) 0).2 - (f 0 0).2) (by linarith) (by linarith)
  unfold sqDist; nlinarith

lemma sqDist_up_lt : sqDist (f 0 1) (f 0 0) < (2 - (f 0 0).2) ^ 2 + 1 := by
  have h0 := hf.bounds 0 0
  have h1 := hf.bounds 0 1
  push_cast at h0 h1
  have hy := sq_lt_sq_of_lt' (c := (f 0 1).2 - (f 0 0).2) (u := 2 - (f 0 0).2)
    (by linarith) (by linarith)
  have hx := sq_lt_one_of_abs_lt (v := (f 0 1).1 - (f 0 0).1) (by linarith) (by linarith)
  unfold sqDist; linarith

lemma sqDist_down_lt : sqDist (f 0 (-1)) (f 0 0) < ((f 0 0).2 + 1) ^ 2 + 1 := by
  have h0 := hf.bounds 0 0
  have h1 := hf.bounds 0 (-1)
  push_cast at h0 h1
  have hy := sq_le_sq_of_le' (c := (f 0 0).2 - (f 0 (-1)).2) (u := (f 0 0).2 + 1)
    (by linarith) (by linarith)
  have hx := sq_lt_one_of_abs_lt (v := (f 0 (-1)).1 - (f 0 0).1) (by linarith) (by linarith)
  unfold sqDist; nlinarith

end AxisNeighbours

section Nearest

variable (hf : IsJitter f) (hN : IsNearest f A B)
include hf hN

/-- A nearest cell is strictly beaten by nothing, in particular not by cell `(1, 0)`. -/
lemma nearest_lt_right : sqDist (f A B) (f 0 0) < (2 - (f 0 0).1) ^ 2 + 1 :=
  lt_of_le_of_lt (hN.2 1 0 (by decide)) (sqDist_right_lt hf)

lemma nearest_lt_left : sqDist (f A B) (f 0 0) < ((f 0 0).1 + 1) ^ 2 + 1 :=
  lt_of_le_of_lt (hN.2 (-1) 0 (by decide)) (sqDist_left_lt hf)

lemma nearest_lt_up : sqDist (f A B) (f 0 0) < (2 - (f 0 0).2) ^ 2 + 1 :=
  lt_of_le_of_lt (hN.2 0 1 (by decide)) (sqDist_up_lt hf)

lemma nearest_lt_down : sqDist (f A B) (f 0 0) < ((f 0 0).2 + 1) ^ 2 + 1 :=
  lt_of_le_of_lt (hN.2 0 (-1) (by decide)) (sqDist_down_lt hf)

lemma not_three_le_A (h : 3 ≤ A) : False := by
  have hlt := nearest_lt_right hf hN
  have h0 := hf.bounds 0 0
  have hAB := hf.bounds A B
  have hA : (3 : ℝ) ≤ A := by exact_mod_cast h
  push_cast at h0
  have hx := sq_le_sq_of_le' (c := 3 - (f 0 0).1) (u := (f A B).1 - (f 0 0).1)
    (by linarith) (by linarith)
  unfold sqDist at hlt
  nlinarith [sq_nonneg ((f A B).2 - (f 0 0).2)]

lemma not_A_le_neg_three (h : A ≤ -3) : False := by
  have hlt := nearest_lt_left hf hN
  have h0 := hf.bounds 0 0
  have hAB := hf.bounds A B
  have hA : (A : ℝ) ≤ -3 := by exact_mod_cast h
  push_cast at h0
  have hx := sq_le_sq_of_le' (c := (f 0 0).1 + 2) (u := (f 0 0).1 - (f A B).1)
    (by linarith) (by linarith)
  unfold sqDist at hlt
  nlinarith [sq_nonneg ((f A B).2 - (f 0 0).2)]

lemma not_three_le_B (h : 3 ≤ B) : False := by
  have hlt := nearest_lt_up hf hN
  have h0 := hf.bounds 0 0
  have hAB := hf.bounds A B
  have hB : (3 : ℝ) ≤ B := by exact_mod_cast h
  push_cast at h0
  have hy := sq_le_sq_of_le' (c := 3 - (f 0 0).2) (u := (f A B).2 - (f 0 0).2)
    (by linarith) (by linarith)
  unfold sqDist at hlt
  nlinarith [sq_nonneg ((f A B).1 - (f 0 0).1)]

lemma not_B_le_neg_three (h : B ≤ -3) : False := by
  have hlt := nearest_lt_down hf hN
  have h0 := hf.bounds 0 0
  have hAB := hf.bounds A B
  have hB : (B : ℝ) ≤ -3 := by exact_mod_cast h
  push_cast at h0
  have hy := sq_le_sq_of_le' (c := (f 0 0).2 + 2) (u := (f 0 0).2 - (f A B).2)
    (by linarith) (by linarith)
  unfold sqDist at hlt
  nlinarith [sq_nonneg ((f A B).1 - (f 0 0).1)]

/-- The corner cells `(±2, ±2)` are never nearest. -/
lemma not_corner (hA : A = 2 ∨ A = -2) (hB : B = 2 ∨ B = -2) : False := by
  have h0 := hf.bounds 0 0
  have hAB := hf.bounds A B
  push_cast at h0
  -- the `y`-part of the squared distance exceeds `1`
  have hy : 1 < ((f A B).2 - (f 0 0).2) ^ 2 := by
    rcases hB with hB | hB
    · have hB' : (B : ℝ) = 2 := by exact_mod_cast hB
      have := sq_lt_sq_of_lt' (c := 1) (u := (f A B).2 - (f 0 0).2) (by norm_num) (by linarith)
      linarith
    · have hB' : (B : ℝ) = -2 := by exact_mod_cast hB
      have := sq_lt_sq_of_lt' (c := 1) (u := (f 0 0).2 - (f A B).2) (by norm_num) (by linarith)
      nlinarith
  rcases hA with hA | hA
  · have hA' : (A : ℝ) = 2 := by exact_mod_cast hA
    have hlt := nearest_lt_right hf hN
    have hx := sq_le_sq_of_le' (c := 2 - (f 0 0).1) (u := (f A B).1 - (f 0 0).1)
      (by linarith) (by linarith)
    unfold sqDist at hlt
    nlinarith
  · have hA' : (A : ℝ) = -2 := by exact_mod_cast hA
    have hlt := nearest_lt_left hf hN
    have hx := sq_le_sq_of_le' (c := (f 0 0).1 + 1) (u := (f 0 0).1 - (f A B).1)
      (by linarith) (by linarith)
    unfold sqDist at hlt
    nlinarith

end Nearest

/-- **Necessity.**  A cell that is nearest under some jitter lies in `Answer`. -/
theorem mem_answer_of_isNearest (hf : IsJitter f) (hN : IsNearest f A B) : (A, B) ∈ Answer := by
  simp only [Answer, Set.mem_ofPred_eq]
  refine ⟨hN.1, ?_, ?_, ?_⟩
  · by_contra h
    rw [not_le, lt_abs] at h
    rcases h with h | h
    · exact not_three_le_A hf hN (by omega)
    · exact not_A_le_neg_three hf hN (by omega)
  · by_contra h
    rw [not_le, lt_abs] at h
    rcases h with h | h
    · exact not_three_le_B hf hN (by omega)
    · exact not_B_le_neg_three hf hN (by omega)
  · rintro ⟨hA, hB⟩
    rw [abs_eq (by norm_num)] at hA hB
    exact not_corner hf hN hA hB

end JitteredVoronoi
