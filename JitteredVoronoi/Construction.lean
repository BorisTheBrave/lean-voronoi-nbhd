import JitteredVoronoi.Basic

/-!
# Sufficiency: an explicit jitter for each of the twenty cells

For a target cell `(A, B)` in `Answer` we build a jitter `jitter A B` with the target cell
nearest.  The recipe, coordinate by coordinate:

* the origin point is `(base A, base B)`, where `base A = 1/2 + sign A / 10`, i.e. the origin
  point is nudged slightly towards the target cell;
* the target point `(tgt A, tgt B)` is (up to `ε = 1/100` for negative coordinates, where the
  nearest corner is excluded by half-openness) the point of the target cell closest to the origin
  point;
* every other cell `(a, b)` gets the point `(far A a, far B b)`, where `far A a` is (up to `ε`)
  the point of `[a, a+1)` farthest from `base A`.

All numbers are rational, so the finitely many comparisons among cells in the `5 × 5` block are
checked by `decide`; cells outside the block are far away for trivial reasons.
-/

namespace JitteredVoronoi

namespace Construction

/-- The perturbation used to stay inside half-open cells. -/
def eps : ℚ := 1 / 100

/-- Coordinate of the origin point: nudged by `1/10` towards the target cell. -/
def base (A : ℤ) : ℚ := if 0 < A then 3 / 5 else if A < 0 then 2 / 5 else 1 / 2

/-- Coordinate of the target point. -/
def tgt (A : ℤ) : ℚ := if 1 ≤ A then A else if A = 0 then base A else A + 1 - eps

/-- Coordinate of a "far" point of cell `a`, relative to the origin coordinate `base A`. -/
def far (A a : ℤ) : ℚ :=
  if 1 ≤ a then a + 1 - eps else if a ≤ -1 then a else if 0 ≤ A then 0 else 1 - eps

/-- Squared Euclidean distance over `ℚ`. -/
def sqQ (p q : ℚ × ℚ) : ℚ := (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)

/-- The twenty cells of `Answer`, as a list (used for the decidable checks). -/
def answerList : List (ℤ × ℤ) :=
  [(-2, -1), (-2, 0), (-2, 1),
   (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2),
   (0, -2), (0, -1), (0, 1), (0, 2),
   (1, -2), (1, -1), (1, 0), (1, 1), (1, 2),
   (2, -1), (2, 0), (2, 1)]

/-- The integers `-2, …, 2`. -/
def range5 : List ℤ := [-2, -1, 0, 1, 2]

/-- The jitter witnessing that `(A, B)` can be the nearest cell. -/
def jitter (A B : ℤ) (a b : ℤ) : ℝ × ℝ :=
  if a = 0 ∧ b = 0 then ((base A : ℝ), (base B : ℝ))
  else if a = A ∧ b = B then ((tgt A : ℝ), (tgt B : ℝ))
  else ((far A a : ℝ), (far B b : ℝ))

/-! ### The decidable finite checks -/

/-- Inside the `5 × 5` block, every non-origin cell other than the target is at least as far
from the origin point as the target point. -/
theorem finCheck : ∀ c ∈ answerList, ∀ a ∈ range5, ∀ b ∈ range5,
    (a, b) ≠ (0, 0) → (a, b) ≠ c →
    sqQ (tgt c.1, tgt c.2) (base c.1, base c.2) ≤ sqQ (far c.1 a, far c.2 b) (base c.1, base c.2) := by
  decide +kernel

/-- The target point is within squared distance `4` of the origin point. -/
theorem tgt_bound : ∀ a ∈ range5, ∀ b ∈ range5, sqQ (tgt a, tgt b) (base a, base b) ≤ 4 := by
  decide +kernel

theorem mem_range5 {a : ℤ} (h1 : -2 ≤ a) (h2 : a ≤ 2) : a ∈ range5 := by
  interval_cases a <;> decide

theorem mem_answerList {c : ℤ × ℤ} (h : c ∈ Answer) : c ∈ answerList := by
  obtain ⟨A, B⟩ := c
  simp only [Answer, Set.mem_ofPred_eq, abs_le] at h
  obtain ⟨h0, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, h4⟩ := h
  interval_cases A <;> interval_cases B <;>
    first
    | decide
    | exact absurd rfl h0
    | exact absurd (by decide) h4

/-! ### Symbolic facts about the coordinates -/

lemma base_bounds (A : ℤ) : 2 / 5 ≤ base A ∧ base A ≤ 3 / 5 := by
  unfold base; split_ifs <;> norm_num

lemma base_mem (A : ℤ) : 0 ≤ base A ∧ base A < 1 := by
  have := base_bounds A; constructor <;> linarith

lemma tgt_mem (A : ℤ) : (A : ℚ) ≤ tgt A ∧ tgt A < A + 1 := by
  unfold tgt
  split_ifs with h1 h2
  · constructor <;> linarith
  · subst h2; have := base_mem 0; push_cast; constructor <;> linarith
  · unfold eps; constructor <;> linarith

lemma far_mem (A a : ℤ) : (a : ℚ) ≤ far A a ∧ far A a < a + 1 := by
  unfold far eps
  split_ifs with h1 h2 h3
  · constructor <;> linarith
  · constructor <;> linarith
  · have ha : a = 0 := by omega
    subst ha; norm_num
  · have ha : a = 0 := by omega
    subst ha; norm_num

/-- A cell three or more steps away in a coordinate is at squared distance at least `4`. -/
lemma far_big (A a : ℤ) (h : 3 ≤ |a|) : 4 ≤ (far A a - base A) * (far A a - base A) := by
  have hb := base_bounds A
  rw [le_abs] at h
  rcases h with h | h
  · have ha : (3 : ℚ) ≤ a := by exact_mod_cast h
    unfold far eps
    rw [if_pos (by omega)]
    nlinarith
  · have ha : (a : ℚ) ≤ -3 := by exact_mod_cast (by omega : a ≤ -3)
    unfold far
    rw [if_neg (by omega), if_pos (by omega)]
    nlinarith

/-! ### The jitter and its nearest cell -/

theorem jitter_isJitter (A B : ℤ) : IsJitter (jitter A B) := by
  intro a b
  simp only [Set.mem_Ico]
  unfold jitter
  split_ifs with h1 h2 <;> dsimp only
  · obtain ⟨rfl, rfl⟩ := h1
    have hA := base_mem A
    have hB := base_mem B
    push_cast
    exact ⟨⟨by exact_mod_cast hA.1, by exact_mod_cast hA.2⟩,
      ⟨by exact_mod_cast hB.1, by exact_mod_cast hB.2⟩⟩
  · obtain ⟨rfl, rfl⟩ := h2
    have hA := tgt_mem a
    have hB := tgt_mem b
    exact ⟨⟨by exact_mod_cast hA.1, by exact_mod_cast hA.2⟩,
      ⟨by exact_mod_cast hB.1, by exact_mod_cast hB.2⟩⟩
  · have hA := far_mem A a
    have hB := far_mem B b
    exact ⟨⟨by exact_mod_cast hA.1, by exact_mod_cast hA.2⟩,
      ⟨by exact_mod_cast hB.1, by exact_mod_cast hB.2⟩⟩

/-- The rational core of the sufficiency proof. -/
theorem key {A B : ℤ} (h : (A, B) ∈ Answer) {a b : ℤ} (hab : (a, b) ≠ (0, 0))
    (hc : (a, b) ≠ (A, B)) :
    sqQ (tgt A, tgt B) (base A, base B) ≤ sqQ (far A a, far B b) (base A, base B) := by
  by_cases hsmall : -2 ≤ a ∧ a ≤ 2 ∧ -2 ≤ b ∧ b ≤ 2
  · obtain ⟨ha1, ha2, hb1, hb2⟩ := hsmall
    exact finCheck (A, B) (mem_answerList h) a (mem_range5 ha1 ha2) b (mem_range5 hb1 hb2) hab hc
  · have hbox : |A| ≤ 2 ∧ |B| ≤ 2 := ⟨h.2.1, h.2.2.1⟩
    rw [abs_le, abs_le] at hbox
    have hT := tgt_bound A (mem_range5 hbox.1.1 hbox.1.2) B (mem_range5 hbox.2.1 hbox.2.2)
    have h3 : 3 ≤ |a| ∨ 3 ≤ |b| := by
      rw [le_abs, le_abs]; omega
    simp only [sqQ] at hT ⊢
    rcases h3 with h3 | h3
    · have := far_big A a h3
      nlinarith [mul_self_nonneg (far B b - base B)]
    · have := far_big B b h3
      nlinarith [mul_self_nonneg (far A a - base A)]

theorem jitter_isNearest {A B : ℤ} (h : (A, B) ∈ Answer) : IsNearest (jitter A B) A B := by
  have hAB : (A, B) ≠ (0, 0) := h.1
  have hA0 : ¬ (A = 0 ∧ B = 0) := by rintro ⟨rfl, rfl⟩; exact hAB rfl
  refine ⟨hAB, ?_⟩
  intro a b hab
  have hab' : ¬ (a = 0 ∧ b = 0) := by rintro ⟨rfl, rfl⟩; exact hab rfl
  have h00 : jitter A B 0 0 = ((base A : ℝ), (base B : ℝ)) := by
    rw [jitter, if_pos ⟨rfl, rfl⟩]
  have hAB' : jitter A B A B = ((tgt A : ℝ), (tgt B : ℝ)) := by
    rw [jitter, if_neg hA0, if_pos ⟨rfl, rfl⟩]
  rw [h00, hAB']
  by_cases hc : a = A ∧ b = B
  · rw [hc.1, hc.2, hAB']
  · have hfar : jitter A B a b = ((far A a : ℝ), (far B b : ℝ)) := by
      rw [jitter, if_neg hab', if_neg hc]
    rw [hfar]
    have hc' : (a, b) ≠ (A, B) := fun e => hc ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
    have hk := key h hab hc'
    have hk' : ((sqQ (tgt A, tgt B) (base A, base B) : ℚ) : ℝ) ≤
        ((sqQ (far A a, far B b) (base A, base B) : ℚ) : ℝ) := by exact_mod_cast hk
    simp only [sqQ] at hk'
    push_cast at hk'
    simp only [sqDist]
    nlinarith [hk']

end Construction

/-- **Sufficiency.**  Every cell of `Answer` is nearest under some jitter. -/
theorem mem_nearestCells_of_mem_answer {c : ℤ × ℤ} (h : c ∈ Answer) : c ∈ NearestCells := by
  obtain ⟨A, B⟩ := c
  exact ⟨Construction.jitter A B, Construction.jitter_isJitter A B, Construction.jitter_isNearest h⟩

end JitteredVoronoi
