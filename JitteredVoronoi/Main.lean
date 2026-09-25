import JitteredVoronoi.Necessity
import JitteredVoronoi.Construction

/-!
# Main theorem

`NearestCells = Answer`: over all jitters, the cells that can hold the nearest neighbour of the
origin cell's point are exactly the `5 × 5` block around the origin with the origin and the four
corners removed.  Twenty cells.

We also record the concrete finite description, the comparison with the `3 × 3` and `5 × 5`
blocks, and the fact that nothing changes if the squared distance is replaced by the genuine
Euclidean distance on `EuclideanSpace ℝ (Fin 2)`.
-/

namespace JitteredVoronoi

/-- **Main theorem.** -/
theorem nearestCells_eq_answer : NearestCells = Answer := by
  ext c
  obtain ⟨A, B⟩ := c
  constructor
  · rintro ⟨f, hf, hN⟩
    exact mem_answer_of_isNearest hf hN
  · exact mem_nearestCells_of_mem_answer

theorem mem_nearestCells_iff {A B : ℤ} :
    (A, B) ∈ NearestCells ↔ (A, B) ≠ (0, 0) ∧ |A| ≤ 2 ∧ |B| ≤ 2 ∧ ¬ (|A| = 2 ∧ |B| = 2) := by
  rw [nearestCells_eq_answer]; rfl

/-! ### Concrete finite descriptions -/

/-- `Answer` as an explicit list of twenty cells. -/
theorem answer_eq_list : Answer = {c | c ∈ Construction.answerList} := by
  ext c
  constructor
  · exact Construction.mem_answerList
  · intro h
    have key : ∀ c ∈ Construction.answerList,
        c ≠ (0, 0) ∧ |c.1| ≤ 2 ∧ |c.2| ≤ 2 ∧ ¬ (|c.1| = 2 ∧ |c.2| = 2) := by
      decide +kernel
    exact key c h

/-- `Answer` as a `Finset`. -/
theorem answer_eq_finset : Answer = ↑Construction.answerList.toFinset := by
  rw [answer_eq_list]; ext c; simp

/-- There are exactly twenty possible nearest cells. -/
theorem card_answer : Construction.answerList.toFinset.card = 20 := by decide +kernel

theorem nearestCells_eq_finset : NearestCells = ↑Construction.answerList.toFinset :=
  nearestCells_eq_answer.trans answer_eq_finset

/-! ### Comparison with the `3 × 3` and `5 × 5` blocks -/

/-- Every non-origin cell of the `3 × 3` block can be nearest. -/
theorem threeBox_subset {A B : ℤ} (h0 : (A, B) ≠ (0, 0)) (hA : |A| ≤ 1) (hB : |B| ≤ 1) :
    (A, B) ∈ NearestCells := by
  rw [mem_nearestCells_iff]
  refine ⟨h0, by omega, by omega, ?_⟩
  rintro ⟨h, -⟩; omega

/-- The nearest cell always lies in the `5 × 5` block. -/
theorem subset_fiveBox {A B : ℤ} (h : (A, B) ∈ NearestCells) : |A| ≤ 2 ∧ |B| ≤ 2 := by
  rw [mem_nearestCells_iff] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-- The `3 × 3` block is not enough: the cell `(2, 1)` can be nearest. -/
theorem two_one_mem : (2, 1) ∈ NearestCells := by
  rw [mem_nearestCells_iff]; decide

/-- The full `5 × 5` block is more than needed: the corner `(2, 2)` is never nearest. -/
theorem two_two_not_mem : (2, 2) ∉ NearestCells := by
  rw [mem_nearestCells_iff]; decide

/-! ### Euclidean distance instead of squared distance -/

/-- Embed `ℝ × ℝ` into the Euclidean plane. -/
def toE (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![p.1, p.2]

lemma dist_toE (p q : ℝ × ℝ) : dist (toE p) (toE q) = Real.sqrt (sqDist p q) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [toE, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.dist_eq, sq_abs, sqDist]

/-- `IsNearest`, phrased with the Euclidean distance `‖f A B - f 0 0‖`. -/
def IsNearestDist (f : ℤ → ℤ → ℝ × ℝ) (A B : ℤ) : Prop :=
  (A, B) ≠ (0, 0) ∧
    ∀ a b : ℤ, (a, b) ≠ (0, 0) → dist (toE (f A B)) (toE (f 0 0)) ≤ dist (toE (f a b)) (toE (f 0 0))

theorem isNearestDist_iff (f : ℤ → ℤ → ℝ × ℝ) (A B : ℤ) :
    IsNearestDist f A B ↔ IsNearest f A B := by
  unfold IsNearestDist IsNearest
  simp only [dist_toE]
  refine and_congr_right fun _ => ?_
  refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_
  exact Real.sqrt_le_sqrt_iff (sqDist_nonneg _ _)

/-- The main theorem, stated with the Euclidean distance. -/
theorem nearestCells_dist_eq_answer :
    {c : ℤ × ℤ | ∃ f, IsJitter f ∧ IsNearestDist f c.1 c.2} = Answer := by
  rw [← nearestCells_eq_answer]
  ext c
  simp only [Set.mem_ofPred_eq, NearestCells, isNearestDist_iff]

end JitteredVoronoi
