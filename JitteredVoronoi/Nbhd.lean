import Mathlib

/-!
# The neighbourhood

`Nbhd` is the set of cells `(a, b)` with `|a| ≤ 3`, `|b| ≤ 3` and `|a| + |b| ≤ 4`: the `7 × 7`
block around the origin with the three cells at each corner removed.  It has 37 cells including
the origin.  It is written with `Int.natAbs` so that `omega` can reason about it directly.
-/

namespace JitteredVoronoi

/-- The neighbourhood of the origin cell: `|a| ≤ 3`, `|b| ≤ 3`, `|a| + |b| ≤ 4`. -/
def Nbhd : Set (ℤ × ℤ) :=
  {c | c.1.natAbs ≤ 3 ∧ c.2.natAbs ≤ 3 ∧ c.1.natAbs + c.2.natAbs ≤ 4}

theorem mem_Nbhd_iff {a b : ℤ} : (a, b) ∈ Nbhd ↔ a.natAbs ≤ 3 ∧ b.natAbs ≤ 3 ∧ a.natAbs + b.natAbs ≤ 4 :=
  Iff.rfl

/-- The same set written with `|·|`. -/
theorem mem_Nbhd_iff_abs {a b : ℤ} : (a, b) ∈ Nbhd ↔ |a| ≤ 3 ∧ |b| ≤ 3 ∧ |a| + |b| ≤ 4 := by
  rw [mem_Nbhd_iff, ← Int.natCast_natAbs, ← Int.natCast_natAbs]
  omega

theorem mem_Nbhd_of {a b : ℤ} (h1 : a.natAbs ≤ 3) (h2 : b.natAbs ≤ 3) (h3 : a.natAbs + b.natAbs ≤ 4) :
    (a, b) ∈ Nbhd := ⟨h1, h2, h3⟩

theorem mem_Nbhd_neg_fst {a b : ℤ} : (-a, b) ∈ Nbhd ↔ (a, b) ∈ Nbhd := by
  simp only [mem_Nbhd_iff, Int.natAbs_neg]

theorem mem_Nbhd_neg_snd {a b : ℤ} : (a, -b) ∈ Nbhd ↔ (a, b) ∈ Nbhd := by
  simp only [mem_Nbhd_iff, Int.natAbs_neg]

theorem mem_Nbhd_swap {a b : ℤ} : (b, a) ∈ Nbhd ↔ (a, b) ∈ Nbhd := by
  simp only [mem_Nbhd_iff]
  omega

theorem origin_mem_Nbhd : ((0 : ℤ), (0 : ℤ)) ∈ Nbhd := mem_Nbhd_of (by decide) (by decide) (by decide)

end JitteredVoronoi
