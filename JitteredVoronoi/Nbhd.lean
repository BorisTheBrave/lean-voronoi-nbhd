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

/-- The square containing a point of `[0, 3) × [0, 3)` is in `Nbhd`. -/
theorem floor_mem_Nbhd {u v : ℝ} (hu0 : 0 ≤ u) (hu3 : u < 3) (hv0 : 0 ≤ v) (hv3 : v < 3) :
    (⌊u⌋, ⌊v⌋) ∈ Nbhd := by
  have h1 : 0 ≤ ⌊u⌋ := Int.floor_nonneg.2 hu0
  have h2 : ⌊u⌋ < 3 := Int.floor_lt.2 (by exact_mod_cast hu3)
  have h3 : 0 ≤ ⌊v⌋ := Int.floor_nonneg.2 hv0
  have h4 : ⌊v⌋ < 3 := Int.floor_lt.2 (by exact_mod_cast hv3)
  exact mem_Nbhd_of (by omega) (by omega) (by omega)

/-! ### The neighbourhood as a list -/

/-- The 36 non-origin cells of `Nbhd`, as a list (for decidable checks). -/
def nbhdList : List (ℤ × ℤ) :=
  let r := (List.range 7).map fun n => (n : ℤ) - 3
  (r ×ˢ r).filter fun c => c ≠ (0, 0) ∧ c.1.natAbs + c.2.natAbs ≤ 4

theorem mem_nbhdList {c : ℤ × ℤ} (hc : c ∈ Nbhd) (h0 : c ≠ (0, 0)) : c ∈ nbhdList := by
  obtain ⟨a, b⟩ := c
  have h : a.natAbs ≤ 3 ∧ b.natAbs ≤ 3 ∧ a.natAbs + b.natAbs ≤ 4 := hc
  have ha : -3 ≤ a ∧ a ≤ 3 := by omega
  have hb : -3 ≤ b ∧ b ≤ 3 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> first | decide | (exfalso; revert h h0; decide)

theorem mem_Nbhd_of_mem_nbhdList {c : ℤ × ℤ} (hc : c ∈ nbhdList) : c ∈ Nbhd ∧ c ≠ (0, 0) := by
  have key : ∀ c ∈ nbhdList,
      (c.1.natAbs ≤ 3 ∧ c.2.natAbs ≤ 3 ∧ c.1.natAbs + c.2.natAbs ≤ 4) ∧ c ≠ (0, 0) := by
    decide +kernel
  exact key c hc

theorem mem_nbhdList_iff {c : ℤ × ℤ} : c ∈ nbhdList ↔ c ∈ Nbhd ∧ c ≠ (0, 0) :=
  ⟨mem_Nbhd_of_mem_nbhdList, fun h => mem_nbhdList h.1 h.2⟩

/-- The neighbourhood has 36 cells besides the origin. -/
theorem length_nbhdList : nbhdList.length = 36 := by decide

end JitteredVoronoi
