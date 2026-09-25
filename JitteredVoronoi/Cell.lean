import Mathlib

/-!
# One-dimensional cell conventions

A jittered grid puts one point in each unit cell.  Whether a cell is `[a, a+1)`, `(a, a+1]` or
something in between matters at the boundary, and reflecting the plane swaps the conventions.  To
be able to use the symmetries of the square we work with an abstract *cell structure*: a family
of sets `I a ⊆ [a, a+1]` such that any two distinct cells are separated in the sense
`x' - x > a' - a - 1` for `x ∈ I a`, `x' ∈ I a'`, `a < a'`.  For adjacent cells this says
`x < x'`; more generally it says that the two touching endpoints of consecutive cells never both
belong to their cells.  Both half-open conventions satisfy this, and the axioms are stable under
the reflection `x ↦ 1 - x`.
-/

namespace JitteredVoronoi

/-- A convention for the unit cells of `ℝ`; see the module docstring. -/
structure CellStructure where
  /-- The cell with index `a`. -/
  I : ℤ → Set ℝ
  le_of_mem : ∀ a : ℤ, ∀ x ∈ I a, (a : ℝ) ≤ x ∧ x ≤ a + 1
  sep : ∀ a a' : ℤ, a < a' → ∀ x ∈ I a, ∀ x' ∈ I a', ((a' : ℝ) - a - 1) < x' - x

namespace CellStructure

variable (C : CellStructure)

/-- The half-open convention `[a, a+1)` used for jittered grids. -/
def ico : CellStructure where
  I a := Set.Ico (a : ℝ) (a + 1)
  le_of_mem _ _ hx := ⟨hx.1, hx.2.le⟩
  sep a a' h x hx x' hx' := by
    have : (a : ℝ) + 1 ≤ a' := by exact_mod_cast h
    obtain ⟨_, h2⟩ := hx
    obtain ⟨h3, _⟩ := hx'
    linarith

@[simp] theorem mem_ico_iff {a : ℤ} {x : ℝ} : x ∈ ico.I a ↔ (a : ℝ) ≤ x ∧ x < a + 1 := Iff.rfl

/-- The reflected convention: cell `a` of `C.reflect` is the mirror image under `x ↦ 1 - x` of
cell `-a` of `C`. -/
def reflect : CellStructure where
  I a := {x | 1 - x ∈ C.I (-a)}
  le_of_mem a x hx := by
    have := C.le_of_mem (-a) (1 - x) hx
    push_cast at this
    constructor <;> linarith
  sep a a' h x hx x' hx' := by
    have := C.sep (-a') (-a) (by omega) (1 - x') hx' (1 - x) hx
    push_cast at this
    linarith

theorem mem_reflect_iff {a : ℤ} {x : ℝ} : x ∈ C.reflect.I a ↔ 1 - x ∈ C.I (-a) := Iff.rfl

theorem mem_reflect_of_mem {a : ℤ} {x : ℝ} (hx : x ∈ C.I a) : 1 - x ∈ C.reflect.I (-a) := by
  rw [mem_reflect_iff, neg_neg, sub_sub_cancel]
  exact hx

theorem mem_reflect_zero {x : ℝ} (hx : x ∈ C.I 0) : 1 - x ∈ C.reflect.I 0 := by
  simpa using C.mem_reflect_of_mem hx

/-- Points of distinct cells are ordered like the cells. -/
theorem lt_of_mem {a a' : ℤ} (h : a < a') {x x' : ℝ} (hx : x ∈ C.I a) (hx' : x' ∈ C.I a') :
    x < x' := by
  have h1 := C.sep a a' h x hx x' hx'
  have h2 : (a : ℝ) + 1 ≤ a' := by exact_mod_cast h
  linarith

end CellStructure

end JitteredVoronoi
