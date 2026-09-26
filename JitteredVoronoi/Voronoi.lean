import JitteredVoronoi.Sufficiency
import JitteredVoronoi.Witness

/-!
# Jittered Voronoi diagrams: which neighbourhood determines the origin's cell?

A *jitter* `f : ℤ × ℤ → ℝ × ℝ` puts one point in every unit cell `[a, a+1) × [b, b+1)`.  The
Voronoi cell of the site `f x` is the set of points of the plane at least as close to `f x` as
to every other site.  Computing it from a neighbourhood `N` of cells only (ignoring the sites
outside `N`) gives a possibly larger set `voronoiOn f N x`.

**Main theorem** (`sufficientNbhd_iff`, `nbhd_isLeast`): the local computation is exact for the origin
cell and *every* jitter if and only if `N` contains the 36 cells
`{(a, b) ≠ (0, 0) | |a| ≤ 3, |b| ≤ 3, |a| + |b| ≤ 4}` — the `7 × 7` block minus the three cells
at each corner.  In particular the `5 × 5` block is not enough (the cell `(3, 0)` can be a
Voronoi neighbour of the origin's point), and the `7 × 7` block is more than needed.
-/

namespace JitteredVoronoi

/-! ### The characterisation -/

/-- `N` is a sufficient neighbourhood
 if computing voronoi on N gives the same result for the origin's cell as computing voronoi on the full plane-/
def SufficientNbhd (N : Set (ℤ × ℤ)) : Prop :=
  ∀ f : ℤ × ℤ → ℝ × ℝ, IsJitter f → voronoiOn f N (0, 0) = voronoi f (0, 0)

/-- A sufficient neighbourhood contains the origin cell: otherwise the local Voronoi cell is
empty while the true one contains the origin's site. -/
theorem origin_mem_of_sufficientNbhd {N : Set (ℤ × ℤ)} (h : SufficientNbhd N) : (0, 0) ∈ N := by
  by_contra h0
  -- any jitter will do, e.g. the one placing every site at the corner of its cell
  have hf : IsJitter fun c : ℤ × ℤ => ((c.1 : ℝ), (c.2 : ℝ)) :=
    IsJitterIco.isJitter fun c => ⟨⟨le_refl _, by linarith⟩, ⟨le_refl _, by linarith⟩⟩
  have := voronoi_nonempty (fun c : ℤ × ℤ => ((c.1 : ℝ), (c.2 : ℝ))) (0, 0)
  rw [← h _ hf, voronoiOn_eq_empty _ h0] at this
  exact Set.not_nonempty_empty this

/-- `N` is a sufficient neighbourhood if and only if it contains `Nbhd`. -/
theorem sufficientNbhd_iff (N : Set (ℤ × ℤ)) : SufficientNbhd N ↔ Nbhd ⊆ N := by
  constructor
  · intro h c hc
    have h0N := origin_mem_of_sufficientNbhd h
    by_cases h0 : c = (0, 0)
    · exact h0 ▸ h0N
    by_contra hcN
    obtain ⟨f, hf, p, hp1, hp2⟩ := exists_jitter_voronoiOn_ne hc h0
    apply hp2
    rw [← h f hf]
    exact voronoiOn_anti f (fun d hd => (show d ≠ c from fun e => hcN (e ▸ hd))) h0N hp1
  · intro hN f hf
    exact voronoiOn_eq_voronoi_of_subset hN hf

/-- *Main Theorem*
`Nbhd` is the least sufficient neighbourhood.
-/
theorem nbhd_isLeast : IsLeast {N | SufficientNbhd N} Nbhd :=
  ⟨(sufficientNbhd_iff Nbhd).2 le_rfl, fun _ hN => (sufficientNbhd_iff _).1 hN⟩


/-! ### Concrete consequences -/

/-- The `5 × 5` block is not enough: the cell `(3, 0)` is needed. -/
theorem three_zero_needed :
    ∃ f : ℤ × ℤ → ℝ × ℝ, IsJitter f ∧
      ∃ p, p ∈ voronoiOn f {(3, 0)}ᶜ (0, 0) ∧ p ∉ voronoi f (0, 0) :=
  exists_jitter_voronoiOn_ne (mem_Nbhd_of (by decide) (by decide) (by decide)) (by decide)

/-- The `7 × 7` block is more than needed: the cell `(3, 2)` never matters. -/
theorem three_two_not_needed {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) :
    voronoiOn f {(3, 2)}ᶜ (0, 0) = voronoi f (0, 0) :=
  voronoiOn_eq_voronoi_of_subset (fun c hc => by
    have h : c.1.natAbs ≤ 3 ∧ c.2.natAbs ≤ 3 ∧ c.1.natAbs + c.2.natAbs ≤ 4 := hc
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp at h) hf

end JitteredVoronoi
