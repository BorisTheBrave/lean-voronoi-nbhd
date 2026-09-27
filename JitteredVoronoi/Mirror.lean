import JitteredVoronoi.Basic
import JitteredVoronoi.Nbhd

/-!
# Symmetries of jittered grids

The mirror `m x = 1 - x` swaps the two ends of the unit interval and sends the cell `[a, a+1]` to
the cell `[-a, -a+1]`.  Reflecting a jitter in the line `x = 1/2` (or `y = 1/2`), or swapping
the two axes, gives another jitter, and the Voronoi cell of the origin's site is carried along.
These facts let the main proof assume, without loss of generality, that the test point lies in
the quadrant `u, v ≥ 1/2` and that the cell under consideration satisfies `b ≤ a`.
-/

namespace JitteredVoronoi

/-- The mirror `x ↦ 1 - x` of the unit interval. -/
abbrev m (x : ℝ) : ℝ := 1 - x

@[simp] theorem m_m (x : ℝ) : m (m x) = x := by simp [m]

/-! ### Mirror images of points -/

/-- Reflection of a point in the line `x = 1/2`. -/
def mx (p : ℝ × ℝ) : ℝ × ℝ := (m p.1, p.2)

/-- Reflection of a point in the line `y = 1/2`: swap, reflect in `x = 1/2`, swap back. -/
def my (p : ℝ × ℝ) : ℝ × ℝ := (mx p.swap).swap

@[simp] theorem mx_fst (p : ℝ × ℝ) : (mx p).1 = m p.1 := rfl
@[simp] theorem mx_snd (p : ℝ × ℝ) : (mx p).2 = p.2 := rfl
@[simp] theorem my_fst (p : ℝ × ℝ) : (my p).1 = p.1 := rfl
@[simp] theorem my_snd (p : ℝ × ℝ) : (my p).2 = m p.2 := rfl

@[simp] theorem mx_mx (p : ℝ × ℝ) : mx (mx p) = p := by simp [mx]
@[simp] theorem my_my (p : ℝ × ℝ) : my (my p) = p := by simp [my]

@[simp] theorem sqDist_mx (p q : ℝ × ℝ) : sqDist (mx p) (mx q) = sqDist p q := by
  simp only [sqDist, mx, m]; ring

@[simp] theorem sqDist_swap (p q : ℝ × ℝ) : sqDist p.swap q.swap = sqDist p q := by
  simp only [sqDist, Prod.swap]; ring

@[simp] theorem sqDist_my (p q : ℝ × ℝ) : sqDist (my p) (my q) = sqDist p q := by
  simp only [my, sqDist_swap, sqDist_mx]

/-! ### Mirror images of jitters -/

/-- The jitter reflected in the line `x = 1/2`: the site of the cell `(a, b)` is the mirror
image of the site of the cell `(-a, b)`. -/
def mirrorX (f : ℤ × ℤ → ℝ × ℝ) (c : ℤ × ℤ) : ℝ × ℝ := mx (f (-c.1, c.2))

/-- The jitter with the two axes swapped. -/
def swapXY (f : ℤ × ℤ → ℝ × ℝ) (c : ℤ × ℤ) : ℝ × ℝ := (f c.swap).swap

/-- The jitter reflected in the line `y = 1/2`: swap the axes, reflect in `x = 1/2`, swap back. -/
def mirrorY (f : ℤ × ℤ → ℝ × ℝ) : ℤ × ℤ → ℝ × ℝ := swapXY (mirrorX (swapXY f))

theorem mirrorY_apply (f : ℤ × ℤ → ℝ × ℝ) (c : ℤ × ℤ) : mirrorY f c = my (f (c.1, -c.2)) := rfl

theorem mirrorX_mirrorX (f : ℤ × ℤ → ℝ × ℝ) : mirrorX (mirrorX f) = f := by
  funext c; simp [mirrorX]

theorem swapXY_swapXY (f : ℤ × ℤ → ℝ × ℝ) : swapXY (swapXY f) = f := by
  funext c; simp [swapXY]

theorem mirrorY_mirrorY (f : ℤ × ℤ → ℝ × ℝ) : mirrorY (mirrorY f) = f := by
  simp only [mirrorY, swapXY_swapXY, mirrorX_mirrorX]

theorem IsJitter.mirrorX {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) : IsJitter (mirrorX f) where
  mem c := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hf.mem (-c.1, c.2)
    push_cast at h1 h2
    refine ⟨Set.mem_Icc.2 ⟨?_, ?_⟩, h3⟩
    · show (c.1 : ℝ) ≤ 1 - (f (-c.1, c.2)).1
      linarith
    · show 1 - (f (-c.1, c.2)).1 ≤ c.1 + 1
      linarith
  injective c d h := by
    have h' : mx (mx (f (-c.1, c.2))) = mx (mx (f (-d.1, d.2))) := congrArg mx h
    rw [mx_mx, mx_mx] at h'
    have := hf.injective h'
    simp only [Prod.mk.injEq, neg_inj] at this
    exact Prod.ext this.1 this.2

theorem IsJitter.swapXY {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) : IsJitter (swapXY f) where
  mem c := by
    obtain ⟨h1, h2⟩ := hf.mem c.swap
    exact ⟨h2, h1⟩
  injective c d h :=
    Prod.swap_injective
      (hf.injective (Prod.swap_injective (show (f c.swap).swap = (f d.swap).swap from h)))

theorem IsJitter.mirrorY {f : ℤ × ℤ → ℝ × ℝ} (hf : IsJitter f) : IsJitter (mirrorY f) :=
  hf.swapXY.mirrorX.swapXY

/-! ### Transport of Voronoi cells -/

/-- If `N` is symmetric under `(a, b) ↦ (-a, b)`, the local Voronoi cell is carried along by the
reflection. -/
theorem mem_voronoiOn_mirrorX {f : ℤ × ℤ → ℝ × ℝ} {N : Set (ℤ × ℤ)}
    (hN : ∀ c ∈ N, (-c.1, c.2) ∈ N) {p : ℝ × ℝ} (hp : p ∈ voronoiOn f N (0, 0)) :
    mx p ∈ voronoiOn (mirrorX f) N (0, 0) := by
  refine ⟨hp.1, fun y hy => ?_⟩
  have := hp.2 (-y.1, y.2) (hN y hy)
  simpa [mirrorX] using this

theorem mem_voronoiOn_swapXY {f : ℤ × ℤ → ℝ × ℝ} {N : Set (ℤ × ℤ)}
    (hN : ∀ c ∈ N, c.swap ∈ N) {p : ℝ × ℝ} (hp : p ∈ voronoiOn f N (0, 0)) :
    p.swap ∈ voronoiOn (swapXY f) N (0, 0) := by
  refine ⟨hp.1, fun y hy => ?_⟩
  have := hp.2 y.swap (hN y hy)
  simpa [swapXY] using this

/-- If `N` is symmetric under the swap and under `(a, b) ↦ (-a, b)`, the local Voronoi cell is
carried along by the reflection in `y = 1/2`. -/
theorem mem_voronoiOn_mirrorY {f : ℤ × ℤ → ℝ × ℝ} {N : Set (ℤ × ℤ)}
    (hNs : ∀ c ∈ N, c.swap ∈ N) (hNx : ∀ c ∈ N, (-c.1, c.2) ∈ N) {p : ℝ × ℝ}
    (hp : p ∈ voronoiOn f N (0, 0)) : my p ∈ voronoiOn (mirrorY f) N (0, 0) :=
  mem_voronoiOn_swapXY hNs (mem_voronoiOn_mirrorX hNx (mem_voronoiOn_swapXY hNs hp))

theorem Nbhd_mirrorX : ∀ c ∈ Nbhd, (-c.1, c.2) ∈ Nbhd := fun _ hc => mem_Nbhd_neg_fst.2 hc
theorem Nbhd_swap : ∀ c ∈ Nbhd, c.swap ∈ Nbhd := fun _ hc => mem_Nbhd_swap.2 hc

end JitteredVoronoi
