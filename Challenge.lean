module

public import Mathlib

/-!
# Harris's polarization constant `3√3/4` is attained for a bilinear form on `L^∞(𝕋)`

`𝕋 = AddCircle (2π)` with normalized Haar measure `η`. For `f : 𝕋 → ℂ` put `a_k(f) = f̂(-k) = ∫ f(t) e^{ikt} dη(t)`.
The symmetric bilinear form of S. Loisel's M.Sc. thesis (McGill, 2001, ch. 4) is
`φ(f,g) = a₀(f)a₃(g) - 2a₁(f)a₂(g) - 2a₂(f)a₁(g) + a₃(f)a₀(g)`, with quadratic form `q(f) = φ(f,f)`.

The theorem: on the unit ball of `L^∞(𝕋)`, `sup |φ| = 2` and `sup |q| = 8/(3√3)`, both suprema attained.
Hence `‖φ‖ = (3√3/4) ‖q‖`: L. A. Harris's bound `‖φ‖ ≤ (3√3/4) ‖q‖` for symmetric bilinear forms on
`L^∞` spaces (equivalently, on `C(K)`) is sharp.

Functions in `UnitBall` are a.e.-strongly measurable and bounded by `1` at every point. Every element of the
unit ball of `L^∞(𝕋)` has such a representative, and `a_k` does not depend on the representative.
-/

@[expose] public section

open MeasureTheory

namespace Polarization

/-- The circle `ℝ/2πℤ`. -/
abbrev 𝕋 := AddCircle (2 * Real.pi)

instance twoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- `a_k(f) = f̂(-k) = ∫ f(t) e^{ikt} dη(t)`, with `η` the normalized Haar measure on `𝕋`. -/
noncomputable def a (f : 𝕋 → ℂ) (k : ℕ) : ℂ := fourierCoeff f (-(k : ℤ))

/-- The symmetric bilinear form. -/
noncomputable def φ (f g : 𝕋 → ℂ) : ℂ :=
  a f 0 * a g 3 - 2 * a f 1 * a g 2 - 2 * a f 2 * a g 1 + a f 3 * a g 0

/-- Its quadratic form. -/
noncomputable def q (f : 𝕋 → ℂ) : ℂ := φ f f

/-- The closed unit ball of `L^∞(𝕋)`, as measurable functions bounded by `1` everywhere. -/
def UnitBall : Set (𝕋 → ℂ) := {f | AEStronglyMeasurable f AddCircle.haarAddCircle ∧ ∀ t, ‖f t‖ ≤ 1}

/-- `‖φ‖ = 2` and `‖q‖ = 8/(3√3)` on the unit ball (both attained), hence `‖φ‖ = (3√3/4) ‖q‖`. -/
theorem harris_constant_attained :
    IsGreatest {x : ℝ | ∃ f ∈ UnitBall, ∃ g ∈ UnitBall, x = ‖φ f g‖} 2 ∧
    IsGreatest {x : ℝ | ∃ f ∈ UnitBall, x = ‖q f‖} (8 / (3 * Real.sqrt 3)) := by
  sorry

end Polarization
