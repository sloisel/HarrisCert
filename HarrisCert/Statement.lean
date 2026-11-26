module

public import Mathlib

/-!
# The definitions of `Challenge.lean`, verbatim, for use by `Solution.lean`
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

end Polarization
