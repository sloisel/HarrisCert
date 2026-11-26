module

public import HarrisCert.Local14

/-!
# The main theorem

On the unit ball of `L^∞(𝕋)`, with `a_k(f) = f̂(-k)`, `φ(f, g) = a₀b₃ - 2a₁b₂ - 2a₂b₁ + a₃b₀` and `q(f) = φ(f, f)`:
`sup |φ| = 2` and `sup |q| = 8/(3√3)`, both attained. Hence `‖φ‖ = (3√3/4) ‖q‖`, and Harris's constant `3√3/4`
for the polarization of bilinear forms on `L^∞(𝕋)` is sharp.
-/

@[expose] public section

namespace Harris

theorem harris_main :
    IsGreatest {x : ℝ | ∃ f ∈ Ball, ∃ g ∈ Ball, x = ‖phiB (momV f) (momV g)‖} 2 ∧
    IsGreatest {x : ℝ | ∃ f ∈ Ball, x = ‖qform (momV f)‖} (8 / (3 * Real.sqrt 3)) :=
  main_of_local localThm

end Harris
