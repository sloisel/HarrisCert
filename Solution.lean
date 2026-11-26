module

public import HarrisCert.Statement
public import HarrisCert.Main

/-!
# Proof of `Polarization.harris_constant_attained`

The statement of `Challenge.lean` is reduced to `Harris.harris_main`, which works with the same objects
under other names: `Harris.Ball = Polarization.UnitBall`, `Harris.momV f k = a_k(f)`,
`Harris.phiB (momV f) (momV g) = φ f g`, `Harris.qform (momV f) = q f`.
-/

@[expose] public section

namespace Polarization

lemma unitBall_eq : UnitBall = Harris.Ball := rfl

lemma φ_eq (f g : 𝕋 → ℂ) : φ f g = Harris.phiB (Harris.momV f) (Harris.momV g) := rfl

lemma q_eq (f : 𝕋 → ℂ) : q f = Harris.qform (Harris.momV f) := by
  rw [q, φ_eq, Harris.phiB, Harris.qform]; ring

theorem harris_constant_attained :
    IsGreatest {x : ℝ | ∃ f ∈ UnitBall, ∃ g ∈ UnitBall, x = ‖φ f g‖} 2 ∧
    IsGreatest {x : ℝ | ∃ f ∈ UnitBall, x = ‖q f‖} (8 / (3 * Real.sqrt 3)) := by
  simp only [unitBall_eq, φ_eq, q_eq]
  exact Harris.harris_main

end Polarization
