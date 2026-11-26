module

public import HarrisCert.Q3
public import HarrisCert.Core.Check

/-!
# The statement of the global step

Coordinates: `x : Fin 7 → ℝ` and the moment vector
`a = (x₀ + i x₁, x₂, x₃ + i x₄, x₅ + i x₆) = (ĥ(0), ĥ(-1), ĥ(-2), ĥ(-3))`, with `a₁` real
(the rotation normalization of Lemma 10 in `harris_sharp.tex`).

* `q(a) = 2 a₀ a₃ - 4 a₁ a₂` and `φ(a,b) = aᵀ B b` with `B = antidiag(1,-2,-2,1)`;
* the orbit point for `u = e^{iα/2}` is `a(h_α) = (0, r u, (2/3) ū, -(2r/3) ū³)` with `r = 1/√3`;
  the reflected point is `a(R h_α)_k = conj (a(h_α)_{3-k})`;
* `N(γ) = ∫_𝕋 |Σ γ_k z^k| dη` is the support function of the moment body.
-/

open Complex

@[expose] public section

namespace Harris

noncomputable def r : ℝ := Real.sqrt 3 / 3
noncomputable def M : ℝ := 8 * Real.sqrt 3 / 9

/-- The moment vector of `x`. -/
noncomputable def amom (x : Fin 7 → ℝ) : Fin 4 → ℂ :=
  ![⟨x 0, x 1⟩, ⟨x 2, 0⟩, ⟨x 3, x 4⟩, ⟨x 5, x 6⟩]

/-- `q(a) = φ(a,a)`. -/
noncomputable def qform (a : Fin 4 → ℂ) : ℂ := 2 * a 0 * a 3 - 4 * a 1 * a 2

/-- `φ(a,b) = aᵀ B b`. -/
noncomputable def phiB (a b : Fin 4 → ℂ) : ℂ :=
  a 0 * b 3 - 2 * a 1 * b 2 - 2 * a 2 * b 1 + a 3 * b 0

/-- Moments of `h_α`, in terms of `u = e^{iα/2}`. -/
noncomputable def aorb (u : ℂ) : Fin 4 → ℂ :=
  ![0, (r : ℂ) * u, (2 / 3 : ℂ) * (starRingEnd ℂ) u, -(2 * r / 3 : ℂ) * (starRingEnd ℂ) u ^ 3]

/-- Moments of `R g` from those of `g`. -/
noncomputable def refl (b : Fin 4 → ℂ) : Fin 4 → ℂ := fun k => (starRingEnd ℂ) (b (Fin.rev k))

/-- `X(a, b) = M + Re φ(a, b)`. -/
noncomputable def Xslab (a b : Fin 4 → ℂ) : ℝ := M + (phiB a b).re

/-- `N(γ) = (1/2π) ∫₀^{2π} |Σ_k γ_k (e^{iθ})^k| dθ`. -/
noncomputable def Nsupp (γ : Fin 4 → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖∑ k : Fin 4, γ k * exp ((θ : ℂ) * I) ^ (k : ℕ)‖


def InBox (lo hi : Fin 7 → ℚ) (x : Fin 7 → ℝ) : Prop := ∀ j, (lo j : ℝ) ≤ x j ∧ x j ≤ hi j

/-- The hypotheses on a point `x` that is not covered by the local theorem (after normalization). -/
structure Hyps (x : Fin 7 → ℝ) : Prop where
  box : InBox rootLo rootHi x
  supp : ∀ γ : Fin 4 → ℂ, (∑ k, γ k * amom x k).re ≤ Nsupp γ
  slab : ∀ u : ℂ, ‖u‖ = 1 →
    (X0 : ℝ) ≤ Xslab (amom x) (aorb u) ∧ (X0 : ℝ) ≤ Xslab (amom x) (refl (aorb u))

/-- The conclusion: `Re q(a) ≥ -M`, i.e. `f ≤ M` with `f = -Re q`. -/
def Goal (x : Fin 7 → ℝ) : Prop := -M ≤ (qform (amom x)).re

end Harris
