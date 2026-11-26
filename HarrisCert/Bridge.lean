module

public import HarrisCert.Defs

/-!
# From `L^∞(𝕋)` to moment vectors

`𝕋 = AddCircle (2π)` with normalized Haar measure `η`. For `f : 𝕋 → ℂ` the moments are
`a_k(f) = f̂(-k) = ∫ f(t) e^{ikt} dη(t)`.
-/

open MeasureTheory Complex

@[expose] public section

namespace Harris

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev 𝕋 := AddCircle (2 * Real.pi)

noncomputable abbrev η : Measure 𝕋 := AddCircle.haarAddCircle

/-- `a_k(f) = f̂(-k)`. -/
noncomputable def mom (f : 𝕋 → ℂ) (k : ℕ) : ℂ := fourierCoeff f (-(k : ℤ))

noncomputable def momV (f : 𝕋 → ℂ) : Fin 4 → ℂ := fun k => mom f k

/-- The unit ball of `L^∞(𝕋)`. -/
def Ball : Set (𝕋 → ℂ) := {f | AEStronglyMeasurable f η ∧ ∀ t, ‖f t‖ ≤ 1}

lemma norm_fourier_apply (n : ℤ) (x : 𝕋) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

lemma fourier_add_arg (n : ℤ) (x y : 𝕋) : fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma fourier_coe_2pi (n : ℤ) (θ : ℝ) : fourier n (θ : 𝕋) = exp ((θ : ℂ) * I) ^ n := by
  rw [fourier_coe_apply, ← Complex.exp_int_mul]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast; field_simp

lemma mom_eq (f : 𝕋 → ℂ) (k : ℕ) : mom f k = ∫ t, fourier (k : ℤ) t * f t ∂η := by
  unfold mom fourierCoeff; simp

lemma Ball.integrable {f : 𝕋 → ℂ} (hf : f ∈ Ball) : Integrable f η :=
  Integrable.mono' (integrable_const (1 : ℝ)) hf.1 (Filter.Eventually.of_forall hf.2)

lemma Ball.integrable_mul {f : 𝕋 → ℂ} (hf : f ∈ Ball) {g : 𝕋 → ℂ} (hg : Continuous g) :
    Integrable (fun t => g t * f t) η := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hg).isBounded.exists_norm_le
  refine Integrable.mono' (integrable_const C) (hg.aestronglyMeasurable.mul hf.1) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_mul]
  calc ‖g t‖ * ‖f t‖ ≤ C * 1 := by
        apply mul_le_mul (hC _ ⟨t, trivial, rfl⟩) (hf.2 t) (norm_nonneg _)
        exact le_trans (norm_nonneg _) (hC _ ⟨t, trivial, rfl⟩)
    _ = C := mul_one C

lemma norm_mom_le {f : 𝕋 → ℂ} (hf : f ∈ Ball) (k : ℕ) : ‖mom f k‖ ≤ 1 := by
  rw [mom_eq]
  calc ‖∫ t, fourier (k : ℤ) t * f t ∂η‖ ≤ ∫ t, ‖fourier (k : ℤ) t * f t‖ ∂η :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _t, (1 : ℝ) ∂η := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const _)
        refine Filter.Eventually.of_forall fun t => ?_
        dsimp only; rw [norm_mul, norm_fourier_apply, one_mul]; exact hf.2 t
    _ = 1 := by simp

/-- `∫ g dη = (1/2π) ∫₀^{2π} g(θ) dθ`. -/
lemma integral_eta (g : 𝕋 → ℝ) :
    ∫ t, g t ∂η = (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
  have h := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 g
  rw [zero_add] at h
  rw [h, AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [ENNReal.toReal_ofReal hpi.le, smul_eq_mul]
  field_simp

/-- The support-function inequality: `Re Σ_k γ_k a_k(f) ≤ N(γ)` for `‖f‖_∞ ≤ 1`. -/
lemma supp_ineq {f : 𝕋 → ℂ} (hf : f ∈ Ball) (γ : Fin 4 → ℂ) :
    (∑ k, γ k * momV f k).re ≤ Nsupp γ := by
  set C : 𝕋 → ℂ := fun t => ∑ k : Fin 4, γ k * fourier ((k : ℕ) : ℤ) t with hC
  have hCc : Continuous C := by rw [hC]; fun_prop
  have hsum : ∑ k, γ k * momV f k = ∫ t, C t * f t ∂η := by
    simp only [momV, mom_eq, hC, Finset.sum_mul]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl; intro k _
      rw [← integral_const_mul]; congr 1; funext t; ring
    · intro k _
      have := Ball.integrable_mul hf (g := fun t => γ k * fourier ((k : ℕ) : ℤ) t) (by fun_prop)
      exact this
  rw [hsum]
  calc (∫ t, C t * f t ∂η).re ≤ ‖∫ t, C t * f t ∂η‖ := Complex.re_le_norm _
    _ ≤ ∫ t, ‖C t * f t‖ ∂η := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖C t‖ ∂η := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hCc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        refine Filter.Eventually.of_forall fun t => ?_
        dsimp only; rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hf.2 t)
    _ = Nsupp γ := by
        rw [integral_eta]
        unfold Nsupp
        congr 1
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [hC, fourier_coe_2pi, zpow_natCast]

end Harris
