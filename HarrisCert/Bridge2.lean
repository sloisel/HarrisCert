module

public import HarrisCert.Bridge

/-!
# Symmetries, Bessel's inequality, and the extremal functions
-/

open MeasureTheory Complex

@[expose] public section

namespace Harris

/-! ## Rotation `U_β f (t) = e^{3iβ/2} f(t + β)` -/

noncomputable def rot (β : ℝ) (f : 𝕋 → ℂ) : 𝕋 → ℂ :=
  fun t => exp (((3 * β / 2 : ℝ) : ℂ) * I) * f (t + (β : 𝕋))

lemma norm_exp_real_mul_I (x : ℝ) : ‖exp ((x : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x

lemma rot_mem {f : 𝕋 → ℂ} (hf : f ∈ Ball) (β : ℝ) : rot β f ∈ Ball := by
  refine ⟨?_, fun t => ?_⟩
  · have hmp : MeasurePreserving (fun t : 𝕋 => t + (β : 𝕋)) η η := measurePreserving_add_right _ _
    exact aestronglyMeasurable_const.mul (hf.1.comp_measurePreserving hmp)
  · simp only [rot, norm_mul, norm_exp_real_mul_I, one_mul]; exact hf.2 _

lemma mom_rot (f : 𝕋 → ℂ) (β : ℝ) (k : ℕ) :
    mom (rot β f) k = exp (((3 * β / 2 : ℝ) : ℂ) * I) * exp (-((β : ℂ) * I)) ^ k * mom f k := by
  rw [mom_eq, mom_eq]
  set c := exp (((3 * β / 2 : ℝ) : ℂ) * I)
  have hshift : ∀ t : 𝕋, fourier (k : ℤ) t = fourier (k : ℤ) (t + (β : 𝕋)) * fourier (k : ℤ) (-(β : 𝕋)) := by
    intro t; rw [← fourier_add_arg]; congr 1; abel
  have hfb : fourier (k : ℤ) (-(β : 𝕋)) = exp (-((β : ℂ) * I)) ^ k := by
    rw [← AddCircle.coe_neg, fourier_coe_2pi]; push_cast; rw [zpow_natCast]; congr 1; ring_nf
  have key : ∫ t, fourier (k : ℤ) t * f (t + (β : 𝕋)) ∂η =
      fourier (k : ℤ) (-(β : 𝕋)) * ∫ t, fourier (k : ℤ) t * f t ∂η := by
    rw [← integral_const_mul]
    have := integral_add_right_eq_self (μ := η)
      (fun s => fourier (k : ℤ) (-(β : 𝕋)) * (fourier (k : ℤ) s * f s)) (β : 𝕋)
    rw [← this]; congr 1; funext t; rw [hshift t]; ring
  simp only [rot]
  have : ∫ t, fourier (k : ℤ) t * (c * f (t + (β : 𝕋))) ∂η = c * ∫ t, fourier (k : ℤ) t * f (t + (β : 𝕋)) ∂η := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [this, key, hfb]; ring

/-! ## Reflection `R f = z̄³ f̄` -/

noncomputable def reflF (f : 𝕋 → ℂ) : 𝕋 → ℂ := fun t => fourier (-3) t * (starRingEnd ℂ) (f t)

lemma reflF_mem {f : 𝕋 → ℂ} (hf : f ∈ Ball) : reflF f ∈ Ball := by
  refine ⟨?_, fun t => ?_⟩
  · exact (fourier (-3)).continuous.aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hf.1)
  · simp only [reflF, norm_mul, norm_fourier_apply, one_mul, RCLike.norm_conj]; exact hf.2 t

lemma mom_reflF (f : 𝕋 → ℂ) (k : ℕ) (hk : k ≤ 3) :
    mom (reflF f) k = (starRingEnd ℂ) (mom f (3 - k)) := by
  rw [mom_eq, mom_eq, ← integral_conj]
  congr 1; funext t
  simp only [reflF, map_mul]
  have : fourier (k : ℤ) t * fourier (-3) t = (starRingEnd ℂ) (fourier (((3 - k : ℕ) : ℤ)) t) := by
    rw [← fourier_add, ← fourier_neg]; congr 1; push_cast [Nat.cast_sub hk]; ring
  rw [← mul_assoc, this]

/-! ## Moments of a multiple, and the forms -/

lemma mom_smul (c : ℂ) (f : 𝕋 → ℂ) (k : ℕ) : mom (fun t => c * f t) k = c * mom f k := by
  rw [mom_eq, mom_eq, ← integral_const_mul]; congr 1; funext t; ring

lemma smul_mem {f : 𝕋 → ℂ} (hf : f ∈ Ball) {c : ℂ} (hc : ‖c‖ = 1) : (fun t => c * f t) ∈ Ball :=
  ⟨aestronglyMeasurable_const.mul hf.1, fun t => by rw [norm_mul, hc, one_mul]; exact hf.2 t⟩

/-! ## Bessel's inequality for the four moments -/

lemma Ball.memLp {f : 𝕋 → ℂ} (hf : f ∈ Ball) : MemLp f 2 η :=
  MemLp.of_bound hf.1 1 (Filter.Eventually.of_forall hf.2)

lemma bessel {f : 𝕋 → ℂ} (hf : f ∈ Ball) :
    ‖mom f 0‖ ^ 2 + ‖mom f 1‖ ^ 2 + ‖mom f 2‖ ^ 2 + ‖mom f 3‖ ^ 2 ≤ 1 := by
  set F := (Ball.memLp hf).toLp f
  have hcoef : ∀ n : ℤ, fourierCoeff (⇑F) n = fourierCoeff f n := by
    intro n; unfold fourierCoeff
    apply integral_congr_ae
    filter_upwards [(Ball.memLp hf).coeFn_toLp] with t ht
    rw [ht]
  have hsum := hasSum_sq_fourierCoeff F
  have hint : ∫ t, ‖(F : 𝕋 → ℂ) t‖ ^ 2 ∂η ≤ 1 := by
    have : ∫ t, ‖(F : 𝕋 → ℂ) t‖ ^ 2 ∂η = ∫ t, ‖f t‖ ^ 2 ∂η := by
      apply integral_congr_ae
      filter_upwards [(Ball.memLp hf).coeFn_toLp] with t ht
      rw [ht]
    rw [this]
    calc ∫ t, ‖f t‖ ^ 2 ∂η ≤ ∫ _t, (1 : ℝ) ∂η := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
            (integrable_const _)
          exact Filter.Eventually.of_forall fun t => by
            have := hf.2 t; have := norm_nonneg (f t); nlinarith
      _ = 1 := by simp
  have hle : ∑ n ∈ ({0, -1, -2, -3} : Finset ℤ), ‖fourierCoeff (⇑F) n‖ ^ 2 ≤
      ∑' n, ‖fourierCoeff (⇑F) n‖ ^ 2 :=
    hsum.summable.sum_le_tsum _ (fun _ _ => by positivity)
  rw [hsum.tsum_eq] at hle
  simp only [hcoef] at hle
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hle
  simp only [mom]
  push_cast
  linarith

end Harris
