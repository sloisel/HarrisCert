module

public import HarrisCert.Local5

/-!
# Local theorem, part 6: the Gram integrals and Bessel's inequality in `L²(ρ)`
-/

open MeasureTheory Complex Filter Topology

@[expose] public section

namespace Harris

lemma hzk_cont (k : ℕ) : Continuous (hzk k) := by unfold hzk; exact h0_cont.mul (fourier _).continuous

lemma φb_cont (a : Fin 7) : Continuous (φb a) := by
  unfold φb; split_ifs
  · exact Complex.continuous_im.comp (hzk_cont _)
  · exact Complex.continuous_re.comp (hzk_cont _)

lemma Wfun_cont (m : ℤ) : Continuous fun t => fourier m t * h0sqρ t := (fourier m).continuous.mul h0sqρ_cont
lemma Ufun_cont (m : ℤ) : Continuous fun t => fourier m t * invρ t := (fourier m).continuous.mul invρ_cont

noncomputable def Gfn (j k : ℕ) (s : ℂ) (t : 𝕋) : ℂ :=
  (s * (fourier ((j : ℤ) + k) t * h0sqρ t) + fourier ((j : ℤ) - k) t * invρ t) / 2

lemma Gfn_cont (j k : ℕ) (s : ℂ) : Continuous (Gfn j k s) := by
  unfold Gfn; exact ((continuous_const.mul (Wfun_cont _)).add (Ufun_cont _)).div_const _

lemma intG (j k : ℕ) (s : ℂ) : ∫ t, Gfn j k s t ∂η = (s * Wc ((j : ℤ) + k) + Uc ((j : ℤ) - k)) / 2 := by
  unfold Gfn
  rw [integral_div, integral_add ((integrable_cont (Wfun_cont _)).const_mul s)
    (integrable_cont (Ufun_cont _)), integral_const_mul]
  rfl

lemma pw_parts (j k : ℕ) (t : 𝕋) :
    (hzk j t).re * (hzk k t).re / ρf t = (Gfn j k 1 t).re ∧
    (hzk j t).im * (hzk k t).im / ρf t = (Gfn j k (-1) t).re ∧
    (hzk j t).re * (hzk k t).im / ρf t = -(Gfn j k (-1) t).im ∧
    (hzk j t).im * (hzk k t).re / ρf t = (Gfn j k 1 t).im := by
  have e1 := hzk_mul j k t
  have e2 := hzk_mul_conj j k t
  set A := hzk j t; set B := hzk k t
  have hρ : (ρf t : ℂ) ≠ 0 := by exact_mod_cast (ρf_pos t).ne'
  have g1 : Gfn j k 1 t = (A * B / ρf t + A * (starRingEnd ℂ) B / ρf t) / 2 := by
    unfold Gfn; rw [e1, e2]; ring
  have g2 : Gfn j k (-1) t = (-(A * B / ρf t) + A * (starRingEnd ℂ) B / ρf t) / 2 := by
    unfold Gfn; rw [e1, e2]; ring
  rw [g1, g2]
  obtain ⟨q1, q2, q3, q4⟩ := prod_parts A B
  have r2 : ∀ X : ℂ, (X / 2).re = X.re / 2 := fun X => by simp
  have i2 : ∀ X : ℂ, (X / 2).im = X.im / 2 := fun X => by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r2, Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, q1]; ring
  · rw [r2, Complex.add_re, Complex.neg_re, Complex.div_ofReal_re, Complex.div_ofReal_re, q2]; ring
  · rw [i2, Complex.add_im, Complex.neg_im, Complex.div_ofReal_im, Complex.div_ofReal_im, q3]; ring
  · rw [i2, Complex.add_im, Complex.div_ofReal_im, Complex.div_ofReal_im, q4]; ring

/-- The four Gram integrals in terms of `U`, `W`. -/
lemma gram_parts (j k : ℕ) :
    (∫ t, (hzk j t).re * (hzk k t).re / ρf t ∂η) = ((Wc ((j : ℤ) + k) + Uc ((j : ℤ) - k)) / 2).re ∧
    (∫ t, (hzk j t).im * (hzk k t).im / ρf t ∂η) = ((-Wc ((j : ℤ) + k) + Uc ((j : ℤ) - k)) / 2).re ∧
    (∫ t, (hzk j t).re * (hzk k t).im / ρf t ∂η) = -((-Wc ((j : ℤ) + k) + Uc ((j : ℤ) - k)) / 2).im ∧
    (∫ t, (hzk j t).im * (hzk k t).re / ρf t ∂η) = ((Wc ((j : ℤ) + k) + Uc ((j : ℤ) - k)) / 2).im := by
  have i1 := integrable_cont (Gfn_cont j k 1)
  have i2 := integrable_cont (Gfn_cont j k (-1))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [fun t => (pw_parts j k t).1]
    have h := integral_re i1; simp only [RCLike.re_to_complex] at h; rw [h, intG]; simp
  · simp_rw [fun t => (pw_parts j k t).2.1]
    have h := integral_re i2; simp only [RCLike.re_to_complex] at h; rw [h, intG]; simp
  · simp_rw [fun t => (pw_parts j k t).2.2.1]
    have h := integral_im i2; simp only [RCLike.im_to_complex] at h; rw [integral_neg, h, intG]; simp
  · simp_rw [fun t => (pw_parts j k t).2.2.2]
    have h := integral_im i1; simp only [RCLike.im_to_complex] at h; rw [h, intG]; simp

/-- The Gram matrix: `∫ φ_a φ_b / ρ = σ(Γk a b)`. -/
lemma gram_eq (a b : Fin 7) : ∫ t, φb a t * φb b t / ρf t ∂η = σ (Γk a b) := by
  have ha := bj_le a
  have hb := bj_le b
  have hU := Uc_σ ((bj a : ℤ) - bj b) (by omega)
  have hW := Wc_σ ((bj a : ℤ) + bj b) (by omega)
  obtain ⟨g1, g2, g3, g4⟩ := gram_parts (bj a) (bj b)
  unfold φb Γk
  cases h1 : bim a <;> cases h2 : bim b <;> simp only [Bool.false_eq_true, ite_false, ite_true, and_self,
    and_true, and_false, true_and, false_and]
  · rw [g1, hU, hW]; simp [map_add, Rat.smul_def]; ring
  · rw [g3, hU, hW]; simp
  · rw [g4, hU, hW]; simp
  · rw [g2, hU, hW]; simp [map_sub, Rat.smul_def]; ring

lemma integrable_cont' {g : 𝕋 → ℝ} (hg : Continuous g) : Integrable g η :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma BddMeas.integrable_cmul {f : 𝕋 → ℝ} (hf : BddMeas f) {k : 𝕋 → ℝ} (hk : Continuous k) (n : ℕ) :
    Integrable (fun t => k t * f t ^ n) η := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := (isCompact_univ.image hk).isBounded.exists_norm_le
  refine Integrable.mono' (integrable_const (D * C ^ n)) (hk.aestronglyMeasurable.mul (hf.1.pow n)) ?_
  refine Eventually.of_forall fun t => ?_
  rw [norm_mul, norm_pow, Real.norm_eq_abs (f t)]
  exact mul_le_mul (hD _ ⟨t, trivial, rfl⟩) (pow_le_pow_left₀ (abs_nonneg _) (hC t) n) (by positivity)
    (le_trans (norm_nonneg _) (hD _ ⟨t, trivial, rfl⟩))

/-- Bessel's inequality in `L²(ρ)` for the seven basis functions:
`∫ ρ f² ≥ 2 Σ c_a ∫ f φ_a - Σ c_a c_b Γ_ab`. -/
lemma bessel_rho {f : 𝕋 → ℝ} (hf : BddMeas f) (c : Fin 7 → ℝ) :
    2 * ∑ a, c a * ∫ t, f t * φb a t ∂η - ∑ a, ∑ b, c a * c b * σ (Γk a b) ≤
      ∫ t, ρf t * f t ^ 2 ∂η := by
  set ψ : 𝕋 → ℝ := fun t => ∑ a, c a * φb a t with hψ
  have hψc : Continuous ψ := by
    rw [hψ]; exact continuous_finsetSum _ (fun a _ => continuous_const.mul (φb_cont a))
  have hρinv : Continuous fun t => (ρf t)⁻¹ := ρf_cont.inv₀ (fun t => (ρf_pos t).ne')
  have pw : ∀ t, 2 * (f t * ψ t) - ψ t ^ 2 / ρf t ≤ ρf t * f t ^ 2 := by
    intro t
    have hp := ρf_pos t
    have : 0 ≤ (ρf t * f t - ψ t) ^ 2 / ρf t := by positivity
    have e : (ρf t * f t - ψ t) ^ 2 / ρf t = ρf t * f t ^ 2 - 2 * (f t * ψ t) + ψ t ^ 2 / ρf t := by
      field_simp; ring
    linarith
  have i1 : Integrable (fun t => f t * ψ t) η := hf.integrable_mulR hψc
  have i2 : Integrable (fun t => ψ t ^ 2 / ρf t) η :=
    integrable_cont' ((hψc.pow 2).div ρf_cont (fun t => (ρf_pos t).ne'))
  have i3 := hf.integrable_cmul ρf_cont 2
  have hmono : ∫ t, (2 * (f t * ψ t) - ψ t ^ 2 / ρf t) ∂η ≤ ∫ t, ρf t * f t ^ 2 ∂η :=
    integral_mono ((i1.const_mul 2).sub i2) i3 pw
  rw [integral_sub (i1.const_mul 2) i2, integral_const_mul] at hmono
  have e1 : ∫ t, f t * ψ t ∂η = ∑ a, c a * ∫ t, f t * φb a t ∂η := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun a _ => (hf.integrable_mulR (φb_cont a)).const_mul (c a))]
    congr 1; funext t; simp only [hψ, Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  have e2 : ∫ t, ψ t ^ 2 / ρf t ∂η = ∑ a, ∑ b, c a * c b * σ (Γk a b) := by
    have : (fun t => ψ t ^ 2 / ρf t) = fun t => ∑ a, ∑ b, c a * c b * (φb a t * φb b t / ρf t) := by
      funext t; simp only [hψ, sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro b _; ring
    rw [this, integral_finsetSum]
    · apply Finset.sum_congr rfl; intro a _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl; intro b _
        rw [integral_const_mul, gram_eq]
      · intro b _
        exact (integrable_cont' (((φb_cont a).mul (φb_cont b)).div ρf_cont
          (fun t => (ρf_pos t).ne'))).const_mul _
    · intro a _
      exact integrable_finsetSum _ (fun b _ => (integrable_cont' (((φb_cont a).mul (φb_cont b)).div
        ρf_cont (fun t => (ρf_pos t).ne'))).const_mul _)
  rw [e1, e2] at hmono
  exact hmono

end Harris
