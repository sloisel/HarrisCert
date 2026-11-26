module

public import HarrisCert.Local11

/-!
# Local theorem, part 12: the test vectors `t_w`, the alignment condition

* `t_w = m̃(w) / (2r|w + r|⁴)`, so that `ρ(w) t_w·ξ = m̃(w)·ξ / |w + r|²`;
  `(Cᵀt_w)ᵀ Âᵢ (Cᵀt_w) ≤ 230` and `|t_w·ξ_κ| ≤ √3`.
* At a minimizer of `u ↦ X(a, aorb u)` over the unit circle, `Im(r a₀ + (2/3) a₁ - r a₂) = 0`.
-/

open MeasureTheory Complex Matrix

@[expose] public section

namespace Harris

lemma Nz_pos (t : 𝕋) : 0 < ‖zz t + r‖ := norm_pos_iff.mpr (den_ne t)

noncomputable def tw (t : 𝕋) : Fin 7 → ℝ := (1 / (2 * r * ‖zz t + r‖ ^ 4)) • mt (zz t)

lemma tw_cont : Continuous tw := by
  have hz : Continuous zz := (fourier 1).continuous
  have hN : Continuous fun t => ‖zz t + r‖ := (hz.add continuous_const).norm
  have hc : Continuous fun t => 1 / (2 * r * ‖zz t + r‖ ^ 4) :=
    continuous_const.div (continuous_const.mul (hN.pow 4)) (fun t => by
      have := Nz_pos t; have := r_pos; positivity)
  have hm : Continuous fun t => mt (zz t) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [mt, cvec] <;> fun_prop
  exact hc.smul hm

lemma ρ_tw (t : 𝕋) (ξ : Fin 7 → ℝ) : ρf t * (tw t ⬝ᵥ ξ) = mt (zz t) ⬝ᵥ ξ / ‖zz t + r‖ ^ 2 := by
  have hN := Nz_pos t
  have hr := r_pos
  unfold tw ρf; rw [smul_dotProduct, smul_eq_mul]; field_simp

lemma tw_Λ (t : 𝕋) : (Cr.transpose *ᵥ tw t) ⬝ᵥ Air *ᵥ (Cr.transpose *ᵥ tw t) ≤ 230 := by
  have h := Qm_le (zz t) (norm_zz t)
  have hN := Nz_pos t
  have hr := r_pos
  have hr2 := r_sq
  unfold Qm at h
  unfold tw
  set c := 1 / (2 * r * ‖zz t + r‖ ^ 4) with hc
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hc0 : 0 ≤ c := by positivity
  have h1 : c * (c * ((Cr.transpose *ᵥ mt (zz t)) ⬝ᵥ Air *ᵥ (Cr.transpose *ᵥ mt (zz t)))) ≤
      c * (c * (920 / 3 * ‖zz t + r‖ ^ 8)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hc0) hc0
  have h2 : c * (c * (920 / 3 * ‖zz t + r‖ ^ 8)) = 230 := by
    rw [hc]; field_simp; rw [show r ^ 2 = 1 / 3 from hr2]; norm_num
  linarith

lemma ξκr_vals : ξκr = ![0, r / 2, -1 / 3, r, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [ξκr, vR, ξκ, σ_mk] <;> ring

lemma cκr_vals : cκr = ![r, 2 / 3, -r, 0, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [cκr, vR, cκ, σ_mk] <;> ring

lemma mt_ξκ (z : ℂ) (hz : ‖z‖ = 1) : mt z ⬝ᵥ ξκr = -(4 / 3) * ‖z + r‖ ^ 2 * z.im := by
  have hzc : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hN : ((‖z + r‖ ^ 2 : ℝ) : ℂ) = (z + r) * ((starRingEnd ℂ) z + r) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_add, Complex.conj_ofReal]
  have hr := r_sq_C
  have key : (r / 2 : ℂ) * cvec z 1 - 1 / 3 * cvec z 2 + r * cvec z 3 =
      ((‖z + r‖ ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) z - z / 3) := by
    rw [hN, cvec1, cvec2, cvec3]
    linear_combination ((starRingEnd ℂ) z + r) * ((-1 / 3 - r * z) * hzc + (1 - z ^ 2) * hr)
  have h := congrArg Complex.im key
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_im, Complex.div_ofNat_im, Complex.div_ofNat_re] at h
  rw [ξκr_vals]
  simp only [mt, dotProduct, Fin.sum_univ_seven]
  simp
  norm_num at h
  linarith

lemma tw_ξκ (t : 𝕋) : |tw t ⬝ᵥ ξκr| ≤ Real.sqrt 3 := by
  have hN := Nz_pos t
  have hr := r_pos
  have hb := im_bound (zz t) (norm_zz t)
  unfold tw
  rw [smul_dotProduct, smul_eq_mul, mt_ξκ _ (norm_zz t), sqrt3_eq]
  have e : 1 / (2 * r * ‖zz t + r‖ ^ 4) * (-(4 / 3) * ‖zz t + r‖ ^ 2 * (zz t).im) =
      -(2 / 3 * (zz t).im) / (r * ‖zz t + r‖ ^ 2) := by field_simp; ring
  have hp : 0 < r * ‖zz t + r‖ ^ 2 := by positivity
  rw [e, abs_div, abs_neg, abs_of_pos hp, div_le_iff₀ hp, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2 / 3)]
  have hr3 : 3 * r * r = 1 := by nlinarith [r_sq]
  nlinarith

/-- The pointwise bound `(4/3)|Im z| ≤ √3 ρ`. -/
lemma IG_le (t : 𝕋) : 4 / 3 * |(zz t).im| ≤ Real.sqrt 3 * ρf t := by
  have hb := im_bound (zz t) (norm_zz t)
  have hr3 : 3 * r * r = 1 := by nlinarith [r_sq]
  rw [sqrt3_eq]; unfold ρf
  nlinarith

end Harris
