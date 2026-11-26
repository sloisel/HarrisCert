module

public import HarrisCert.Local2

/-!
# Local theorem, part 3: coefficient values, the Gram integrals, Bessel in `L²(ρ)`

`U n = ∫ zⁿ/ρ`, `W n = ∫ h₀² zⁿ/ρ`. From the recurrences:
`U 0 = 3/(4r)`, `U ±1 = -3/4`, `U ±2 = 3r/4`, `U ±3 = -1/4`;
`W 0..6 = 0, 0, 0, 1/2, 0, -1/2, 4/(9r)`.
-/

open MeasureTheory Complex Filter Topology

@[expose] public section

namespace Harris

lemma rr : (r : ℂ) * r = 1 / 3 := by rw [← sq]; exact r_sq_C
lemma r_ne : (r : ℂ) ≠ 0 := by exact_mod_cast r_pos.ne'

/-! ## Coefficients of `1/(z+r)` and `1/(1+rz)` -/

lemma E1_0 : coef e1 0 = 0 := E1_neg 0 le_rfl
lemma E1_1 : coef e1 1 = 1 := by have := E1_rec 0; rw [E1_0] at this; simpa using this
lemma E1_2 : coef e1 2 = -r := by have := E1_rec 1; rw [E1_1] at this; simp at this; linear_combination this
lemma E1_3 : coef e1 3 = r * r := by
  have := E1_rec 2; rw [E1_2] at this; simp at this; linear_combination this

lemma F1_1 : coef f1 1 = 0 := F1_pos 1 le_rfl
lemma F1_0 : coef f1 0 = 1 := by have := F1_rec 0; rw [show (0 : ℤ) + 1 = 1 by norm_num, F1_1] at this; simpa using this
lemma F1_m1 : coef f1 (-1) = -r := by
  have := F1_rec (-1); rw [show (-1 : ℤ) + 1 = 0 by norm_num, F1_0] at this; simp at this
  linear_combination this
lemma F1_m2 : coef f1 (-2) = r * r := by
  have := F1_rec (-2); rw [show (-2 : ℤ) + 1 = -1 by norm_num, F1_m1] at this; simp at this
  linear_combination this
lemma F1_m3 : coef f1 (-3) = -(r * r * r) := by
  have := F1_rec (-3); rw [show (-3 : ℤ) + 1 = -2 by norm_num, F1_m2] at this; simp at this
  linear_combination this

/-! ## `1/ρ` and `h₀²/ρ` -/

lemma rho_C (t : 𝕋) : (ρf t : ℂ) = 2 * r * ((zz t + r) * ((starRingEnd ℂ) (zz t) + r)) := by
  unfold ρf
  have : ((‖zz t + r‖ ^ 2 : ℝ) : ℂ) = (zz t + r) * (starRingEnd ℂ) (zz t + r) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast at this ⊢
  rw [this]; simp

noncomputable def invρ (t : 𝕋) : ℂ := 1 / (ρf t : ℂ)
noncomputable def h0sqρ (t : 𝕋) : ℂ := h0 t ^ 2 / (ρf t : ℂ)

lemma invρ_cont : Continuous invρ := by
  unfold invρ
  exact continuous_const.div (Complex.continuous_ofReal.comp ρf_cont) (fun t => by
    exact_mod_cast (ρf_pos t).ne')
lemma h0sqρ_cont : Continuous h0sqρ := by
  unfold h0sqρ
  exact (h0_cont.pow 2).div (Complex.continuous_ofReal.comp ρf_cont) (fun t => by
    exact_mod_cast (ρf_pos t).ne')

lemma invρ_eq (t : 𝕋) : invρ t = (-(r : ℂ) * e1 t + f1 t) / (2 * r * (1 - r * r)) := by
  unfold invρ e1 f1
  rw [rho_C]
  have hz := zz_mul_conj t
  have h1 : zz t + (r : ℂ) ≠ 0 := den_ne t
  have h2 := den2_ne t
  have h3 : (1 : ℂ) - r * r ≠ 0 := by rw [rr]; norm_num
  have hz0 : zz t ≠ 0 := by intro h; rw [h, zero_mul] at hz; exact zero_ne_one hz
  have hbar : (starRingEnd ℂ) (zz t) = (zz t)⁻¹ := (eq_inv_of_mul_eq_one_right hz)
  have hc : (zz t)⁻¹ + r = (1 + r * zz t) / zz t := by field_simp
  rw [hbar, hc]
  have h4 : (r : ℂ) - r ^ 3 ≠ 0 := by
    rw [show (r : ℂ) - r ^ 3 = r * (1 - r * r) by ring]; exact mul_ne_zero r_ne h3
  have hr0 := r_ne
  have h5 : (1 : ℂ) - r ^ 2 ≠ 0 := by rw [sq]; exact h3
  field_simp
  ring

lemma h0sqρ_eq (t : 𝕋) : h0sqρ t = e3 t / (2 * r) := by
  unfold h0sqρ e3 e2
  rw [rho_C, h0_eq_zz]
  have h1 : zz t + (r : ℂ) ≠ 0 := den_ne t
  have h4 : (starRingEnd ℂ) (zz t) + r ≠ 0 := by
    rw [show (starRingEnd ℂ) (zz t) + r = (starRingEnd ℂ) (zz t + r) by simp]
    exact (map_ne_zero _).mpr h1
  field_simp

/-- `U n = ∫ zⁿ/ρ`. -/
noncomputable def Uc (n : ℤ) : ℂ := coef invρ n
/-- `W n = ∫ h₀² zⁿ/ρ`. -/
noncomputable def Wc (n : ℤ) : ℂ := coef h0sqρ n

lemma coef_lin (a b : ℂ) {e f : 𝕋 → ℂ} (he : Continuous e) (hf : Continuous f) (n : ℤ) :
    coef (fun t => (a * e t + f t) / b) n = (a * coef e n + coef f n) / b := by
  unfold coef
  have hfun : (fun t => fourier n t * ((a * e t + f t) / b)) =
      fun t => (b⁻¹ * a) * (fourier n t * e t) + b⁻¹ * (fourier n t * f t) := by
    funext t; field_simp
  rw [hfun, integral_add, integral_const_mul, integral_const_mul]
  · field_simp
  · exact (integrable_fe he _).const_mul _
  · exact (integrable_fe hf _).const_mul _

lemma Uc_eq (n : ℤ) : Uc n = (-(r : ℂ) * coef e1 n + coef f1 n) / (2 * r * (1 - r * r)) := by
  unfold Uc
  rw [coef_congr invρ_eq, coef_lin _ _ e1_cont f1_cont]

lemma Wc_eq (n : ℤ) : Wc n = coef e3 n / (2 * r) := by
  unfold Wc
  rw [coef_congr h0sqρ_eq]
  unfold coef
  rw [← integral_div]; congr 1; funext t; ring

end Harris
