module

public import HarrisCert.Bridge2

/-!
# The extremal functions: `φ(e^{-it}, e^{-2it}) = -2` and `q(h₀) = -M`

`h₀ = (z̄ + r)/(z + r)` with `r = 1/√3`. Its moments `c_n = ∫ zⁿ h₀ dη` satisfy
`c_{n+1} + r c_n = [n = 1] + r [n = 0]` (from `(z + r) h₀ = z̄ + r`), and boundedness forces `c₀ = 0`.
-/

open MeasureTheory Complex Filter Topology

@[expose] public section

namespace Harris

lemma integral_fourier (m : ℤ) : ∫ t, fourier m t ∂η = if m = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) m) 0
  unfold fourierCoeff at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [h, Pi.single_apply]
  by_cases hm : m = 0
  · subst hm; simp
  · simp [hm, Ne.symm hm]

lemma integrable_cont {g : 𝕋 → ℂ} (hg : Continuous g) : Integrable g η :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ## The witness for `‖φ‖ = 2` -/

lemma mom_fourier (m : ℤ) (k : ℕ) : mom (fun t => fourier m t) k = if -(k : ℤ) = m then 1 else 0 := by
  unfold mom
  rw [show (fun t => fourier m t) = ⇑(fourier m) from rfl, fourierCoeff_fourier, Pi.single_apply]

lemma fourier_mem (m : ℤ) : (fun t => fourier m t) ∈ Ball :=
  ⟨(fourier m).continuous.aestronglyMeasurable, fun t => le_of_eq (norm_fourier_apply m t)⟩

lemma phi_witness : phiB (momV fun t => fourier (-1) t) (momV fun t => fourier (-2) t) = -2 := by
  simp only [phiB, momV, mom_fourier]
  norm_num

/-! ## `h₀` -/

lemma r_pos : 0 < r := by unfold r; positivity
lemma r_lt_one : r < 1 := by
  unfold r
  have : Real.sqrt 3 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith
lemma r_sq : r ^ 2 = 1 / 3 := by unfold r; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma den_ne (t : 𝕋) : fourier 1 t + (r : ℂ) ≠ 0 := by
  intro h
  have h1 : fourier 1 t = -(r : ℂ) := by linear_combination h
  have := norm_fourier_apply 1 t
  rw [h1, norm_neg, Complex.norm_real, Real.norm_of_nonneg r_pos.le] at this
  linarith [r_lt_one]

noncomputable def h0 : 𝕋 → ℂ := fun t => (fourier (-1) t + r) / (fourier 1 t + r)

lemma h0_cont : Continuous h0 := by
  unfold h0
  exact ((fourier (-1)).continuous.add continuous_const).div
    ((fourier 1).continuous.add continuous_const) den_ne

lemma h0_norm (t : 𝕋) : ‖h0 t‖ = 1 := by
  unfold h0
  rw [norm_div, fourier_neg]
  have : (starRingEnd ℂ) (fourier 1 t) + (r : ℂ) = (starRingEnd ℂ) (fourier 1 t + r) := by
    simp [Complex.conj_ofReal]
  rw [this, RCLike.norm_conj, div_self]
  exact norm_ne_zero_iff.mpr (den_ne t)

lemma h0_mem : h0 ∈ Ball := ⟨h0_cont.aestronglyMeasurable, fun t => le_of_eq (h0_norm t)⟩

lemma h0_eq (t : 𝕋) : (fourier 1 t + r) * h0 t = fourier (-1) t + r := by
  unfold h0; rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ (den_ne t)

/-- `c_n = ∫ zⁿ h₀ dη`. -/
noncomputable def ch (n : ℤ) : ℂ := ∫ t, fourier n t * h0 t ∂η

lemma ch_norm (n : ℤ) : ‖ch n‖ ≤ 1 := by
  unfold ch
  calc ‖∫ t, fourier n t * h0 t ∂η‖ ≤ ∫ t, ‖fourier n t * h0 t‖ ∂η := norm_integral_le_integral_norm _
    _ = ∫ _t, (1 : ℝ) ∂η := by congr 1; funext t; rw [norm_mul, norm_fourier_apply, h0_norm, one_mul]
    _ = 1 := by simp

lemma ch_rec (n : ℤ) : ch (n + 1) + r * ch n = (if n = 1 then 1 else 0) + r * (if n = 0 then 1 else 0) := by
  have hL : ∫ t, fourier n t * ((fourier 1 t + r) * h0 t) ∂η = ch (n + 1) + r * ch n := by
    unfold ch
    rw [← integral_const_mul, ← integral_add]
    · congr 1; funext t; rw [fourier_add]; ring
    · exact integrable_cont ((fourier (n + 1)).continuous.mul h0_cont)
    · exact integrable_cont (continuous_const.mul ((fourier n).continuous.mul h0_cont))
  have hR : ∫ t, fourier n t * (fourier (-1) t + r) ∂η =
      (if n = 1 then 1 else 0) + r * (if n = 0 then 1 else 0) := by
    have e : (fun t : 𝕋 => fourier n t * (fourier (-1) t + r)) =
        fun t : 𝕋 => fourier (n - 1) t + (r : ℂ) * fourier n t := by
      funext t; rw [sub_eq_add_neg, fourier_add]; ring
    rw [e, integral_add (integrable_cont (g := fun t : 𝕋 => fourier (n - 1) t) (fourier _).continuous)
      (integrable_cont (g := fun t : 𝕋 => (r : ℂ) * fourier n t) (by fun_prop)), integral_const_mul,
      integral_fourier, integral_fourier]
    congr 1
    by_cases h : n = 1 <;> simp [h, sub_eq_zero]
  rw [← hL, ← hR]; congr 1; funext t; rw [h0_eq]

lemma ch_zero : ch 0 = 0 := by
  -- c(-m) = (-1/r)^m c(0), and |c(-m)| ≤ 1
  have hstep : ∀ m : ℕ, ch (-(m : ℤ)) = r * (-1) * ch (-((m + 1 : ℕ) : ℤ)) := by
    intro m
    have := ch_rec (-((m + 1 : ℕ) : ℤ))
    have h1 : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
    have h2 : -((m + 1 : ℕ) : ℤ) ≠ 1 := by omega
    have h3 : -((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [h1, if_neg h2, if_neg h3] at this
    linear_combination this
  have hpow : ∀ m : ℕ, ch 0 = ((r : ℂ) * (-1)) ^ m * ch (-(m : ℤ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [ih, hstep m, pow_succ]; ring
  have hbound : ∀ m : ℕ, ‖ch 0‖ ≤ r ^ m := by
    intro m
    rw [hpow m, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg r_pos.le,
      norm_neg, norm_one, mul_one]
    exact mul_le_of_le_one_right (pow_nonneg r_pos.le m) (ch_norm _)
  have hlim : Tendsto (fun m : ℕ => r ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one r_pos.le r_lt_one
  have : ‖ch 0‖ ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  exact norm_le_zero_iff.mp this

lemma mom_h0 (k : ℕ) : mom h0 k = ch k := by rw [mom_eq]; rfl

lemma momV_h0 : momV h0 = ![0, (r : ℂ), 2 / 3, -(2 * r / 3 : ℂ)] := by
  have c1 : ch 1 = r := by have := ch_rec 0; rw [ch_zero] at this; simpa using this
  have c2 : ch 2 = 2 / 3 := by
    have := ch_rec 1; rw [show (1 : ℤ) + 1 = 2 by norm_num, c1] at this
    simp at this
    have hr : (r : ℂ) ^ 2 = 1 / 3 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) r_sq; push_cast at this; exact this
    linear_combination this - hr
  have c3 : ch 3 = -(2 * r / 3 : ℂ) := by
    have := ch_rec 2; rw [show (2 : ℤ) + 1 = 3 by norm_num, c2] at this
    simp at this
    linear_combination this
  funext k; fin_cases k <;> simp [momV, mom_h0, ch_zero, c1, c2, c3]

lemma q_h0 : qform (momV h0) = -(M : ℂ) := by
  rw [momV_h0]; simp [qform, M, r]; ring

end Harris
