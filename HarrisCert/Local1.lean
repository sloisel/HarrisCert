module

public import HarrisCert.Assembly

/-!
# Local theorem, part 1: the decomposition `g = h₀ (1 + x + i y)` and the basic identity

For `g` in the unit ball put `v = g · conj h₀`, `x = Re v - 1 ≤ 0`, `y = Im v`. With
`A(f)_k = ∫ f h₀ z^k dη` (for real `f`) the moments are `a(g) = a(h₀) + A(x) + i A(y)`, and with
`ρ = |P| = 2r|z + r|²`:

* `X := M + Re φ(a(g), a(h₀)) = -∫ ρ x`,
* `M + Re q(g) = 2X + Re q(A x) - Re q(A y) - 2 Im φ(A x, A y)`.
-/

open MeasureTheory Complex

@[expose] public section

namespace Harris

noncomputable def zz (t : 𝕋) : ℂ := fourier 1 t

lemma norm_zz (t : 𝕋) : ‖zz t‖ = 1 := norm_fourier_apply 1 t

lemma conj_zz (t : 𝕋) : (starRingEnd ℂ) (zz t) = fourier (-1) t := by
  unfold zz; rw [fourier_neg]

lemma zz_mul_conj (t : 𝕋) : zz t * (starRingEnd ℂ) (zz t) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_zz]
  norm_num

/-- `ρ = |P| = 2r |z + r|²`. -/
noncomputable def ρf (t : 𝕋) : ℝ := 2 * r * ‖zz t + r‖ ^ 2

/-- `P = Λ h₀ = -2r (z + r)²`. -/
noncomputable def Pf (t : 𝕋) : ℂ := -2 * r * (zz t + r) ^ 2

lemma h0_eq_zz (t : 𝕋) : h0 t = ((starRingEnd ℂ) (zz t) + r) / (zz t + r) := by
  unfold h0; rw [conj_zz]; rfl

lemma h0_P (t : 𝕋) : h0 t * Pf t = -(ρf t : ℂ) := by
  rw [h0_eq_zz]
  have hd : zz t + (r : ℂ) ≠ 0 := den_ne t
  have hn : ((‖zz t + r‖ ^ 2 : ℝ) : ℂ) = (zz t + r) * (starRingEnd ℂ) (zz t + r) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold Pf ρf
  push_cast
  rw [show ((‖zz t + ↑r‖ : ℝ) : ℂ) ^ 2 = ((‖zz t + r‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, hn]
  simp only [map_add, Complex.conj_ofReal]
  field_simp
  all_goals ring

lemma ρf_pos (t : 𝕋) : 0 < ρf t := by
  unfold ρf
  exact mul_pos (mul_pos two_pos r_pos) (pow_pos (norm_pos_iff.mpr (den_ne t)) 2)

/-- `ρ ≥ m = 2r(1-r)²`. -/
lemma ρf_ge (t : 𝕋) : 2 * r * (1 - r) ^ 2 ≤ ρf t := by
  unfold ρf
  have h1 : 1 - r ≤ ‖zz t + r‖ := by
    have := norm_sub_norm_le (zz t) (-(r : ℂ))
    rw [norm_zz, norm_neg, Complex.norm_real, Real.norm_of_nonneg r_pos.le, sub_neg_eq_add] at this
    linarith
  have h0 : 0 ≤ 1 - r := by linarith [r_lt_one]
  have := r_pos
  have := pow_le_pow_left₀ h0 h1 2
  nlinarith

lemma ρf_cont : Continuous ρf := by
  unfold ρf zz; fun_prop

/-! ## The decomposition -/

noncomputable def vf (g : 𝕋 → ℂ) (t : 𝕋) : ℂ := g t * (starRingEnd ℂ) (h0 t)
noncomputable def xf (g : 𝕋 → ℂ) (t : 𝕋) : ℝ := (vf g t).re - 1
noncomputable def yf (g : 𝕋 → ℂ) (t : 𝕋) : ℝ := (vf g t).im

lemma h0_conj_mul (t : 𝕋) : (starRingEnd ℂ) (h0 t) * h0 t = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h0_norm]; simp

lemma g_eq (g : 𝕋 → ℂ) (t : 𝕋) : g t = h0 t * (1 + xf g t + I * yf g t) := by
  have : (1 : ℂ) + xf g t + I * yf g t = vf g t := by
    apply Complex.ext <;> simp [xf, yf]
  rw [this, vf]
  have h := h0_conj_mul t
  calc g t = g t * ((starRingEnd ℂ) (h0 t) * h0 t) := by rw [h, mul_one]
    _ = h0 t * (g t * (starRingEnd ℂ) (h0 t)) := by ring

lemma norm_vf {g : 𝕋 → ℂ} (hg : g ∈ Ball) (t : 𝕋) : ‖vf g t‖ ≤ 1 := by
  rw [vf, norm_mul, RCLike.norm_conj, h0_norm, mul_one]; exact hg.2 t

lemma xf_nonpos {g : 𝕋 → ℂ} (hg : g ∈ Ball) (t : 𝕋) : xf g t ≤ 0 := by
  have := Complex.re_le_norm (vf g t); have := norm_vf hg t; unfold xf; linarith

lemma disc {g : 𝕋 → ℂ} (hg : g ∈ Ball) (t : 𝕋) : xf g t ^ 2 + yf g t ^ 2 ≤ -2 * xf g t := by
  have h := norm_vf hg t
  have h2 : (vf g t).re ^ 2 + (vf g t).im ^ 2 ≤ 1 := by
    have := Complex.sq_norm (vf g t); rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg (vf g t)]
  unfold xf yf; nlinarith

lemma vf_meas {g : 𝕋 → ℂ} (hg : g ∈ Ball) : AEStronglyMeasurable (vf g) η :=
  hg.1.mul (Complex.continuous_conj.comp h0_cont).aestronglyMeasurable

lemma xf_meas {g : 𝕋 → ℂ} (hg : g ∈ Ball) : AEStronglyMeasurable (xf g) η :=
  ((Complex.continuous_re.comp_aestronglyMeasurable (vf_meas hg)).sub aestronglyMeasurable_const)

lemma yf_meas {g : 𝕋 → ℂ} (hg : g ∈ Ball) : AEStronglyMeasurable (yf g) η :=
  Complex.continuous_im.comp_aestronglyMeasurable (vf_meas hg)

lemma xf_bound {g : 𝕋 → ℂ} (hg : g ∈ Ball) (t : 𝕋) : |xf g t| ≤ 2 := by
  have h1 := Complex.abs_re_le_norm (vf g t); have h2 := norm_vf hg t
  have h3 := abs_le.mp (le_trans h1 h2)
  unfold xf; rw [abs_le]; constructor <;> linarith [h3.1, h3.2]

lemma yf_bound {g : 𝕋 → ℂ} (hg : g ∈ Ball) (t : 𝕋) : |yf g t| ≤ 1 := by
  have := Complex.abs_im_le_norm (vf g t); have := norm_vf hg t; unfold yf; linarith

/-- Bounded measurable real functions. -/
def BddMeas (f : 𝕋 → ℝ) : Prop := AEStronglyMeasurable f η ∧ ∃ C, ∀ t, |f t| ≤ C

lemma xf_bm {g : 𝕋 → ℂ} (hg : g ∈ Ball) : BddMeas (xf g) := ⟨xf_meas hg, 2, xf_bound hg⟩
lemma yf_bm {g : 𝕋 → ℂ} (hg : g ∈ Ball) : BddMeas (yf g) := ⟨yf_meas hg, 1, yf_bound hg⟩

lemma BddMeas.integrable_mul {f : 𝕋 → ℝ} (hf : BddMeas f) {k : 𝕋 → ℂ} (hk : Continuous k) :
    Integrable (fun t => (f t : ℂ) * k t) η := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := (isCompact_univ.image hk).isBounded.exists_norm_le
  refine Integrable.mono' (integrable_const (C * D))
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1).mul hk.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (hC t) (hD _ ⟨t, trivial, rfl⟩) (norm_nonneg _) (le_trans (abs_nonneg _) (hC t))

lemma BddMeas.integrable_mulR {f : 𝕋 → ℝ} (hf : BddMeas f) {k : 𝕋 → ℝ} (hk : Continuous k) :
    Integrable (fun t => f t * k t) η := by
  have := hf.integrable_mul (k := fun t => (k t : ℂ)) (Complex.continuous_ofReal.comp hk)
  have h2 := this.re
  simpa using h2

/-- `A(f)_k = ∫ f h₀ z^k dη`. -/
noncomputable def Am (f : 𝕋 → ℝ) : Fin 4 → ℂ := fun k => ∫ t, (f t : ℂ) * (h0 t * fourier (k : ℕ) t) ∂η

lemma mom_decomp {g : 𝕋 → ℂ} (hg : g ∈ Ball) :
    momV g = fun k => momV h0 k + Am (xf g) k + I * Am (yf g) k := by
  funext k
  simp only [momV, mom_eq, Am]
  have i1 := (xf_bm hg).integrable_mul (k := fun t => h0 t * fourier ((k : ℕ) : ℤ) t)
    (h0_cont.mul (fourier _).continuous)
  have i2 := (yf_bm hg).integrable_mul (k := fun t => h0 t * fourier ((k : ℕ) : ℤ) t)
    (h0_cont.mul (fourier _).continuous)
  have i0 : Integrable (fun t => fourier ((k : ℕ) : ℤ) t * h0 t) η :=
    integrable_cont ((fourier _).continuous.mul h0_cont)
  have key : (fun t => fourier ((k : ℕ) : ℤ) t * g t) = fun t =>
      (fourier ((k : ℕ) : ℤ) t * h0 t + (xf g t : ℂ) * (h0 t * fourier ((k : ℕ) : ℤ) t)) +
        I * ((yf g t : ℂ) * (h0 t * fourier ((k : ℕ) : ℤ) t)) := by
    funext t; rw [g_eq g t]; ring
  rw [key, integral_add, integral_add, integral_const_mul]
  · exact i0
  · exact i1
  · exact i0.add i1
  · exact i2.const_mul I

/-! ## The algebraic identity -/

lemma a0_vec : momV h0 = ![0, (r : ℂ), 2 / 3, -(2 * r / 3 : ℂ)] := momV_h0

lemma aorb_one : aorb 1 = momV h0 := by
  rw [a0_vec]; funext k; fin_cases k <;> simp [aorb]

lemma r_sq_C : (r : ℂ) ^ 2 = 1 / 3 := by
  have := congrArg (fun x : ℝ => (x : ℂ)) r_sq; push_cast at this; exact this

/-- `φ(a(h₀), A f) = -∫ ρ f`. -/
lemma fourier_nat_eq (j : ℕ) (t : 𝕋) : fourier (j : ℤ) t = zz t ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by push_cast; ring, fourier_add, ih, pow_succ]; rfl

lemma phiB_a0_Am {f : 𝕋 → ℝ} (hf : BddMeas f) :
    phiB (momV h0) (Am f) = -((∫ t, ρf t * f t ∂η : ℝ) : ℂ) := by
  have hi : ∀ j : ℕ, Integrable (fun t => (f t : ℂ) * (h0 t * fourier (j : ℤ) t)) η := fun j =>
    hf.integrable_mul (h0_cont.mul (fourier _).continuous)
  set F : ℕ → ℂ := fun j => ∫ t, (f t : ℂ) * (h0 t * fourier (j : ℤ) t) ∂η with hF
  have hAm : ∀ k : Fin 4, Am f k = F k := fun k => rfl
  -- ∫ f h₀ P = (-2r/3) F₀ + (-4/3) F₁ + (-2r) F₂
  have hsum : ∫ t, (f t : ℂ) * (h0 t * Pf t) ∂η = (-2 * r / 3 : ℂ) * F 0 + (-4 / 3 : ℂ) * F 1 + (-2 * r : ℂ) * F 2 := by
    have e : (fun t => (f t : ℂ) * (h0 t * Pf t)) = fun t =>
        ((-2 * r / 3 : ℂ) * ((f t : ℂ) * (h0 t * fourier ((0 : ℕ) : ℤ) t)) +
          (-4 / 3 : ℂ) * ((f t : ℂ) * (h0 t * fourier ((1 : ℕ) : ℤ) t))) +
          (-2 * r : ℂ) * ((f t : ℂ) * (h0 t * fourier ((2 : ℕ) : ℤ) t)) := by
      funext t
      simp only [fourier_nat_eq, Pf]
      have h2 := r_sq_C
      linear_combination ((-(4 : ℂ)) * (f t : ℂ) * h0 t * zz t - 2 * (f t : ℂ) * h0 t * r) * h2
    rw [e, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
    · exact (hi 0).const_mul _
    · exact (hi 1).const_mul _
    · exact ((hi 0).const_mul _).add ((hi 1).const_mul _)
    · exact (hi 2).const_mul _
  have hρ : ∫ t, (f t : ℂ) * (h0 t * Pf t) ∂η = -((∫ t, ρf t * f t ∂η : ℝ) : ℂ) := by
    have e : (fun t => (f t : ℂ) * (h0 t * Pf t)) = fun t => -(((ρf t * f t : ℝ)) : ℂ) := by
      funext t; rw [h0_P]; push_cast; ring
    rw [e, integral_neg]; congr 1; exact integral_ofReal
  rw [a0_vec]
  simp only [phiB, hAm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  norm_num
  rw [← hρ, hsum]
  ring

lemma qform_split (a u w : Fin 4 → ℂ) :
    qform (fun k => a k + u k + I * w k) =
      qform a + 2 * phiB a u + 2 * I * phiB a w + (qform u - qform w + 2 * I * phiB u w) := by
  simp only [qform, phiB]
  linear_combination (2 * w 0 * w 3 - 4 * w 1 * w 2) * Complex.I_sq

lemma phiB_split (a u w : Fin 4 → ℂ) :
    phiB (fun k => a k + u k + I * w k) a = qform a + phiB a u + I * phiB a w := by
  simp only [qform, phiB]; ring

/-- `X := M + Re φ(a(g), a(h₀)) = -∫ ρ x`. -/
lemma X_eq {g : 𝕋 → ℂ} (hg : g ∈ Ball) :
    Xslab (momV g) (aorb 1) = -∫ t, ρf t * xf g t ∂η := by
  rw [aorb_one, Xslab, mom_decomp hg, phiB_split, q_h0, phiB_a0_Am (xf_bm hg),
    phiB_a0_Am (yf_bm hg)]
  simp

/-- The basic identity. -/
lemma basic_identity {g : 𝕋 → ℂ} (hg : g ∈ Ball) :
    M + (qform (momV g)).re = 2 * (-∫ t, ρf t * xf g t ∂η) + (qform (Am (xf g))).re -
      (qform (Am (yf g))).re - 2 * (phiB (Am (xf g)) (Am (yf g))).im := by
  rw [mom_decomp hg, qform_split, q_h0, phiB_a0_Am (xf_bm hg), phiB_a0_Am (yf_bm hg)]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end Harris
