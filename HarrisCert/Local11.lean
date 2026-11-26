module

public import HarrisCert.Local10

/-!
# Local theorem, part 11: coordinates, the relation for `β₁`, `Q(y) = ξᵀD₇ξ`, the cross term

For a bounded real `y`, `α_k = ∫ y Re(h₀ z^k)`, `β_k = ∫ y Im(h₀ z^k)`, `A(y)_k = α_k + i β_k`, and
`ξ(y) = (α₀, α₁, α₂, α₃, β₀, β₂, β₃)`. The pointwise identity `Im(h₀ (z + r)²) = 0` gives
`β₁ = -(r/2) β₀ - (3r/2) β₂`.
-/

open MeasureTheory Complex Matrix

@[expose] public section

namespace Harris

noncomputable def αf (y : 𝕋 → ℝ) (k : ℕ) : ℝ := ∫ t, y t * (hzk k t).re ∂η
noncomputable def βf (y : 𝕋 → ℝ) (k : ℕ) : ℝ := ∫ t, y t * (hzk k t).im ∂η

noncomputable def ξf (y : 𝕋 → ℝ) : Fin 7 → ℝ :=
  ![αf y 0, αf y 1, αf y 2, αf y 3, βf y 0, βf y 2, βf y 3]

lemma ξf_eq (y : 𝕋 → ℝ) (a : Fin 7) : ξf y a = ∫ t, y t * φb a t ∂η := by
  fin_cases a <;> simp [ξf, αf, βf, φb, bim, bj]

lemma Am_eq {y : 𝕋 → ℝ} (hy : BddMeas y) (k : Fin 4) : Am y k = ⟨αf y k, βf y k⟩ := by
  have hi := hy.integrable_mul (k := hzk k) (hzk_cont k)
  apply Complex.ext
  · have h := integral_re hi; simp only [RCLike.re_to_complex] at h
    show (∫ t, (y t : ℂ) * hzk (k : ℕ) t ∂η).re = _
    rw [← h]; simp; rfl
  · have h := integral_im hi; simp only [RCLike.im_to_complex] at h
    show (∫ t, (y t : ℂ) * hzk (k : ℕ) t ∂η).im = _
    rw [← h]; simp; rfl

lemma hzk_eq (k : ℕ) (t : 𝕋) : hzk k t = h0 t * zz t ^ k := by rw [hzk, fourier_nat_eq]

/-- `h₀ (z + r)² = |z + r|²`. -/
lemma h0_sq (t : 𝕋) : h0 t * (zz t + r) ^ 2 = ((‖zz t + r‖ ^ 2 : ℝ) : ℂ) := by
  have e : (zz t + r) * h0 t = (starRingEnd ℂ) (zz t + r) := by
    rw [map_add, Complex.conj_ofReal, conj_zz]; exact h0_eq t
  rw [Complex.ofReal_pow, ← Complex.mul_conj', sq]
  calc h0 t * ((zz t + r) * (zz t + r)) = (zz t + r) * ((zz t + r) * h0 t) := by ring
    _ = _ := by rw [e]

lemma beta1_pw (t : 𝕋) :
    (hzk 1 t).im = -(r / 2) * (hzk 0 t).im - 3 * r / 2 * (hzk 2 t).im := by
  have hr := r_sq_C
  have e : (r / 2 : ℂ) * hzk 0 t + hzk 1 t + 3 * r / 2 * hzk 2 t =
      ((3 * r / 2 * ‖zz t + r‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← h0_sq t]
    simp only [hzk_eq]
    push_cast
    linear_combination (-3 * h0 t * zz t - 3 * (r : ℂ) / 2 * h0 t) * hr
  have h := congrArg Complex.im e
  rw [Complex.ofReal_im] at h
  simp [Complex.mul_im] at h
  linarith

lemma hzk_cont_re (k : ℕ) : Continuous fun t => (hzk k t).re := Complex.continuous_re.comp (hzk_cont k)
lemma hzk_cont_im (k : ℕ) : Continuous fun t => (hzk k t).im := Complex.continuous_im.comp (hzk_cont k)

lemma beta1 {y : 𝕋 → ℝ} (hy : BddMeas y) : βf y 1 = -(r / 2) * βf y 0 - 3 * r / 2 * βf y 2 := by
  have i0 := hy.integrable_mulR (hzk_cont_im 0)
  have i2 := hy.integrable_mulR (hzk_cont_im 2)
  have e : (fun t => y t * (hzk 1 t).im) =
      fun t => -(r / 2) * (y t * (hzk 0 t).im) - 3 * r / 2 * (y t * (hzk 2 t).im) := by
    funext t; rw [beta1_pw]; ring
  unfold βf; rw [e, integral_sub (i0.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]

lemma σR_mk' (p q : ℚ) : σR (⟨p, q⟩ : K3) = p + q * (3 * r) := by rw [σR_mk, sqrt3_eq]

lemma D7_quad (ξ : Fin 7 → ℝ) : ξ ⬝ᵥ D7r *ᵥ ξ =
    2 * ξ 0 * ξ 3 - 4 * ξ 1 * ξ 2 - 2 * r * ξ 4 * ξ 5 - 2 * ξ 4 * ξ 6 - 6 * r * ξ 5 ^ 2 := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_seven, D7r, mR, D7m, σ_mk, σ_two]
  ring

/-- `Re q(A y) = ξᵀ D₇ ξ`. -/
lemma Q_eq {y : 𝕋 → ℝ} (hy : BddMeas y) : (qform (Am y)).re = ξf y ⬝ᵥ D7r *ᵥ ξf y := by
  rw [D7_quad]
  have hb := beta1 hy
  simp only [qform, Am_eq hy]
  simp [ξf, Complex.mul_re, Complex.mul_im]
  rw [hb]; ring

/-- `h₀ = (z̄ + r)² / |z + r|²`. -/
lemma h0_cv (t : 𝕋) : h0 t = ((starRingEnd ℂ) (zz t) + r) ^ 2 / ((‖zz t + r‖ ^ 2 : ℝ) : ℂ) := by
  have hN : ((‖zz t + r‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := norm_pos_iff.mpr (den_ne t); exact_mod_cast (pow_pos this 2).ne'
  rw [eq_div_iff hN, ← h0_sq t]
  have e : (zz t + r) * h0 t = (starRingEnd ℂ) (zz t) + r := by rw [conj_zz]; exact h0_eq t
  calc h0 t * (h0 t * (zz t + ↑r) ^ 2) = h0 t * ((zz t + r) * h0 t) * (zz t + r) := by ring
    _ = h0 t * ((starRingEnd ℂ) (zz t) + r) * (zz t + r) := by rw [e]
    _ = ((starRingEnd ℂ) (zz t) + r) * ((zz t + r) * h0 t) := by ring
    _ = _ := by rw [e]; ring

lemma cvec0 (z : ℂ) : cvec z 0 = ((starRingEnd ℂ) z + r) ^ 2 * z ^ 3 := rfl
lemma cvec1 (z : ℂ) : cvec z 1 = ((starRingEnd ℂ) z + r) ^ 2 * (-2 * z ^ 2) := rfl
lemma cvec2 (z : ℂ) : cvec z 2 = ((starRingEnd ℂ) z + r) ^ 2 * (-2 * z) := rfl
lemma cvec3 (z : ℂ) : cvec z 3 = ((starRingEnd ℂ) z + r) ^ 2 := rfl

lemma cross_pw (t : 𝕋) (b : Fin 4 → ℂ) (hb : (b 1).im = -(r / 2) * (b 0).im - 3 * r / 2 * (b 2).im) :
    (h0 t * (b 3 + zz t * (-2 * b 2) + zz t ^ 2 * (-2 * b 1) + zz t ^ 3 * b 0)).im =
      mt (zz t) ⬝ᵥ ![(b 0).re, (b 1).re, (b 2).re, (b 3).re, (b 0).im, (b 2).im, (b 3).im] /
        ‖zz t + r‖ ^ 2 := by
  rw [h0_cv]
  set N := ‖zz t + r‖ ^ 2
  have e : ((starRingEnd ℂ) (zz t) + r) ^ 2 / (N : ℂ) *
      (b 3 + zz t * (-2 * b 2) + zz t ^ 2 * (-2 * b 1) + zz t ^ 3 * b 0) =
      (cvec (zz t) 0 * b 0 + cvec (zz t) 1 * b 1 + cvec (zz t) 2 * b 2 + cvec (zz t) 3 * b 3) / (N : ℂ) := by
    rw [cvec0, cvec1, cvec2, cvec3]
    ring
  rw [e, Complex.div_ofReal_im]
  congr 1
  simp only [Complex.add_im, Complex.mul_im, mt, dotProduct, Fin.sum_univ_seven]
  simp
  rw [hb]; ring

lemma integrable_xF {x : 𝕋 → ℝ} (hx : BddMeas x) {F : 𝕋 → ℂ} (hF : Continuous F) :
    Integrable (fun t => (x t : ℂ) * F t) η := hx.integrable_mul hF

/-- The cross term. -/
lemma cross_eq {x y : 𝕋 → ℝ} (hx : BddMeas x) (hy : BddMeas y) :
    (phiB (Am x) (Am y)).im = ∫ t, x t * (mt (zz t) ⬝ᵥ ξf y / ‖zz t + r‖ ^ 2) ∂η := by
  set b := Am y
  have hzc : Continuous zz := (fourier 1).continuous
  have hF : Continuous fun t => h0 t * (b 3 + zz t * (-2 * b 2) + zz t ^ 2 * (-2 * b 1) + zz t ^ 3 * b 0) :=
    h0_cont.mul (by fun_prop)
  set G : ℕ → 𝕋 → ℂ := fun k t => (x t : ℂ) * (h0 t * fourier (k : ℤ) t) with hG
  have hi : ∀ k : ℕ, Integrable (G k) η := fun k =>
    integrable_xF hx (h0_cont.mul (fourier _).continuous)
  have hA : ∀ k : Fin 4, Am x k = ∫ t, G k t ∂η := fun k => rfl
  have e1 : phiB (Am x) b = ∫ t, (x t : ℂ) *
      (h0 t * (b 3 + zz t * (-2 * b 2) + zz t ^ 2 * (-2 * b 1) + zz t ^ 3 * b 0)) ∂η := by
    have e : (fun t => (x t : ℂ) * (h0 t * (b 3 + zz t * (-2 * b 2) + zz t ^ 2 * (-2 * b 1) + zz t ^ 3 * b 0)))
        = fun t => ((G 0 t * b 3 + G 1 t * (-2 * b 2)) + G 2 t * (-2 * b 1)) + G 3 t * b 0 := by
      funext t; simp only [hG, fourier_nat_eq]; ring
    have j0 := (hi 0).mul_const (b 3)
    have j1 := (hi 1).mul_const (-2 * b 2)
    have j2 := (hi 2).mul_const (-2 * b 1)
    have j3 := (hi 3).mul_const (b 0)
    rw [e, integral_add, integral_add, integral_add, integral_mul_const, integral_mul_const,
      integral_mul_const, integral_mul_const]
    rotate_left
    · exact j0
    · exact j1
    · exact j0.add j1
    · exact j2
    · exact (j0.add j1).add j2
    · exact j3
    unfold phiB
    rw [hA 0, hA 1, hA 2, hA 3]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
    ring
  rw [e1]
  have h := integral_im (integrable_xF hx hF)
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  congr 1; funext t
  have hv : ![(b 0).re, (b 1).re, (b 2).re, (b 3).re, (b 0).im, (b 2).im, (b 3).im] = ξf y := by
    funext i; fin_cases i <;> simp [ξf, b, Am_eq hy]
  rw [Complex.im_ofReal_mul, cross_pw t b]
  · rw [hv]
  · simp only [b, Am_eq hy]; exact beta1 hy

/-- `h₀ (r + 2z/3 - r z²) = z̄ - z/3`. -/
lemma IG_pw (t : 𝕋) : h0 t * (r + 2 / 3 * zz t - r * zz t ^ 2) = (starRingEnd ℂ) (zz t) - zz t / 3 := by
  have e : (zz t + r) * h0 t = (starRingEnd ℂ) (zz t) + r := by rw [conj_zz]; exact h0_eq t
  have hz := zz_mul_conj t
  have hd : zz t + (r : ℂ) ≠ 0 := den_ne t
  have hr := r_sq_C
  apply mul_left_cancel₀ hd
  calc (zz t + r) * (h0 t * (r + 2 / 3 * zz t - r * zz t ^ 2))
      = ((zz t + r) * h0 t) * (r + 2 / 3 * zz t - r * zz t ^ 2) := by ring
    _ = _ := by
      rw [e]
      linear_combination (-1 / 3 - r * zz t) * hz + (1 - zz t ^ 2) * hr

lemma im_bound (z : ℂ) (hz : ‖z‖ = 1) : 2 / 3 * |z.im| ≤ ‖z + r‖ ^ 2 := by
  have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z; rw [hz, Complex.normSq_apply] at this; nlinarith
  have hn : ‖z + r‖ ^ 2 = (z.re + r) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hr := r_sq
  have hr0 := r_pos
  have hre : -1 ≤ z.re := by nlinarith
  rw [hn]
  rcases abs_cases z.im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg (2 * z.re + 3 * r), sq_nonneg (z.im - 2 * (z.re + r) ^ 2), sq_nonneg (z.im + 1)]

end Harris
