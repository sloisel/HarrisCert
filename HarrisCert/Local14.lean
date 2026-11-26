module

public import HarrisCert.Local13

/-!
# Local theorem, part 14: assembly

With `X = -∫ρx` and `ξ = ξ(y)`:
* `∫ρx² + ∫ρy² ≤ 2X` (the disc constraint);
* `ξᵀ Gᵢ ξ ≤ ∫ρy²` (Bessel);
* `Re q(Ax) ≥ -6 (X/m)²`;
* `-2 Im φ(Ax, Ay) = 2I` with `I = ∫ (-x) ρ t_w·ξ`, and `ξᵀHξ + 2I ≥ -Λ' X²` (core inequality, integrated);
* `|c_κ·ξ| ≤ √3 X` (alignment).
Hence `M + Re q ≥ 2εX - (Λ' + 6/m²) X² ≥ 0` for `X ≤ X₀`.
-/

open MeasureTheory Complex Matrix

@[expose] public section

namespace Harris

lemma ΓGi : Γr * Gir = 1 := by unfold Γr Gir; rw [← mR_mul, Γ_Gi, mR_one]

lemma Am_norm_le {g : 𝕋 → ℂ} (k : Fin 4) : ‖Am (xf g) k‖ ≤ ∫ t, |xf g t| ∂η := by
  unfold Am
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  congr 1; funext t
  rw [norm_mul, norm_mul, h0_norm, norm_fourier_apply, Complex.norm_real, Real.norm_eq_abs]; ring

lemma cont_twξ (ξ : Fin 7 → ℝ) : Continuous fun t => ρf t * (tw t ⬝ᵥ ξ) := by
  refine ρf_cont.mul ?_
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp tw_cont).mul continuous_const

section core

variable {g : 𝕋 → ℂ} (hg : g ∈ Ball)
include hg

lemma disc_int : ∫ t, ρf t * xf g t ^ 2 ∂η + ∫ t, ρf t * yf g t ^ 2 ∂η ≤ 2 * (-∫ t, ρf t * xf g t ∂η) := by
  have i1 := (xf_bm hg).integrable_cmul ρf_cont 2
  have i2 := (yf_bm hg).integrable_cmul ρf_cont 2
  have i3 : Integrable (fun t => ρf t * xf g t) η := by
    have := (xf_bm hg).integrable_cmul ρf_cont 1; simpa using this
  rw [← integral_add i1 i2, ← integral_neg, ← integral_const_mul]
  refine integral_mono (i1.add i2) (i3.neg.const_mul 2) fun t => ?_
  have hd := disc hg t
  have hp := ρf_pos t
  simp only [Pi.add_apply, Pi.neg_apply]
  nlinarith

lemma bessel_xi : ξf (yf g) ⬝ᵥ Gir *ᵥ ξf (yf g) ≤ ∫ t, ρf t * yf g t ^ 2 ∂η := by
  set ξ := ξf (yf g)
  set c := Gir *ᵥ ξ
  have h := bessel_rho (yf_bm hg) c
  have e1 : ∑ a, c a * ∫ t, yf g t * φb a t ∂η = ξ ⬝ᵥ Gir *ᵥ ξ := by
    simp only [← ξf_eq]; rw [dotProduct_comm]; rfl
  have e2 : ∑ a, ∑ b, c a * c b * σ (Γk a b) = ξ ⬝ᵥ Gir *ᵥ ξ := by
    have hΓc : Γr *ᵥ c = ξ := by rw [Matrix.mulVec_mulVec, ΓGi, Matrix.one_mulVec]
    have : ∑ a, ∑ b, c a * c b * σ (Γk a b) = c ⬝ᵥ Γr *ᵥ c := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
      show c a * c b * σ (Γk a b) = c a * (σ (Γk a b) * c b); ring
    rw [this, hΓc, dotProduct_comm]
  rw [e1, e2] at h
  linarith

lemma int_abs_le : 2 * r * (1 - r) ^ 2 * ∫ t, |xf g t| ∂η ≤ -∫ t, ρf t * xf g t ∂η := by
  have ia : Integrable (fun t => |xf g t|) η := by
    have := (xf_bm hg).integrable_cmul (k := fun _ => (1 : ℝ)) continuous_const 1
    simpa using this.abs
  have i3 : Integrable (fun t => ρf t * xf g t) η := by
    have := (xf_bm hg).integrable_cmul ρf_cont 1; simpa using this
  rw [← integral_const_mul, ← integral_neg]
  refine integral_mono (ia.const_mul _) i3.neg fun t => ?_
  have hx := xf_nonpos hg t
  have hm := ρf_ge t
  simp only
  rw [abs_of_nonpos hx]
  nlinarith

lemma qx_bound :
    -(6 * ((-∫ t, ρf t * xf g t ∂η) / (2 * r * (1 - r) ^ 2)) ^ 2) ≤ (qform (Am (xf g))).re := by
  set B := (-∫ t, ρf t * xf g t ∂η) / (2 * r * (1 - r) ^ 2)
  have hm : 0 < 2 * r * (1 - r) ^ 2 := by have := r_pos; have := r_lt_one; nlinarith [sq_pos_of_pos (sub_pos.mpr r_lt_one)]
  have hB : ∀ k, ‖Am (xf g) k‖ ≤ B := fun k => by
    refine le_trans (Am_norm_le k) ?_
    rw [le_div_iff₀ hm, mul_comm]; exact int_abs_le hg
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have h1 := le_trans (neg_le_neg (Complex.abs_re_le_norm (qform (Am (xf g))))) (neg_abs_le _)
  have h2 : ‖qform (Am (xf g))‖ ≤ 6 * B ^ 2 := by
    unfold qform
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    have := mul_le_mul (hB 0) (hB 3) (norm_nonneg _) hB0
    have := mul_le_mul (hB 1) (hB 2) (norm_nonneg _) hB0
    nlinarith [norm_nonneg (Am (xf g) 0), norm_nonneg (Am (xf g) 1)]
  linarith

lemma cross_rep : -2 * (phiB (Am (xf g)) (Am (yf g))).im =
    2 * ∫ t, -xf g t * (ρf t * (tw t ⬝ᵥ ξf (yf g))) ∂η := by
  rw [cross_eq (xf_bm hg) (yf_bm hg)]
  have e : (fun t => xf g t * (mt (zz t) ⬝ᵥ ξf (yf g) / ‖zz t + r‖ ^ 2)) =
      fun t => xf g t * (ρf t * (tw t ⬝ᵥ ξf (yf g))) := by
    funext t; rw [ρ_tw]
  rw [e]
  have e2 : ∫ t, -xf g t * (ρf t * (tw t ⬝ᵥ ξf (yf g))) ∂η =
      -∫ t, xf g t * (ρf t * (tw t ⬝ᵥ ξf (yf g))) ∂η := by
    rw [← integral_neg]; congr 1; funext t; ring
  rw [e2]; ring

lemma X_nonneg : 0 ≤ -∫ t, ρf t * xf g t ∂η := by
  have h := int_abs_le hg
  have hm : 0 ≤ 2 * r * (1 - r) ^ 2 := by have := r_pos; positivity
  have : 0 ≤ ∫ t, |xf g t| ∂η := integral_nonneg fun t => abs_nonneg _
  nlinarith

lemma align_bound (hmin : ∀ u : ℂ, ‖u‖ = 1 → Xslab (momV g) (aorb 1) ≤ Xslab (momV g) (aorb u)) :
    |cκr ⬝ᵥ ξf (yf g)| ≤ Real.sqrt 3 * (-∫ t, ρf t * xf g t ∂η) := by
  have h0 := deriv_zero (momV g) hmin
  rw [align_id hg] at h0
  have hc : Continuous fun t : 𝕋 => -(4 / 3) * (zz t).im :=
    continuous_const.mul (Complex.continuous_im.comp (fourier 1).continuous)
  have i1 := (xf_bm hg).integrable_mulR hc
  have i3 : Integrable (fun t => ρf t * xf g t) η := by
    have := (xf_bm hg).integrable_cmul ρf_cont 1; simpa using this
  have e : cκr ⬝ᵥ ξf (yf g) = -∫ t, xf g t * (-(4 / 3) * (zz t).im) ∂η := by linarith
  rw [e, abs_neg]
  refine le_trans (abs_integral_le_integral_abs) ?_
  have e2 : Real.sqrt 3 * (-∫ t, ρf t * xf g t ∂η) = ∫ t, Real.sqrt 3 * (-(ρf t * xf g t)) ∂η := by
    rw [integral_const_mul, integral_neg]
  rw [e2]
  refine integral_mono i1.abs (i3.neg.const_mul _) fun t => ?_
  have hx := xf_nonpos hg t
  have hb := IG_le t
  simp only
  rw [abs_mul, abs_of_nonpos hx, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4 / 3)]
  nlinarith [abs_nonneg (zz t).im]

/-- The integrated core inequality. -/
lemma core_int (hs : |cκr ⬝ᵥ ξf (yf g)| ≤ Real.sqrt 3 * (-∫ t, ρf t * xf g t ∂η)) :
    -(230 + (εR + 2) * 3 / κnR) * (-∫ t, ρf t * xf g t ∂η) ^ 2 ≤
      ξf (yf g) ⬝ᵥ Hr *ᵥ ξf (yf g) + 2 * ∫ t, -xf g t * (ρf t * (tw t ⬝ᵥ ξf (yf g))) ∂η := by
  set X := -∫ t, ρf t * xf g t ∂η with hXdef
  set ξ := ξf (yf g)
  set Λ' := 230 + (εR + 2) * 3 / κnR
  set Hq := ξ ⬝ᵥ Hr *ᵥ ξ
  have hX0 : 0 ≤ X := X_nonneg hg
  have hpt : ∀ t, -Λ' * X ^ 2 ≤ Hq + 2 * X * (tw t ⬝ᵥ ξ) := fun t =>
    core_ineq ξ (tw t) X 230 hX0 hs (tw_ξκ t) (tw_Λ t)
  set w : 𝕋 → ℝ := fun t => -xf g t * ρf t with hw
  have hw0 : ∀ t, 0 ≤ w t := fun t => by
    have := xf_nonpos hg t; have := ρf_pos t; simp only [hw]; nlinarith
  have iw : Integrable w η := by
    have := ((xf_bm hg).integrable_cmul ρf_cont 1).neg
    refine this.congr (Filter.Eventually.of_forall fun t => ?_); simp [hw]; ring
  have hwX : ∫ t, w t ∂η = X := by
    rw [hXdef, ← integral_neg]; congr 1; funext t; simp [hw]; ring
  have iK : Integrable (fun t => w t * (tw t ⬝ᵥ ξ)) η := by
    have := ((xf_bm hg).integrable_mulR (cont_twξ ξ)).neg
    refine this.congr (Filter.Eventually.of_forall fun t => ?_); simp [hw]; ring
  have hI : ∫ t, -xf g t * (ρf t * (tw t ⬝ᵥ ξ)) ∂η = ∫ t, w t * (tw t ⬝ᵥ ξ) ∂η := by
    congr 1; funext t; simp [hw]; ring
  rw [hI]
  set I := ∫ t, w t * (tw t ⬝ᵥ ξ) ∂η
  rcases eq_or_lt_of_le hX0 with hX | hX
  · -- X = 0
    have hq := hpt 0
    rw [← hX] at hq ⊢
    have hwz : w =ᵐ[η] 0 := by
      have := (integral_eq_zero_iff_of_nonneg hw0 iw).mp (by rw [hwX, ← hX])
      exact this
    have hIz : I = 0 := by
      have : (fun t => w t * (tw t ⬝ᵥ ξ)) =ᵐ[η] 0 := by
        filter_upwards [hwz] with t ht; simp [ht]
      simp only [I]; rw [integral_congr_ae this]; simp
    rw [hIz]; simp at hq ⊢; linarith
  · -- X > 0
    have hmono : ∫ t, w t * (-Λ' * X ^ 2) ∂η ≤ ∫ t, (Hq * w t + 2 * X * (w t * (tw t ⬝ᵥ ξ))) ∂η := by
      refine integral_mono (iw.mul_const _) ((iw.const_mul _).add (iK.const_mul _)) fun t => ?_
      have := mul_le_mul_of_nonneg_left (hpt t) (hw0 t)
      simp only; nlinarith
    rw [integral_mul_const, integral_add (iw.const_mul _) (iK.const_mul _), integral_const_mul,
      integral_const_mul, hwX] at hmono
    have : X * (-Λ' * X ^ 2) ≤ X * (Hq + 2 * I) := by linarith
    have := le_of_mul_le_mul_left this hX
    linarith

lemma Hq_eq (ξ : Fin 7 → ℝ) : ξ ⬝ᵥ Hr *ᵥ ξ = (1 - εR) * (ξ ⬝ᵥ Gir *ᵥ ξ) - ξ ⬝ᵥ D7r *ᵥ ξ := by
  rw [Hr_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]

end core

lemma sqrt3_bounds : 1.732 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 1.7321 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h0 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

lemma const_bound : 230 + (εR + 2) * 3 / κnR + 6 / (2 * r * (1 - r) ^ 2) ^ 2 ≤ 400 := by
  obtain ⟨s1, s2⟩ := sqrt3_bounds
  have hr : r = Real.sqrt 3 / 3 := rfl
  have r1 : 0.5773 ≤ r := by rw [hr]; linarith
  have r2 : r ≤ 0.57737 := by rw [hr]; linarith
  have hm1 : 0.42263 ≤ 1 - r := by linarith
  have hsq : 0.42263 ^ 2 ≤ (1 - r) ^ 2 := pow_le_pow_left₀ (by norm_num) hm1 2
  have hm : 0.2062 ≤ 2 * r * (1 - r) ^ 2 := by nlinarith
  have hm2 : 0.2062 ^ 2 ≤ (2 * r * (1 - r) ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
  have t2 : 6 / (2 * r * (1 - r) ^ 2) ^ 2 ≤ 6 / 0.2062 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm2
  have t1 : (εR + 2) * 3 / κnR ≤ 16.7 := by
    unfold εR κnR
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have : (6 : ℝ) / 0.2062 ^ 2 ≤ 141.2 := by norm_num
  linarith

/-- The local theorem, in the aligned form. -/
theorem localCore : LocalCore := by
  intro g hg hmin hXle
  have hXe := X_eq hg
  set X := -∫ t, ρf t * xf g t ∂η with hXdef
  have hX0 : 0 ≤ X := X_nonneg hg
  have hXle' : X ≤ 7 / 10000 := by
    rw [← hXe]; have : ((X0 : ℚ) : ℝ) = 7 / 10000 := by simp [X0]
    rw [← this]; exact hXle
  have bi := basic_identity hg
  rw [Q_eq (yf_bm hg)] at bi
  have hcr := cross_rep hg
  have hd := disc_int hg
  have hb := bessel_xi hg
  have hqx := qx_bound hg
  have hcore := core_int hg (align_bound hg hmin)
  have hH := Hq_eq hg (ξf (yf g))
  have hxx : 0 ≤ ∫ t, ρf t * xf g t ^ 2 ∂η :=
    integral_nonneg fun t => mul_nonneg (ρf_pos t).le (sq_nonneg _)
  have hc := const_bound
  have hε : εR = 7 / 50 := rfl
  set m := 2 * r * (1 - r) ^ 2
  have hmpos : 0 < m := by
    have := r_pos; have := r_lt_one; have : 0 < 1 - r := by linarith
    positivity
  set Λ' := 230 + (εR + 2) * 3 / κnR
  set K := 6 / m ^ 2
  have hqx' : -(K * X ^ 2) ≤ (qform (Am (xf g))).re := by
    have : 6 * (X / m) ^ 2 = K * X ^ 2 := by simp only [K]; field_simp
    linarith
  have hX2 : X ^ 2 ≤ 7 / 10000 * X := by nlinarith
  have hKX : (Λ' + K) * X ^ 2 ≤ 400 * X ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg X)
  -- M + Re q ≥ 2εX + ξᵀHξ + 2I - K X² ≥ 2εX - (Λ' + K) X² ≥ 0
  rw [hε] at hH
  nlinarith

/-- The local theorem. -/
theorem localThm : LocalThm := localThm_of_core localCore

end Harris
