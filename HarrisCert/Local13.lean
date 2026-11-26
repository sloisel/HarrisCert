module

public import HarrisCert.Local12

/-!
# Local theorem, part 13: alignment

* `Im(r a₀ + (2/3) a₁ - r a₂) = c_κ·ξ(y) - (4/3) ∫ x Im z` for `a = a(g)`;
* at a minimizer over the unit circle of `u ↦ X(a, aorb u)` this imaginary part vanishes;
* by rotating, the local theorem reduces to the case where the minimum is attained at `u = 1`.
-/

open MeasureTheory Complex Matrix

@[expose] public section

namespace Harris

lemma IG_im (t : 𝕋) :
    r * (hzk 0 t).im + 2 / 3 * (hzk 1 t).im - r * (hzk 2 t).im = -(4 / 3) * (zz t).im := by
  have h := congrArg Complex.im (IG_pw t)
  have e : h0 t * (r + 2 / 3 * zz t - r * zz t ^ 2) = (r : ℂ) * hzk 0 t + 2 / 3 * hzk 1 t - r * hzk 2 t := by
    simp only [hzk_eq]; ring
  rw [e] at h
  simp [Complex.mul_im] at h
  linarith

lemma align_id {g : 𝕋 → ℂ} (hg : g ∈ Ball) :
    ((r : ℂ) * momV g 0 + 2 / 3 * momV g 1 - r * momV g 2).im =
      cκr ⬝ᵥ ξf (yf g) + ∫ t, xf g t * (-(4 / 3) * (zz t).im) ∂η := by
  have hx := xf_bm hg
  have hy := yf_bm hg
  have hdec := mom_decomp hg
  have e0 : momV g 0 = momV h0 0 + Am (xf g) 0 + I * Am (yf g) 0 := congrFun hdec 0
  have e1 : momV g 1 = momV h0 1 + Am (xf g) 1 + I * Am (yf g) 1 := congrFun hdec 1
  have e2 : momV g 2 = momV h0 2 + Am (xf g) 2 + I * Am (yf g) 2 := congrFun hdec 2
  rw [e0, e1, e2, a0_vec, Am_eq hx, Am_eq hx, Am_eq hx, Am_eq hy, Am_eq hy, Am_eq hy, cκr_vals]
  have i0 := hx.integrable_mulR (hzk_cont_im 0)
  have i1 := hx.integrable_mulR (hzk_cont_im 1)
  have i2 := hx.integrable_mulR (hzk_cont_im 2)
  have hint : ∫ t, xf g t * (-(4 / 3) * (zz t).im) ∂η =
      r * βf (xf g) 0 + 2 / 3 * βf (xf g) 1 - r * βf (xf g) 2 := by
    have e : (fun t => xf g t * (-(4 / 3) * (zz t).im)) = fun t =>
        (r * (xf g t * (hzk 0 t).im) + 2 / 3 * (xf g t * (hzk 1 t).im)) - r * (xf g t * (hzk 2 t).im) := by
      funext t; rw [← IG_im t]; ring
    unfold βf
    have j01 : Integrable (fun t => r * (xf g t * (hzk 0 t).im) + 2 / 3 * (xf g t * (hzk 1 t).im)) η :=
      (i0.const_mul _).add (i1.const_mul _)
    have j0 : Integrable (fun t => r * (xf g t * (hzk 0 t).im)) η := i0.const_mul _
    have j1 : Integrable (fun t => 2 / 3 * (xf g t * (hzk 1 t).im)) η := i1.const_mul _
    have j2 : Integrable (fun t => r * (xf g t * (hzk 2 t).im)) η := i2.const_mul _
    rw [e, integral_sub j01 j2, integral_add j0 j1, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [hint]
  simp [ξf, dotProduct, Fin.sum_univ_seven, Complex.mul_im]
  ring

/-! ## The vanishing derivative -/

lemma hasDerivAt_E (c : ℂ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => exp ((x : ℂ) * c)) (exp ((θ : ℂ) * c) * c) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const c).cexp
  simpa using h

lemma deriv_zero (a : Fin 4 → ℂ)
    (hmin : ∀ u : ℂ, ‖u‖ = 1 → Xslab a (aorb 1) ≤ Xslab a (aorb u)) :
    ((r : ℂ) * a 0 + 2 / 3 * a 1 - r * a 2).im = 0 := by
  set G : ℝ → ℂ := fun x => -(2 * r / 3 : ℂ) * a 0 * exp ((x : ℂ) * (-3 * I)) -
    (4 / 3 : ℂ) * a 1 * exp ((x : ℂ) * (-I)) - 2 * r * a 2 * exp ((x : ℂ) * I) with hG
  have hGd : HasDerivAt G (-(2 * r / 3 : ℂ) * a 0 * (exp ((0 : ℝ) * (-3 * I)) * (-3 * I)) -
      (4 / 3 : ℂ) * a 1 * (exp ((0 : ℝ) * (-I)) * (-I)) - 2 * r * a 2 * (exp ((0 : ℝ) * I) * I)) 0 :=
    (((hasDerivAt_E _ 0).const_mul _).sub ((hasDerivAt_E _ 0).const_mul _)).sub
      ((hasDerivAt_E _ 0).const_mul _)
  have hFd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hGd).const_add M
  have hF : ∀ x : ℝ, Xslab a (aorb (exp ((x : ℂ) * I))) = M + Complex.reCLM (G x) := by
    intro x
    have hc : (starRingEnd ℂ) (exp ((x : ℂ) * I)) = exp ((x : ℂ) * (-I)) := by
      rw [← Complex.exp_conj]; simp
    have h3 : exp ((x : ℂ) * (-I)) ^ 3 = exp ((x : ℂ) * (-3 * I)) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have a1 : aorb (exp ((x : ℂ) * I)) 1 = r * exp ((x : ℂ) * I) := rfl
    have a2 : aorb (exp ((x : ℂ) * I)) 2 = 2 / 3 * (starRingEnd ℂ) (exp ((x : ℂ) * I)) := rfl
    have a3 : aorb (exp ((x : ℂ) * I)) 3 = -(2 * r / 3) * (starRingEnd ℂ) (exp ((x : ℂ) * I)) ^ 3 := rfl
    have a0 : aorb (exp ((x : ℂ) * I)) 0 = 0 := rfl
    simp only [Xslab, phiB, a0, a1, a2, a3, hc, h3, Complex.reCLM_apply, hG]
    congr 1; congr 1; ring
  have hmin' : IsLocalMin (fun x : ℝ => M + Complex.reCLM (G x)) 0 := by
    refine Filter.Eventually.of_forall fun x => ?_
    simp only
    rw [← hF, ← hF]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    exact hmin _ (Complex.norm_exp_ofReal_mul_I x)
  have h0 := hmin'.hasDerivAt_eq_zero hFd
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul] at h0
  simp [Complex.mul_re, Complex.mul_im] at h0 ⊢
  linarith

/-! ## Reduction to an aligned minimizer -/

def LocalCore : Prop :=
  ∀ g ∈ Ball, (∀ u : ℂ, ‖u‖ = 1 → Xslab (momV g) (aorb 1) ≤ Xslab (momV g) (aorb u)) →
    Xslab (momV g) (aorb 1) ≤ X0 → -M ≤ (qform (momV g)).re

lemma aorb_cont : Continuous aorb := by
  refine continuous_pi fun k => ?_
  fin_cases k <;> simp only [aorb] <;> fun_prop

theorem localThm_of_core (hC : LocalCore) : LocalThm := by
  intro f hf u0 hu0 hX
  set F : ℂ → ℝ := fun u => Xslab (momV f) (aorb u) with hFdef
  have hFc : Continuous F := by
    simp only [hFdef, Xslab, phiB]
    have := aorb_cont
    fun_prop
  have hS : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hu0S : u0 ∈ Metric.sphere (0 : ℂ) 1 := by simpa using hu0
  obtain ⟨us, husS, hmin⟩ := hS.exists_isMinOn ⟨u0, hu0S⟩ hFc.continuousOn
  have hus : ‖us‖ = 1 := by simpa using husS
  set w := (starRingEnd ℂ) us with hw
  have hwn : ‖w‖ = 1 := by rw [hw, RCLike.norm_conj, hus]
  set β : ℝ := 2 * arg w
  have hv : exp (((β / 2 : ℝ) : ℂ) * I) = w := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hwn, Complex.ofReal_one, one_mul] at this
    have hb : β / 2 = arg w := by simp only [β]; ring
    rw [hb]; exact this
  have hvinv : w⁻¹ = us := by
    rw [hw, conj_eq_inv hus, inv_inv]
  set g := rot β f
  have hg : g ∈ Ball := rot_mem hf β
  have hmg : momV g = rotV w (momV f) := by rw [momV_rot, hv]
  have hXg : ∀ u : ℂ, ‖u‖ = 1 → Xslab (momV g) (aorb u) = F (u * us) := by
    intro u hu
    rw [hmg, Xslab, phiB_rotV w u hwn hu, hvinv]; rfl
  have hq : qform (momV g) = qform (momV f) := by rw [hmg, qform_rotV w hwn]
  have h1 := hXg 1 (by simp)
  rw [one_mul] at h1
  rw [← hq]
  refine hC g hg (fun u hu => ?_) ?_
  · rw [h1, hXg u hu]
    have hm : u * us ∈ Metric.sphere (0 : ℂ) 1 := by simp [norm_mul, hu, hus]
    exact hmin hm
  · rw [h1]; exact le_trans (hmin hu0S) hX

end Harris
