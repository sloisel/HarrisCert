module

public import HarrisCert.CellsInst
public import HarrisCert.Sound

/-!
# From the circle to `t ∈ [-1,1]`

`N(γ) = (1/π) Σ_{σ=±1} ∫_{-1}^{1} |P_σ(t)| (1+t²)⁻⁴ dt`, via `θ = 2 arctan t` on the half circle
`|θ| ≤ π/2`, and `θ ↦ θ + π` for the other half.
-/

open Complex MeasureTheory intervalIntegral

@[expose] public section

namespace Harris

/-! ## Complex polynomial evaluation -/

noncomputable def cevalC (P : CPoly) (t : ℝ) : ℂ := ⟨peval P.1 t, peval P.2 t⟩

lemma cevalC_mul (a b : CPoly) (t : ℝ) : cevalC (cpMul a b) t = cevalC a t * cevalC b t := by
  apply Complex.ext <;> simp [cevalC, cpMul, peval_add, peval_mul, peval_scale] <;> ring

lemma cevalC_pow (p : CPoly) (t : ℝ) : ∀ n, cevalC (cpPow p n) t = cevalC p t ^ n
  | 0 => by apply Complex.ext <;> simp [cevalC, cpPow]
  | n + 1 => by rw [cpPow, cevalC_mul, cevalC_pow p t n]; ring

lemma cevalC_basis (k : ℕ) (t : ℝ) :
    cevalC (basisK k) t = (1 + (t : ℂ) * I) ^ (2 * k) * (1 + (t : ℂ) ^ 2) ^ (3 - k) := by
  have h1 : cevalC ([1], [0, 1]) t = 1 + (t : ℂ) * I := by apply Complex.ext <;> simp [cevalC]
  have h2 : cevalC ([1, 0, 1], []) t = 1 + (t : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [cevalC, pow_two]
  rw [basisK, cevalC_mul, cevalC_pow, cevalC_pow, h1, h2]

/-- The term added by `psigStep` for index `k`. -/
noncomputable def psigTerm (g : Array ℚ) (σ : ℚ) (t : ℝ) (k : ℕ) : ℂ :=
  (((σ ^ k : ℚ) : ℂ) * ⟨g.getD k 0, g.getD (k + 4) 0⟩) * cevalC (basisK k) t

lemma ratpow_re (σ : ℚ) (k : ℕ) : ((σ : ℂ) ^ k).re = (σ : ℝ) ^ k := by
  rw [show (σ : ℂ) = ((σ : ℝ) : ℂ) by simp, ← Complex.ofReal_pow, Complex.ofReal_re]

lemma ratpow_im (σ : ℚ) (k : ℕ) : ((σ : ℂ) ^ k).im = 0 := by
  rw [show (σ : ℂ) = ((σ : ℝ) : ℂ) by simp, ← Complex.ofReal_pow, Complex.ofReal_im]

lemma cevalC_step (g : Array ℚ) (σ : ℚ) (acc : CPoly) (k : ℕ) (t : ℝ) :
    cevalC (psigStep g σ acc k) t = cevalC acc t + psigTerm g σ t k := by
  apply Complex.ext <;> simp [cevalC, psigStep, psigTerm, peval_add, peval_scale, ratpow_re, ratpow_im] <;>
    ring

lemma cevalC_foldl (g : Array ℚ) (σ : ℚ) (t : ℝ) :
    ∀ (l : List ℕ) (acc : CPoly),
      cevalC (l.foldl (psigStep g σ) acc) t = cevalC acc t + (l.map (psigTerm g σ t)).sum
  | [], acc => by simp
  | k :: l, acc => by
    rw [List.foldl_cons, cevalC_foldl g σ t l, cevalC_step]; simp; ring

lemma cevalC_Psig (g : Array ℚ) (σ : ℚ) (t : ℝ) :
    cevalC (Psig g σ) t = ∑ k : Fin 4, ((σ : ℂ) ^ (k : ℕ) * gammaC g k) *
      ((1 + (t : ℂ) * I) ^ (2 * (k : ℕ)) * (1 + (t : ℂ) ^ 2) ^ (3 - (k : ℕ))) := by
  have h0 : cevalC (([], []) : CPoly) t = 0 := by apply Complex.ext <;> simp [cevalC]
  rw [Psig, cevalC_foldl, h0, zero_add]
  simp [List.range_succ, Fin.sum_univ_four, psigTerm, cevalC_basis, gammaC]
  ring

lemma peval_absSq (P : CPoly) (t : ℝ) : peval (absSq P) t = ‖cevalC P t‖ ^ 2 := by
  rw [absSq, peval_add, peval_mul, peval_mul, Complex.sq_norm, Complex.normSq_apply]
  simp [cevalC]

lemma sqrt_absSq (P : CPoly) (t : ℝ) : Real.sqrt (peval (absSq P) t) = ‖cevalC P t‖ := by
  rw [peval_absSq, Real.sqrt_sq (norm_nonneg _)]

lemma absSq_nonneg (P : CPoly) (t : ℝ) : 0 ≤ peval (absSq P) t := by
  rw [peval_absSq]; positivity

/-! ## The integrand on the circle -/

/-- `G_σ(θ) = |Σ_k σ^k γ_k (e^{iθ})^k|`. -/
noncomputable def Gfun (γ : Fin 4 → ℂ) (σ : ℂ) (θ : ℝ) : ℝ :=
  ‖∑ k : Fin 4, σ ^ (k : ℕ) * γ k * exp ((θ : ℂ) * I) ^ (k : ℕ)‖

lemma continuous_Gfun (γ : Fin 4 → ℂ) (σ : ℂ) : Continuous (Gfun γ σ) := by
  unfold Gfun; fun_prop

lemma exp_shift_pi (θ : ℝ) : exp (((θ + Real.pi : ℝ) : ℂ) * I) = -exp ((θ : ℂ) * I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring

lemma exp_shift_two_pi (θ : ℝ) : exp (((θ + 2 * Real.pi : ℝ) : ℂ) * I) = exp ((θ : ℂ) * I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  have : exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
    rw [show (((2 * Real.pi : ℝ) : ℂ) * I) = 2 * Real.pi * I by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  rw [this, mul_one]

lemma Gfun_shift (γ : Fin 4 → ℂ) (θ : ℝ) : Gfun γ 1 (θ + Real.pi) = Gfun γ (-1) θ := by
  unfold Gfun
  rw [exp_shift_pi]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [neg_pow, one_pow]; ring

lemma Gfun_periodic (γ : Fin 4 → ℂ) : Function.Periodic (Gfun γ 1) (2 * Real.pi) := by
  intro θ; unfold Gfun; rw [exp_shift_two_pi]

/-- `e^{2i arctan t} = (1+it)²/(1+t²)`. -/
lemma exp_two_arctan (t : ℝ) :
    exp (((2 * Real.arctan t : ℝ) : ℂ) * I) = (1 + (t : ℂ) * I) ^ 2 / (1 + (t : ℂ) ^ 2) := by
  have hss : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (1 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_arctan, div_pow, hss]
    field_simp; ring
  have hsn : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
    field_simp
    rw [hss]
  have hden : (1 + (t : ℂ) ^ 2) ≠ 0 := by
    have : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
  rw [eq_div_iff hden, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hsn]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `G_σ(2 arctan t) = |P_σ(t)| / (1+t²)³`. -/
lemma Gfun_arctan (g : Array ℚ) (σ : ℚ) (t : ℝ) :
    Gfun (gammaC g) σ (2 * Real.arctan t) = ‖cevalC (Psig g σ) t‖ / (1 + t ^ 2) ^ 3 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hden : (1 + (t : ℂ) ^ 2) ≠ 0 := by
    have : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast hpos.ne'
  unfold Gfun
  rw [exp_two_arctan, cevalC_Psig]
  have hsum : ∑ k : Fin 4, (σ : ℂ) ^ (k : ℕ) * gammaC g k *
      ((1 + (t : ℂ) * I) ^ 2 / (1 + (t : ℂ) ^ 2)) ^ (k : ℕ) =
      (∑ k : Fin 4, ((σ : ℂ) ^ (k : ℕ) * gammaC g k) *
        ((1 + (t : ℂ) * I) ^ (2 * (k : ℕ)) * (1 + (t : ℂ) ^ 2) ^ (3 - (k : ℕ)))) /
        (1 + (t : ℂ) ^ 2) ^ 3 := by
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two]
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h3]
    field_simp
    ring
  rw [hsum, norm_div, norm_pow]
  congr 1
  rw [show (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg hpos.le]

/-- Change of variables on the right half circle. -/
lemma half_circle (g : Array ℚ) (σ : ℚ) :
    ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Gfun (gammaC g) σ θ =
      2 * ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g σ)) t) * wfun t := by
  have hderiv : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun t => 2 * Real.arctan t) (2 * (1 / (1 + x ^ 2))) x :=
    fun x _ => (Real.hasDerivAt_arctan x).const_mul 2
  have hcont : ContinuousOn (fun x : ℝ => 2 * (1 / (1 + x ^ 2))) (Set.uIcc (-1 : ℝ) 1) := by
    apply Continuous.continuousOn
    exact continuous_const.mul (continuous_const.div (continuous_const.add (continuous_pow 2))
      (fun x => (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)))
  have hcv := intervalIntegral.integral_comp_mul_deriv hderiv hcont (continuous_Gfun (gammaC g) σ)
  have ha : 2 * Real.arctan (-1) = -(Real.pi / 2) := by rw [Real.arctan_neg, Real.arctan_one]; ring
  have hb : 2 * Real.arctan 1 = Real.pi / 2 := by rw [Real.arctan_one]; ring
  simp only [ha, hb] at hcv
  rw [← hcv, ← intervalIntegral.integral_const_mul]
  congr 1; funext t
  simp only [Function.comp_apply, Gfun_arctan, sqrt_absSq, wfun]
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp

/-- `N(γ) = (1/π) (∫ √Q₊ w + ∫ √Q₋ w)`. -/
lemma Nsupp_eq (g : Array ℚ) :
    Nsupp (gammaC g) = (1 / Real.pi) *
      ((∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g 1)) t) * wfun t) +
       ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g (-1))) t) * wfun t) := by
  have hpi := Real.pi_pos
  set G := Gfun (gammaC g) 1 with hG
  have hF : (fun θ : ℝ => ‖∑ k : Fin 4, gammaC g k * exp ((θ : ℂ) * I) ^ (k : ℕ)‖) = G := by
    funext θ; simp [hG, Gfun]
  have hc : Continuous G := continuous_Gfun (gammaC g) 1
  have hper : ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ =
      ∫ θ in (-(Real.pi / 2))..(-(Real.pi / 2) + 2 * Real.pi), G θ := by
    have := (Gfun_periodic (gammaC g)).intervalIntegral_add_eq 0 (-(Real.pi / 2))
    rw [zero_add] at this; exact this
  have hsplit : ∫ θ in (-(Real.pi / 2))..(-(Real.pi / 2) + 2 * Real.pi), G θ =
      (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), G θ) +
        ∫ θ in (Real.pi / 2)..(-(Real.pi / 2) + 2 * Real.pi), G θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  have h2 : ∫ θ in (Real.pi / 2)..(-(Real.pi / 2) + 2 * Real.pi), G θ =
      ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Gfun (gammaC g) (-1) θ := by
    have := intervalIntegral.integral_comp_add_right G Real.pi
      (a := -(Real.pi / 2)) (b := Real.pi / 2)
    rw [show -(Real.pi / 2) + Real.pi = Real.pi / 2 by ring,
      show Real.pi / 2 + Real.pi = -(Real.pi / 2) + 2 * Real.pi by ring] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [hG, Gfun_shift]
  have e1 : ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), G θ =
      2 * ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g 1)) t) * wfun t := by
    rw [hG, ← half_circle g 1]
    apply intervalIntegral.integral_congr
    intro θ _
    simp [Gfun]
  have e2 := half_circle g (-1)
  have e2' : ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Gfun (gammaC g) (-1) θ =
      2 * ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g (-1))) t) * wfun t := by
    rw [← e2]
    apply intervalIntegral.integral_congr
    intro θ _
    simp [Gfun]
  unfold Nsupp
  rw [hF, hper, hsplit, h2, e1, e2']
  field_simp

end Harris
