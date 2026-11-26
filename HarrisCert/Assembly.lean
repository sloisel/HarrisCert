module

public import HarrisCert.Bridge3
public import HarrisCert.GlobalStep

/-!
# Assembly: `sup |φ| = 2` and `sup |q| = M`, given the local theorem

`LocalThm` is Theorem 8 of `harris_sharp.tex` in moment form; it is proved in `Local*.lean`.
-/

open MeasureTheory Complex

@[expose] public section

namespace Harris

/-- The local theorem: near the orbit of `h₀` (in the sense of the slab functional), `Re q ≥ -M`. -/
def LocalThm : Prop :=
  ∀ f ∈ Ball, ∀ u : ℂ, ‖u‖ = 1 → Xslab (momV f) (aorb u) ≤ X0 → -M ≤ (qform (momV f)).re

/-! ## Algebra of the symmetries on moment vectors -/

lemma momV_reflF (f : 𝕋 → ℂ) : momV (reflF f) = refl (momV f) := by
  funext k
  fin_cases k <;> simp [momV, refl, mom_reflF, Fin.rev]

lemma phiB_refl (a b : Fin 4 → ℂ) : phiB (refl a) b = (starRingEnd ℂ) (phiB a (refl b)) := by
  simp [phiB, refl, Fin.rev, map_add, map_sub, map_mul, map_ofNat]; ring

lemma qform_refl (a : Fin 4 → ℂ) : qform (refl a) = (starRingEnd ℂ) (qform a) := by
  simp [qform, refl, Fin.rev, map_sub, map_mul, map_ofNat]; ring

/-- Moments transformed by the rotation with `v = e^{iβ/2}`. -/
noncomputable def rotV (v : ℂ) (a : Fin 4 → ℂ) : Fin 4 → ℂ := fun k => v ^ 3 * (v⁻¹) ^ (2 * (k : ℕ)) * a k

lemma conj_eq_inv {v : ℂ} (hv : ‖v‖ = 1) : (starRingEnd ℂ) v = v⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hv]; simp

lemma ne_zero_of_norm {v : ℂ} (hv : ‖v‖ = 1) : v ≠ 0 := by
  intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv

lemma phiB_rotV (v u : ℂ) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (a : Fin 4 → ℂ) :
    phiB (rotV v a) (aorb u) = phiB a (aorb (u * v⁻¹)) := by
  have hv0 := ne_zero_of_norm hv
  have hu' : ‖u * v⁻¹‖ = 1 := by rw [norm_mul, norm_inv, hu, hv]; norm_num
  simp only [phiB, rotV, aorb]
  rw [conj_eq_inv hu, conj_eq_inv hu']
  simp [Fin.isValue]
  field_simp
  all_goals ring

lemma refl_aorb (u : ℂ) :
    refl (aorb u) = ![-(2 * r / 3 : ℂ) * u ^ 3, (2 / 3 : ℂ) * u, (r : ℂ) * (starRingEnd ℂ) u, 0] := by
  funext k
  fin_cases k <;> simp [refl, aorb, Fin.rev, map_ofNat, Complex.conj_ofReal] <;> ring

lemma phiB_rotV_refl (v u : ℂ) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (a : Fin 4 → ℂ) :
    phiB (rotV v a) (refl (aorb u)) = phiB a (refl (aorb (u * v⁻¹))) := by
  have hv0 := ne_zero_of_norm hv
  have hu' : ‖u * v⁻¹‖ = 1 := by rw [norm_mul, norm_inv, hu, hv]; norm_num
  have hinv : ‖u⁻¹‖ = 1 := by rw [norm_inv, hu]; norm_num
  have hinv' : ‖(u * v⁻¹)⁻¹‖ = 1 := by rw [norm_inv, hu']; norm_num
  rw [refl_aorb, refl_aorb]
  simp only [phiB, rotV]
  rw [conj_eq_inv hu, conj_eq_inv hu']
  simp [Fin.isValue]
  field_simp
  all_goals ring

lemma qform_rotV (v : ℂ) (hv : ‖v‖ = 1) (a : Fin 4 → ℂ) : qform (rotV v a) = qform a := by
  have hv0 := ne_zero_of_norm hv
  simp only [qform, rotV]
  simp [Fin.isValue]
  field_simp
  all_goals ring

lemma momV_rot (f : 𝕋 → ℂ) (β : ℝ) :
    momV (rot β f) = rotV (exp (((β / 2 : ℝ) : ℂ) * I)) (momV f) := by
  funext k
  simp only [momV, rotV, mom_rot]
  have h3 : exp (((3 * β / 2 : ℝ) : ℂ) * I) = exp (((β / 2 : ℝ) : ℂ) * I) ^ 3 := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have h2 : exp (-((β : ℂ) * I)) = (exp (((β / 2 : ℝ) : ℂ) * I))⁻¹ ^ 2 := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [h3, h2, ← pow_mul]

/-! ## The lower bound `Re q ≥ -M` -/

theorem lower_bound (hL : LocalThm) {f : 𝕋 → ℂ} (hf : f ∈ Ball) : -M ≤ (qform (momV f)).re := by
  by_cases h1 : ∃ u : ℂ, ‖u‖ = 1 ∧ Xslab (momV f) (aorb u) ≤ X0
  · obtain ⟨u, hu, hX⟩ := h1; exact hL f hf u hu hX
  by_cases h2 : ∃ u : ℂ, ‖u‖ = 1 ∧ Xslab (momV f) (refl (aorb u)) ≤ X0
  · obtain ⟨u, hu, hX⟩ := h2
    have := hL (reflF f) (reflF_mem hf) u hu (by
      rw [momV_reflF]; unfold Xslab at hX ⊢; rw [phiB_refl, Complex.conj_re]; exact hX)
    rw [momV_reflF, qform_refl, Complex.conj_re] at this; exact this
  push Not at h1 h2
  -- rotate so that a₁ is real and ≥ 0
  set a1 := mom f 1
  set β : ℝ := -2 * Complex.arg a1
  set v : ℂ := exp (((β / 2 : ℝ) : ℂ) * I) with hvdef
  have hv : ‖v‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set g := rot β f
  have hg : g ∈ Ball := rot_mem hf β
  have hmg : momV g = rotV v (momV f) := momV_rot f β
  have hm1 : mom g 1 = (‖a1‖ : ℂ) := by
    have := congrFun hmg 1
    simp only [momV, rotV, Fin.val_one, Nat.cast_one] at this
    rw [this]
    have hv0 := ne_zero_of_norm hv
    have e : v ^ 3 * (v⁻¹) ^ (2 * 1) = v := by
      rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hv0)]; ring
    rw [e, hvdef]
    have hb : ((β / 2 : ℝ) : ℂ) = -(Complex.arg a1 : ℂ) := by simp [β]; ring
    rw [hb]
    change exp (-(Complex.arg a1 : ℂ) * I) * a1 = ‖a1‖
    have := Complex.norm_mul_exp_arg_mul_I a1
    calc exp (-(Complex.arg a1 : ℂ) * I) * a1
        = exp (-(Complex.arg a1 : ℂ) * I) * (‖a1‖ * exp (Complex.arg a1 * I)) := by rw [this]
      _ = ‖a1‖ * (exp (-(Complex.arg a1 : ℂ) * I) * exp (Complex.arg a1 * I)) := by ring
      _ = ‖a1‖ := by rw [← Complex.exp_add]; simp
  set x : Fin 7 → ℝ := ![(mom g 0).re, (mom g 0).im, (mom g 1).re, (mom g 2).re, (mom g 2).im,
    (mom g 3).re, (mom g 3).im] with hxdef
  have hx : amom x = momV g := by
    funext k
    fin_cases k <;> simp [amom, hxdef, momV, Complex.ext_iff, hm1]
  have hbd : ∀ k, |(mom g k).re| ≤ 1 ∧ |(mom g k).im| ≤ 1 := fun k =>
    ⟨le_trans (Complex.abs_re_le_norm _) (norm_mom_le hg k),
     le_trans (Complex.abs_im_le_norm _) (norm_mom_le hg k)⟩
  have hH : Hyps x := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have h0 := hbd 0; have h1 := hbd 1; have h2 := hbd 2; have h3 := hbd 3
      have hre1 : 0 ≤ (mom g 1).re := by rw [hm1]; simp
      fin_cases j <;> simp [rootLo, rootHi, hxdef] <;>
        first
        | exact ⟨by linarith [abs_le.mp h0.1], by linarith [abs_le.mp h0.1]⟩
        | exact ⟨by linarith [abs_le.mp h0.2], by linarith [abs_le.mp h0.2]⟩
        | exact ⟨hre1, by linarith [abs_le.mp h1.1]⟩
        | exact ⟨by linarith [abs_le.mp h2.1], by linarith [abs_le.mp h2.1]⟩
        | exact ⟨by linarith [abs_le.mp h2.2], by linarith [abs_le.mp h2.2]⟩
        | exact ⟨by linarith [abs_le.mp h3.1], by linarith [abs_le.mp h3.1]⟩
        | exact ⟨by linarith [abs_le.mp h3.2], by linarith [abs_le.mp h3.2]⟩
        | (constructor <;> linarith [abs_le.mp h0.1, abs_le.mp h0.2, abs_le.mp h1.1, abs_le.mp h2.1,
            abs_le.mp h2.2, abs_le.mp h3.1, abs_le.mp h3.2])
    · intro γ; rw [hx]; exact supp_ineq hg γ
    · intro u hu
      have hu' : ‖u * v⁻¹‖ = 1 := by rw [norm_mul, norm_inv, hu, hv]; norm_num
      rw [hx, hmg]
      unfold Xslab
      rw [phiB_rotV v u hv hu, phiB_rotV_refl v u hv hu]
      exact ⟨le_of_lt (by have := h1 _ hu'; unfold Xslab at this; exact this),
             le_of_lt (by have := h2 _ hu'; unfold Xslab at this; exact this)⟩
  have := global_step x hH
  unfold Goal at this
  rw [hx, hmg, qform_rotV v hv] at this
  exact this

/-! ## The bounds -/

theorem q_bound (hL : LocalThm) {f : 𝕋 → ℂ} (hf : f ∈ Ball) : ‖qform (momV f)‖ ≤ M := by
  set Q := qform (momV f)
  -- a unit c with c² Q = -‖Q‖
  set c : ℂ := exp ((((Real.pi - Complex.arg Q) / 2 : ℝ) : ℂ) * I)
  have hc : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hmc : momV (fun t => c * f t) = fun k => c * momV f k := by
    funext k; simp [momV, mom_smul]
  have hq : qform (momV (fun t => c * f t)) = -(‖Q‖ : ℂ) := by
    rw [hmc]
    have e : qform (fun k => c * momV f k) = c ^ 2 * Q := by simp only [qform, Q]; ring
    rw [e]
    have hc2 : c ^ 2 = exp (((Real.pi - Complex.arg Q : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [hc2]
    have := Complex.norm_mul_exp_arg_mul_I Q
    calc exp (((Real.pi - Complex.arg Q : ℝ) : ℂ) * I) * Q
        = exp (((Real.pi - Complex.arg Q : ℝ) : ℂ) * I) * (‖Q‖ * exp (Complex.arg Q * I)) := by
          rw [this]
      _ = ‖Q‖ * exp (Real.pi * I) := by rw [mul_left_comm, ← Complex.exp_add]; push_cast; ring_nf
      _ = -(‖Q‖ : ℂ) := by rw [Complex.exp_pi_mul_I]; ring
  have := lower_bound hL (smul_mem hf hc)
  rw [hq] at this
  simp at this
  linarith

theorem phi_bound {f g : 𝕋 → ℂ} (hf : f ∈ Ball) (hg : g ∈ Ball) : ‖phiB (momV f) (momV g)‖ ≤ 2 := by
  have bf := bessel hf
  have bg := bessel hg
  simp only [phiB, momV]
  show ‖mom f 0 * mom g 3 - 2 * mom f 1 * mom g 2 - 2 * mom f 2 * mom g 1 + mom f 3 * mom g 0‖ ≤ 2
  set a0 := mom f 0; set a1 := mom f 1; set a2 := mom f 2; set a3 := mom f 3
  set b0 := mom g 0; set b1 := mom g 1; set b2 := mom g 2; set b3 := mom g 3
  have n1 := norm_add_le (a0 * b3 - 2 * a1 * b2 - 2 * a2 * b1) (a3 * b0)
  have n2 := norm_sub_le (a0 * b3 - 2 * a1 * b2) (2 * a2 * b1)
  have n3 := norm_sub_le (a0 * b3) (2 * a1 * b2)
  have e1 : ‖a0 * b3‖ = ‖a0‖ * ‖b3‖ := norm_mul _ _
  have e2 : ‖2 * a1 * b2‖ = 2 * ‖a1‖ * ‖b2‖ := by rw [norm_mul, norm_mul]; norm_num
  have e3 : ‖2 * a2 * b1‖ = 2 * ‖a2‖ * ‖b1‖ := by rw [norm_mul, norm_mul]; norm_num
  have e4 : ‖a3 * b0‖ = ‖a3‖ * ‖b0‖ := norm_mul _ _
  have hs : ‖a0 * b3 - 2 * a1 * b2 - 2 * a2 * b1 + a3 * b0‖ ≤
      ‖a0‖ * ‖b3‖ + 2 * ‖a1‖ * ‖b2‖ + 2 * ‖a2‖ * ‖b1‖ + ‖a3‖ * ‖b0‖ := by linarith
  have q0 := two_mul_le_add_sq ‖a0‖ ‖b3‖
  have q1 := two_mul_le_add_sq ‖a1‖ ‖b2‖
  have q2 := two_mul_le_add_sq ‖a2‖ ‖b1‖
  have q3 := two_mul_le_add_sq ‖a3‖ ‖b0‖
  have s0 := sq_nonneg ‖a0‖; have s3 := sq_nonneg ‖a3‖
  have t0 := sq_nonneg ‖b0‖; have t3 := sq_nonneg ‖b3‖
  linarith

lemma M_eq : M = 8 / (3 * Real.sqrt 3) := by
  unfold M
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h0 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp; linarith

/-- The main theorem, given the local theorem. -/
theorem main_of_local (hL : LocalThm) :
    IsGreatest {x : ℝ | ∃ f ∈ Ball, ∃ g ∈ Ball, x = ‖phiB (momV f) (momV g)‖} 2 ∧
    IsGreatest {x : ℝ | ∃ f ∈ Ball, x = ‖qform (momV f)‖} (8 / (3 * Real.sqrt 3)) := by
  refine ⟨⟨⟨_, fourier_mem (-1), _, fourier_mem (-2), by rw [phi_witness]; simp⟩, ?_⟩,
    ⟨⟨h0, h0_mem, by
      rw [q_h0, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by unfold M; positivity), M_eq]⟩, ?_⟩⟩
  · rintro x ⟨f, hf, g, hg, rfl⟩; exact phi_bound hf hg
  · rintro x ⟨f, hf, rfl⟩; rw [← M_eq]; exact q_bound hL hf

end Harris
