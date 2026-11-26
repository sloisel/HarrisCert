module

public import HarrisCert.Local9

/-!
# Local theorem, part 10: evaluating the certificate polynomial

For `z` on the unit circle let `m̃(z) ∈ ℝ⁷` be built from `c_k = (z̄ + r)² λ_k(z)`,
`λ = (z³, -2z², -2z, 1)`. Then `Qm z := (Cᵀm̃)ᵀ Âᵢ (Cᵀm̃) ≤ (920/3) |z + r|⁸`.
-/

open Complex Matrix

@[expose] public section

namespace Harris

noncomputable def cvec (z : ℂ) : Fin 4 → ℂ :=
  ![((starRingEnd ℂ) z + r) ^ 2 * z ^ 3, ((starRingEnd ℂ) z + r) ^ 2 * (-2 * z ^ 2),
    ((starRingEnd ℂ) z + r) ^ 2 * (-2 * z), ((starRingEnd ℂ) z + r) ^ 2]

noncomputable def mt (z : ℂ) : Fin 7 → ℝ :=
  ![(cvec z 0).im, (cvec z 1).im, (cvec z 2).im, (cvec z 3).im,
    (cvec z 0).re - r / 2 * (cvec z 1).re, (cvec z 2).re - 3 * r / 2 * (cvec z 1).re, (cvec z 3).re]

noncomputable def Qm (z : ℂ) : ℝ := (Cr.transpose *ᵥ mt z) ⬝ᵥ Air *ᵥ (Cr.transpose *ᵥ mt z)

lemma σ_rK : σ rK = r := by rw [rK, σ_apply]; simp [r]; ring

lemma σ_m16 : σ (⟨0, -1 / 6⟩ : K3) = -(r / 2) := by rw [σ_apply]; simp [r]; ring
lemma σ_m12 : σ (⟨0, -1 / 2⟩ : K3) = -(3 * r / 2) := by rw [σ_apply]; simp [r]; ring

section chart

variable (e : K3) (t : ℝ)

/-- The chart point `z = σ(e) (1 + it)² / (1 + t²)`. -/
noncomputable def zch : ℂ := (σ e : ℂ) * (⟨1 - t ^ 2, 2 * t⟩ : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)

lemma D_pos : 0 < 1 + t ^ 2 := by positivity

lemma D_ne : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (D_pos t).ne'

lemma σ_two : σ (2 : K3) = 2 := map_ofNat σ 2
lemma σ_one : σ (1 : K3) = 1 := map_one σ
lemma σ_neg (x : K3) : σ (-x) = -σ x := map_neg σ x
lemma σ_mul (x y : K3) : σ (x * y) = σ x * σ y := map_mul σ x y

lemma cev_Wn : cev (WnP e) t = ((1 + t ^ 2 : ℝ) : ℂ) * zch e t := by
  rw [zch, mul_div_cancel₀ _ (D_ne t)]
  apply Complex.ext <;>
    simp only [cev, WnP, psc, pev_cons, pev_nil, map_zero, σ_one, σ_neg, σ_mul, σ_two, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero] <;> ring

lemma cev_Wb : cev (WbP e) t = ((1 + t ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) (zch e t) := by
  rw [zch, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, mul_div_cancel₀ _ (D_ne t)]
  apply Complex.ext <;>
    simp only [cev, WbP, psc, pev_cons, pev_nil, map_zero, σ_one, σ_neg, σ_mul, σ_two, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, Complex.conj_re,
      Complex.conj_im] <;> ring

lemma cev_Dn : cev DnP t = ((1 + t ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [cev, DnP, pev_cons, pev_nil, map_one, map_zero, Complex.ofReal_re, Complex.ofReal_im] <;> ring

lemma pev_fst (a : CP) (t : ℝ) : pev a.1 t = (cev a t).re := rfl
lemma pev_snd (a : CP) (t : ℝ) : pev a.2 t = (cev a t).im := rfl

lemma cev_ck (k : Fin 4) :
    cev (ckP e k) t = ((1 + t ^ 2 : ℝ) : ℂ) ^ 5 * cvec (zch e t) k := by
  have hW := cev_Wn e t
  have hB := cev_Wb e t
  have hD := cev_Dn t
  have hsq : cev (sqbP e) t = ((1 + t ^ 2 : ℝ) : ℂ) ^ 2 * ((starRingEnd ℂ) (zch e t) + r) ^ 2 := by
    rw [sqbP, cev_cmul, cev_cadd, cev_csc, hB, hD, σ_rK]; ring
  fin_cases k <;> simp [ckP, cev_cmul, cev_csc, hsq, hW, hD, σ_neg, σ_two, cvec] <;> push_cast <;> ring

lemma ofReal_pow_re (D : ℝ) (n : ℕ) (w : ℂ) : (((D : ℂ) ^ n) * w).re = D ^ n * w.re := by
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
lemma ofReal_pow_im (D : ℝ) (n : ℕ) (w : ℂ) : (((D : ℂ) ^ n) * w).im = D ^ n * w.im := by
  rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]

lemma pev_nvec (i : Fin 7) : pev (nvecP e i) t = (1 + t ^ 2) ^ 5 * mt (zch e t) i := by
  have hre : ∀ k, pev (ckP e k).1 t = (1 + t ^ 2) ^ 5 * (cvec (zch e t) k).re := fun k => by
    rw [pev_fst, cev_ck, ofReal_pow_re]
  have him : ∀ k, pev (ckP e k).2 t = (1 + t ^ 2) ^ 5 * (cvec (zch e t) k).im := fun k => by
    rw [pev_snd, cev_ck, ofReal_pow_im]
  fin_cases i <;> simp [nvecP, mt, pev_padd, pev_psc, hre, him, σ_m16, σ_m12] <;> ring

lemma Cr_apply (i : Fin 7) (j : Fin 6) : Cr i j = σ (Cm i j) := rfl
lemma Air_apply (a b : Fin 6) : Air a b = σ (Aim a b) := rfl

lemma pev_nhat (j : Fin 6) :
    pev (nhatP e j) t = (1 + t ^ 2) ^ 5 * (Cr.transpose *ᵥ mt (zch e t)) j := by
  rw [nhatP, pev_sumP]
  simp only [pev_psc, pev_nvec, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Cr_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

lemma pev_quad : pev (quadP e) t = (1 + t ^ 2) ^ 10 * Qm (zch e t) := by
  rw [quadP, pev_sumP]
  simp only [pev_sumP, pev_psc, pev_pmul, pev_nhat]
  unfold Qm
  set u := Cr.transpose *ᵥ mt (zch e t)
  simp only [dotProduct, Matrix.mulVec, Air_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

lemma pev_N1 : pev (N1P e) t = (1 + t ^ 2) ^ 2 * ‖zch e t + r‖ ^ 2 := by
  have hw : cev (cadd (WnP e) (csc rK DnP)) t = ((1 + t ^ 2 : ℝ) : ℂ) * (zch e t + r) := by
    rw [cev_cadd, cev_csc, cev_Wn, cev_Dn, σ_rK]; ring
  have hn : ∀ w : ℂ, w.re * w.re + w.im * w.im = ‖w‖ ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [N1P, pev_padd, pev_pmul, pev_pmul, pev_fst, pev_snd, hw, hn, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (D_pos t).le]
  ring

lemma pev_Pc : pev (PcP e) t =
    (1 + t ^ 2) ^ 10 * (920 / 3 * ‖zch e t + r‖ ^ 8 - Qm (zch e t)) := by
  have hD : pev DnP.1 t = 1 + t ^ 2 := by rw [pev_fst, cev_Dn, Complex.ofReal_re]
  rw [PcP, pev_padd, pev_psc, pev_psc, pev_quad, pev_pmul, pev_pmul, pev_pmul, pev_pmul, pev_pmul, pev_N1,
    hD, σ_rat, σ_neg, σ_one]
  push_cast; ring

lemma Qm_chart (he : σ e = 1 ∨ σ e = -1) (hc : pcellsOK (PcP e) 64 = true) (ht : |t| ≤ 1) :
    Qm (zch e t) ≤ 920 / 3 * ‖zch e t + r‖ ^ 8 := by
  have h := pcellsOK_sound (PcP e) 64 (by norm_num) hc t ht
  rw [pev_Pc] at h
  have hpos : 0 < (1 + t ^ 2) ^ 10 := pow_pos (D_pos t) 10
  have := (mul_nonneg_iff_of_pos_left hpos).mp h
  linarith

end chart

lemma chart_inv (z : ℂ) (hz : ‖z‖ = 1) (h : 0 ≤ z.re) :
    |z.im / (1 + z.re)| ≤ 1 ∧ zch 1 (z.im / (1 + z.re)) = z := by
  have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z; rw [hz, Complex.normSq_apply] at this; nlinarith
  have hp : 0 < 1 + z.re := by linarith
  constructor
  · rw [abs_div, abs_of_pos hp, div_le_one hp]
    have : z.im ^ 2 ≤ (1 + z.re) ^ 2 := by nlinarith
    have := sq_le_sq.mp this
    rwa [abs_of_pos hp] at this
  · set t := z.im / (1 + z.re) with htd
    have hD := D_pos t
    rw [zch, σ_one, Complex.ofReal_one, one_mul]
    apply Complex.ext
    · rw [Complex.div_ofReal_re]; simp only
      rw [div_eq_iff hD.ne', htd]; field_simp; linear_combination (-(1 + z.re)) * h2
    · rw [Complex.div_ofReal_im]; simp only
      rw [div_eq_iff hD.ne', htd]; field_simp; linear_combination (-z.im) * h2

/-- The `Λ₂` bound on the whole circle. -/
theorem Qm_le (z : ℂ) (hz : ‖z‖ = 1) : Qm z ≤ 920 / 3 * ‖z + r‖ ^ 8 := by
  rcases le_total 0 z.re with h | h
  · obtain ⟨ht, hzt⟩ := chart_inv z hz h
    have := Qm_chart 1 _ (Or.inl σ_one) Pc_pos1 ht
    rwa [hzt] at this
  · have hz' : ‖-z‖ = 1 := by rw [norm_neg, hz]
    obtain ⟨ht, hzt⟩ := chart_inv (-z) hz' (by simp; linarith)
    have hc : zch (-1) ((-z).im / (1 + (-z).re)) = z := by
      have e1 : zch (-1) ((-z).im / (1 + (-z).re)) = -zch 1 ((-z).im / (1 + (-z).re)) := by
        simp only [zch, σ_neg, σ_one]; push_cast; ring
      rw [e1, hzt, neg_neg]
    have := Qm_chart (-1) _ (Or.inr (by rw [σ_neg, σ_one])) Pc_pos2 ht
    rwa [hc] at this

end Harris
