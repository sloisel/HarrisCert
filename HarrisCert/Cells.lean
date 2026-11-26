module

public import HarrisCert.Poly

/-!
# Soundness of the cell bounds

On a cell `[a,b]` the checker certifies `w ≤ U` for a quadratic `U`, and then
`∫ √Q · w ≤ ∫ √Q · U ≤ (1/2λ) ∫ Q U + (λ/2) ∫ U`, with the integrals bounded by rounded moments.
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace Harris

noncomputable def wfun (t : ℝ) : ℝ := 1 / (1 + t ^ 2) ^ 4

lemma wfun_pos (t : ℝ) : 0 < wfun t := by unfold wfun; positivity

lemma continuous_wfun : Continuous wfun := by
  have h : Continuous fun t : ℝ => (1 + t ^ 2) ^ 4 := by fun_prop
  exact continuous_const.div h (fun t => (by positivity : (1 + t ^ 2) ^ 4 ≠ 0))

lemma peval_quad (m : ℚ) (s : ℝ) : peval [1 + m ^ 2, 2 * m, 1] s = 1 + ((m : ℝ) + s) ^ 2 := by
  simp; ring

/-- `w ≤ U := w₀ + w₁ (t-m) + c₂ (t-m)²` near `m`, from the checked coefficient conditions. -/
lemma w_le_U (m δ w0 w1 c2 : ℚ) (E G K : List ℚ)
    (hE : E = pPow [1 + m ^ 2, 2 * m, 1] 4) (hG : G = pAdd (pMul E [w0, w1]) [-1])
    (hKd : K = pAdd (G.drop 2) (pScale c2 E))
    (hG0 : G.getD 0 0 = 0) (hG1 : G.getD 1 0 = 0) (hK : tailAbs K δ ≤ K.getD 0 0)
    (t : ℝ) (ht : |t - m| ≤ δ) :
    wfun t ≤ w0 + w1 * (t - m) + c2 * (t - m) ^ 2 := by
  set s : ℝ := t - m with hs
  have hEs : peval E s = (1 + t ^ 2) ^ 4 := by
    rw [hE, peval_pow, peval_quad]; congr 2; rw [hs]; ring
  have hEpos : 0 < peval E s := by rw [hEs]; positivity
  have hGs : peval G s = peval E s * (w0 + w1 * s) - 1 := by
    rw [hG, peval_add, peval_mul]; simp; ring
  have hsplit := peval_split2 G s
  rw [hG0, hG1] at hsplit
  have hKs : peval K s = peval (G.drop 2) s + c2 * peval E s := by
    rw [hKd, peval_add, peval_scale]
  have hKnn : 0 ≤ peval K s := by
    have := peval_ge_tail K s δ ht
    have h0 : (0 : ℝ) ≤ ((K.getD 0 0 - tailAbs K δ : ℚ) : ℝ) := by
      exact_mod_cast sub_nonneg.mpr hK
    linarith
  -- U - w = s² K / E
  have key : (w0 + w1 * s + c2 * s ^ 2 : ℝ) - wfun t = s ^ 2 * peval K s / peval E s := by
    unfold wfun
    rw [← hEs]
    field_simp
    rw [hKs]
    have : peval E s * (w0 + w1 * s) - 1 = s ^ 2 * peval (G.drop 2) s := by
      rw [← hGs, hsplit]; push_cast; ring
    linear_combination this
  have : 0 ≤ s ^ 2 * peval K s / peval E s := by positivity
  linarith

/-- The AM-GM step: `√Q · U ≤ Q U / (2λ) + λ U / 2` for `U ≥ 0`, `λ > 0`. -/
lemma amgm (Qv U lam : ℝ) (hQ : 0 ≤ Qv) (hU : 0 ≤ U) (hlam : 0 < lam) :
    Real.sqrt Qv * U ≤ Qv * U / (2 * lam) + lam * U / 2 := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 ≤ s ∧ Qv = s ^ 2 := ⟨Real.sqrt Qv, Real.sqrt_nonneg _, (Real.sq_sqrt hQ).symm⟩
  rw [Real.sqrt_sq hs0]
  have h : 0 ≤ U * (s - lam) ^ 2 / (2 * lam) := by positivity
  have : s ^ 2 * U / (2 * lam) + lam * U / 2 - s * U = U * (s - lam) ^ 2 / (2 * lam) := by
    field_simp; ring
  linarith

lemma continuous_zipIdx_sum (l : List (ℚ × ℕ)) :
    Continuous fun t : ℝ => (l.map fun ci => (ci.1 : ℝ) * t ^ ci.2).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact continuous_const
  | cons x l ihl =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuous_const.mul (continuous_pow _)).add ihl

lemma integral_zipIdx_sum (a b : ℝ) (Uf : ℝ → ℝ) (hU : Continuous Uf) :
    ∀ (l : List (ℚ × ℕ)),
      ∫ t in a..b, (l.map fun ci => (ci.1 : ℝ) * t ^ ci.2).sum * Uf t =
        (l.map fun ci => (ci.1 : ℝ) * ∫ t in a..b, t ^ ci.2 * Uf t).sum
  | [] => by simp
  | ci :: l => by
    have ih := integral_zipIdx_sum a b Uf hU l
    simp only [List.map_cons, List.sum_cons, add_mul]
    rw [intervalIntegral.integral_add, ih]
    · congr 1
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    · exact (by fun_prop : Continuous fun t : ℝ => (ci.1 : ℝ) * t ^ ci.2 * Uf t).intervalIntegrable _ _
    · exact ((continuous_zipIdx_sum l).mul hU).intervalIntegrable _ _

/-- The bound on one cell, given moment bounds. -/
lemma cell_bound (a b : ℝ) (hab : a ≤ b) (Uf : ℝ → ℝ) (hUc : Continuous Uf)
    (hwU : ∀ t ∈ Set.Icc a b, wfun t ≤ Uf t) (Q : List ℚ) (hQ : ∀ t, 0 ≤ peval Q t)
    (μhi μlo : ℕ → ℚ)
    (hhi : ∀ i < Q.length, ∫ t in a..b, t ^ i * Uf t ≤ μhi i)
    (hlo : ∀ i < Q.length, (μlo i : ℝ) ≤ ∫ t in a..b, t ^ i * Uf t)
    (h0 : ∫ t in a..b, t ^ 0 * Uf t ≤ μhi 0)
    (lam : ℚ) (hlam : 0 < lam) :
    ∫ t in a..b, Real.sqrt (peval Q t) * wfun t ≤
      (((Q.zipIdx.map fun qi => qi.1 * (if 0 ≤ qi.1 then μhi qi.2 else μlo qi.2)).sum / (2 * lam) +
        lam * μhi 0 / 2 : ℚ) : ℝ) := by
  have hlamR : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hQc : Continuous fun t => peval Q t := continuous_peval Q
  -- pointwise bound on [a,b]
  have hpt : ∀ t ∈ Set.Icc a b, Real.sqrt (peval Q t) * wfun t ≤
      peval Q t * Uf t / (2 * lam) + lam * Uf t / 2 := by
    intro t ht
    have hw := hwU t ht
    have hU0 : 0 ≤ Uf t := le_trans (wfun_pos t).le hw
    calc Real.sqrt (peval Q t) * wfun t ≤ Real.sqrt (peval Q t) * Uf t :=
          mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg _)
      _ ≤ _ := amgm _ _ _ (hQ t) hU0 hlamR
  have hint : ∫ t in a..b, Real.sqrt (peval Q t) * wfun t ≤
      ∫ t in a..b, (peval Q t * Uf t / (2 * lam) + lam * Uf t / 2) := by
    apply intervalIntegral.integral_mono_on hab
    · exact ((Real.continuous_sqrt.comp hQc).mul continuous_wfun).intervalIntegrable _ _
    · exact ((hQc.mul hUc).div_const _ |>.add ((continuous_const.mul hUc).div_const _)).intervalIntegrable _ _
    · exact hpt
  have hsplit : ∫ t in a..b, (peval Q t * Uf t / (2 * lam) + lam * Uf t / 2) =
      (∫ t in a..b, peval Q t * Uf t) / (2 * lam) + lam * (∫ t in a..b, t ^ 0 * Uf t) / 2 := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_div, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul]
    · simp
    · exact ((hQc.mul hUc).div_const _).intervalIntegrable _ _
    · exact ((continuous_const.mul hUc).div_const _).intervalIntegrable _ _
  -- ∫ Q U as a sum of moments
  have hQU : ∫ t in a..b, peval Q t * Uf t =
      ((Q.zipIdx.map fun qi => (qi.1 : ℝ) * ∫ t in a..b, t ^ qi.2 * Uf t).sum) := by
    have := integral_zipIdx_sum a b Uf hUc Q.zipIdx
    rw [← this]; congr 1; funext t; rw [peval_eq_sum]
  have hB : ((Q.zipIdx.map fun qi => (qi.1 : ℝ) * ∫ t in a..b, t ^ qi.2 * Uf t).sum) ≤
      (((Q.zipIdx.map fun qi => qi.1 * (if 0 ≤ qi.1 then μhi qi.2 else μlo qi.2)).sum : ℚ) : ℝ) := by
    rw [Rat.cast_list_sum, List.map_map]
    apply List.sum_le_sum
    intro qi hqi
    have hidx : qi.2 < Q.length := by
      rcases List.mem_zipIdx hqi with ⟨_, h2, _⟩; simpa using h2
    simp only [Function.comp_apply, Rat.cast_mul]
    split_ifs with hq
    · have : (0 : ℝ) ≤ qi.1 := by exact_mod_cast hq
      push_cast; exact mul_le_mul_of_nonneg_left (hhi _ hidx) this
    · have : (qi.1 : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hq))
      push_cast; exact mul_le_mul_of_nonpos_left (hlo _ hidx) this
  rw [hsplit, hQU] at hint
  push_cast
  have h2l : 0 < 2 * (lam : ℝ) := by positivity
  have := div_le_div_of_nonneg_right hB h2l.le
  have h0' : (lam : ℝ) * (∫ t in a..b, t ^ 0 * Uf t) / 2 ≤ lam * μhi 0 / 2 := by
    have := mul_le_mul_of_nonneg_left h0 hlamR.le; linarith
  push_cast at this
  linarith

/-- The exact moments of a quadratic. -/
lemma moment_formula (a b A0 A1 A2 : ℚ) (i : ℕ) :
    ∫ t in (a : ℝ)..b, t ^ i * ((A0 : ℝ) + A1 * t + A2 * t ^ 2) =
      ((A0 * powInt a b i + A1 * powInt a b (i + 1) + A2 * powInt a b (i + 2) : ℚ) : ℝ) := by
  have e : (fun t : ℝ => t ^ i * ((A0 : ℝ) + A1 * t + A2 * t ^ 2)) =
      fun t => (A0 : ℝ) * t ^ i + ((A1 : ℝ) * t ^ (i + 1) + (A2 : ℝ) * t ^ (i + 2)) := by
    funext t; ring
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  · simp only [powInt]; push_cast; ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

end Harris
