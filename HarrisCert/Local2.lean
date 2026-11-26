module

public import HarrisCert.Local1

/-!
# Local theorem, part 2: Fourier coefficients by recurrences

`coef e n = ∫ zⁿ e dη`. If `(z + r) u = v` (or `(1 + r z) u = v`) with `u` continuous, the coefficients
satisfy a first-order recurrence; boundedness pins the solution down. This gives the coefficients of
`1/(z+r)`, `1/(1+rz)`, `h₀/(z+r)` and `h₀/(z+r)²`, hence of `1/ρ` and `h₀²/ρ`.
-/

open MeasureTheory Complex Filter Topology

@[expose] public section

namespace Harris

noncomputable def coef (e : 𝕋 → ℂ) (n : ℤ) : ℂ := ∫ t, fourier n t * e t ∂η

lemma coef_bounded {e : 𝕋 → ℂ} (he : Continuous e) : ∃ C, ∀ n, ‖coef e n‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image he).isBounded.exists_norm_le
  refine ⟨C, fun n => ?_⟩
  calc ‖coef e n‖ ≤ ∫ t, ‖fourier n t * e t‖ ∂η := norm_integral_le_integral_norm _
    _ ≤ ∫ _t, C ∂η := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (integrable_const _)
        refine Eventually.of_forall fun t => ?_
        dsimp only; rw [norm_mul, norm_fourier_apply, one_mul]; exact hC _ ⟨t, trivial, rfl⟩
    _ = C := by simp

lemma integrable_fe {e : 𝕋 → ℂ} (he : Continuous e) (n : ℤ) : Integrable (fun t => fourier n t * e t) η :=
  integrable_cont ((fourier n).continuous.mul he)

lemma coef_mul_zr {e : 𝕋 → ℂ} (he : Continuous e) (n : ℤ) :
    coef (fun t => (zz t + r) * e t) n = coef e (n + 1) + r * coef e n := by
  unfold coef
  have e1 : (fun t => fourier n t * ((zz t + r) * e t)) =
      fun t => fourier (n + 1) t * e t + (r : ℂ) * (fourier n t * e t) := by
    funext t; rw [fourier_add]; unfold zz; ring
  rw [e1, integral_add, integral_const_mul]
  · exact integrable_fe he _
  · exact (integrable_fe he _).const_mul _

lemma coef_mul_rz {e : 𝕋 → ℂ} (he : Continuous e) (n : ℤ) :
    coef (fun t => (1 + r * zz t) * e t) n = coef e n + r * coef e (n + 1) := by
  unfold coef
  have e1 : (fun t => fourier n t * ((1 + r * zz t) * e t)) =
      fun t => fourier n t * e t + (r : ℂ) * (fourier (n + 1) t * e t) := by
    funext t; rw [fourier_add]; unfold zz; ring
  rw [e1, integral_add, integral_const_mul]
  · exact integrable_fe he _
  · exact (integrable_fe he _).const_mul _

lemma coef_one (n : ℤ) : coef (fun _ => 1) n = if n = 0 then 1 else 0 := by
  unfold coef; simp only [mul_one]; exact integral_fourier n

lemma coef_congr {e f : 𝕋 → ℂ} (h : ∀ t, e t = f t) (n : ℤ) : coef e n = coef f n := by
  unfold coef; congr 1; funext t; rw [h]

/-- Backward growth: `U(n+1) + r U(n) = V(n)`, `V = 0` on `n ≤ -1`, `U` bounded ⟹ `U = 0` on `n ≤ 0`. -/
lemma rec_zero_neg (U V : ℤ → ℂ) (hb : ∃ C, ∀ n, ‖U n‖ ≤ C)
    (hrec : ∀ n, U (n + 1) + r * U n = V n) (hV : ∀ n ≤ -1, V n = 0) : ∀ n ≤ 0, U n = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hstep : ∀ m : ℕ, U (-(m : ℤ)) = -r * U (-((m + 1 : ℕ) : ℤ)) := by
    intro m
    have h := hrec (-((m + 1 : ℕ) : ℤ))
    rw [hV _ (by omega), show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by push_cast; ring] at h
    linear_combination h
  have hpow : ∀ m : ℕ, U 0 = (-(r : ℂ)) ^ m * U (-(m : ℤ)) := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [ih, hstep m, pow_succ]; ring
  have hU0 : U 0 = 0 := by
    have hbound : ∀ m : ℕ, ‖U 0‖ ≤ r ^ m * C := by
      intro m; rw [hpow m, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg r_pos.le]
      exact mul_le_mul_of_nonneg_left (hC _) (pow_nonneg r_pos.le m)
    have hlim : Tendsto (fun m : ℕ => r ^ m * C) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one r_pos.le r_lt_one).mul_const C
      simpa using this
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim (Eventually.of_forall hbound))
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast r_pos.ne'
  have hall : ∀ m : ℕ, U (-(m : ℤ)) = 0 := by
    intro m; induction m with
    | zero => simpa using hU0
    | succ m ih =>
      have := hstep m; rw [ih] at this
      have h2 : -(r : ℂ) * U (-((m + 1 : ℕ) : ℤ)) = 0 := this.symm
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (neg_eq_zero.mp h) hr0
      · exact h
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
  exact hall m

/-- Forward growth: `U(n) + r U(n+1) = V(n)`, `V = 0` on `n ≥ 1`, `U` bounded ⟹ `U = 0` on `n ≥ 1`. -/
lemma rec_zero_pos (U V : ℤ → ℂ) (hb : ∃ C, ∀ n, ‖U n‖ ≤ C)
    (hrec : ∀ n, U n + r * U (n + 1) = V n) (hV : ∀ n ≥ 1, V n = 0) : ∀ n ≥ 1, U n = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hstep : ∀ m : ℕ, U ((m : ℤ) + 1) = -r * U ((m : ℤ) + 2) := by
    intro m
    have h := hrec ((m : ℤ) + 1)
    rw [hV _ (by omega), show (m : ℤ) + 1 + 1 = (m : ℤ) + 2 by ring] at h
    linear_combination h
  have hpow : ∀ m : ℕ, U 1 = (-(r : ℂ)) ^ m * U ((m : ℤ) + 1) := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, hstep m, pow_succ, show ((m + 1 : ℕ) : ℤ) + 1 = (m : ℤ) + 2 by push_cast; ring]; ring
  have hU1 : U 1 = 0 := by
    have hbound : ∀ m : ℕ, ‖U 1‖ ≤ r ^ m * C := by
      intro m; rw [hpow m, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg r_pos.le]
      exact mul_le_mul_of_nonneg_left (hC _) (pow_nonneg r_pos.le m)
    have hlim : Tendsto (fun m : ℕ => r ^ m * C) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one r_pos.le r_lt_one).mul_const C
      simpa using this
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim (Eventually.of_forall hbound))
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast r_pos.ne'
  have hall : ∀ m : ℕ, U ((m : ℤ) + 1) = 0 := by
    intro m; induction m with
    | zero => simpa using hU1
    | succ m ih =>
      have := hstep m; rw [ih] at this
      have h2 : -(r : ℂ) * U ((m : ℤ) + 2) = 0 := this.symm
      rw [show ((m + 1 : ℕ) : ℤ) + 1 = (m : ℤ) + 2 by push_cast; ring]
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (neg_eq_zero.mp h) hr0
      · exact h
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  exact hall m

/-! ## `1/(z+r)` and `1/(1+rz)` -/

lemma den2_ne (t : 𝕋) : 1 + (r : ℂ) * zz t ≠ 0 := by
  intro h
  have h1 : (r : ℂ) * zz t = -1 := by linear_combination h
  have := congrArg norm h1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg r_pos.le, norm_zz, norm_neg, norm_one,
    mul_one] at this
  linarith [r_lt_one]

noncomputable def e1 (t : 𝕋) : ℂ := 1 / (zz t + r)
noncomputable def f1 (t : 𝕋) : ℂ := 1 / (1 + r * zz t)

lemma e1_cont : Continuous e1 := by
  unfold e1 zz; exact continuous_const.div ((fourier 1).continuous.add continuous_const) den_ne
lemma f1_cont : Continuous f1 := by
  unfold f1 zz
  exact continuous_const.div (continuous_const.add (continuous_const.mul (fourier 1).continuous)) den2_ne

lemma E1_rec (n : ℤ) : coef e1 (n + 1) + r * coef e1 n = if n = 0 then 1 else 0 := by
  rw [← coef_mul_zr e1_cont, ← coef_one]
  apply coef_congr; intro t; unfold e1; rw [mul_one_div, div_self (show zz t + (r : ℂ) ≠ 0 from den_ne t)]

lemma F1_rec (n : ℤ) : coef f1 n + r * coef f1 (n + 1) = if n = 0 then 1 else 0 := by
  rw [← coef_mul_rz f1_cont, ← coef_one]
  apply coef_congr; intro t; unfold f1; rw [mul_one_div, div_self (den2_ne t)]

lemma E1_neg : ∀ n ≤ 0, coef e1 n = 0 :=
  rec_zero_neg _ _ (coef_bounded e1_cont) E1_rec (fun n hn => by rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))])

lemma F1_pos : ∀ n ≥ 1, coef f1 n = 0 :=
  rec_zero_pos _ _ (coef_bounded f1_cont) F1_rec (fun n hn => by rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))])

/-! ## `h₀/(z+r)` and `h₀/(z+r)²` -/

noncomputable def e2 (t : 𝕋) : ℂ := h0 t / (zz t + r)
noncomputable def e3 (t : 𝕋) : ℂ := e2 t / (zz t + r)

lemma e2_cont : Continuous e2 := by
  unfold e2 zz; exact h0_cont.div ((fourier 1).continuous.add continuous_const) den_ne
lemma e3_cont : Continuous e3 := by
  unfold e3 zz; exact e2_cont.div ((fourier 1).continuous.add continuous_const) den_ne

lemma coef_h0 (n : ℤ) : coef h0 n = ch n := by unfold coef ch; rfl

lemma ch_neg : ∀ n ≤ 0, ch n = 0 :=
  rec_zero_neg ch _ ⟨1, ch_norm⟩ ch_rec (fun n hn => by rw [if_neg (by omega), if_neg (by omega)]; simp)

lemma E2_rec (n : ℤ) : coef e2 (n + 1) + r * coef e2 n = ch n := by
  rw [← coef_mul_zr e2_cont, ← coef_h0]
  apply coef_congr; intro t; unfold e2; rw [mul_div_cancel₀ _ (show zz t + (r : ℂ) ≠ 0 from den_ne t)]

lemma E3_rec (n : ℤ) : coef e3 (n + 1) + r * coef e3 n = coef e2 n := by
  rw [← coef_mul_zr e3_cont]
  apply coef_congr; intro t; unfold e3; rw [mul_div_cancel₀ _ (show zz t + (r : ℂ) ≠ 0 from den_ne t)]

lemma E2_neg : ∀ n ≤ 0, coef e2 n = 0 :=
  rec_zero_neg _ _ (coef_bounded e2_cont) E2_rec (fun n hn => ch_neg n (by omega))

lemma E3_neg : ∀ n ≤ 0, coef e3 n = 0 :=
  rec_zero_neg _ _ (coef_bounded e3_cont) E3_rec (fun n hn => E2_neg n (by omega))

end Harris
