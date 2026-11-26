module

public import HarrisCert.Local3

/-!
# Local theorem, part 4: values of `U`, `W`; Gram integrals; Bessel's inequality in `L²(ρ)`
-/

open MeasureTheory Complex Filter Topology

@[expose] public section

namespace Harris

/-! ## Values -/

lemma ch_1 : ch 1 = r := by have := ch_rec 0; rw [ch_zero] at this; simpa using this
lemma ch_2 : ch 2 = 2 / 3 := by
  have := ch_rec 1; rw [show (1 : ℤ) + 1 = 2 by norm_num, ch_1] at this; simp at this
  linear_combination this - rr
lemma ch_3 : ch 3 = -(2 * r / 3) := by
  have := ch_rec 2; rw [show (2 : ℤ) + 1 = 3 by norm_num, ch_2] at this; simp at this
  linear_combination this
lemma ch_4 : ch 4 = 2 / 9 := by
  have := ch_rec 3; rw [show (3 : ℤ) + 1 = 4 by norm_num, ch_3] at this; simp at this
  linear_combination this + (2 / 3 : ℂ) * rr

lemma E2_0 : coef e2 0 = 0 := E2_neg 0 le_rfl
lemma E2_1 : coef e2 1 = 0 := by
  have := E2_rec 0; rw [show (0 : ℤ) + 1 = 1 by norm_num, E2_0, ch_zero] at this; simpa using this
lemma E2_2 : coef e2 2 = r := by
  have := E2_rec 1; rw [show (1 : ℤ) + 1 = 2 by norm_num, E2_1, ch_1] at this; simpa using this
lemma E2_3 : coef e2 3 = 1 / 3 := by
  have := E2_rec 2; rw [show (2 : ℤ) + 1 = 3 by norm_num, E2_2, ch_2] at this
  linear_combination this - rr
lemma E2_4 : coef e2 4 = -r := by
  have := E2_rec 3; rw [show (3 : ℤ) + 1 = 4 by norm_num, E2_3, ch_3] at this
  linear_combination this
lemma E2_5 : coef e2 5 = 5 / 9 := by
  have := E2_rec 4; rw [show (4 : ℤ) + 1 = 5 by norm_num, E2_4, ch_4] at this
  linear_combination this + rr

lemma E3_0 : coef e3 0 = 0 := E3_neg 0 le_rfl
lemma E3_1 : coef e3 1 = 0 := by
  have := E3_rec 0; rw [show (0 : ℤ) + 1 = 1 by norm_num, E3_0, E2_0] at this; simpa using this
lemma E3_2 : coef e3 2 = 0 := by
  have := E3_rec 1; rw [show (1 : ℤ) + 1 = 2 by norm_num, E3_1, E2_1] at this; simpa using this
lemma E3_3 : coef e3 3 = r := by
  have := E3_rec 2; rw [show (2 : ℤ) + 1 = 3 by norm_num, E3_2, E2_2] at this; simpa using this
lemma E3_4 : coef e3 4 = 0 := by
  have := E3_rec 3; rw [show (3 : ℤ) + 1 = 4 by norm_num, E3_3, E2_3] at this
  linear_combination this - rr
lemma E3_5 : coef e3 5 = -r := by
  have := E3_rec 4; rw [show (4 : ℤ) + 1 = 5 by norm_num, E3_4, E2_4] at this; simpa using this
lemma E3_6 : coef e3 6 = 8 / 9 := by
  have := E3_rec 5; rw [show (5 : ℤ) + 1 = 6 by norm_num, E3_5, E2_5] at this
  linear_combination this + rr

lemma one_sub_rr : (1 : ℂ) - r * r = 2 / 3 := by rw [rr]; norm_num

lemma Uc_vals : Uc 0 = 9 * r / 4 ∧ Uc 1 = -3 / 4 ∧ Uc (-1) = -3 / 4 ∧ Uc 2 = 3 * r / 4 ∧
    Uc (-2) = 3 * r / 4 ∧ Uc 3 = -1 / 4 ∧ Uc (-3) = -1 / 4 := by
  have hr := r_ne
  have h := rr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Uc_eq, one_sub_rr]
  · rw [E1_0, F1_0]; field_simp; linear_combination (-(36 : ℂ)) * h
  · rw [E1_1, F1_1]; field_simp; ring
  · rw [E1_neg (-1) (by norm_num), F1_m1]; field_simp; ring
  · rw [E1_2, F1_pos 2 (by norm_num)]; field_simp; ring
  · rw [E1_neg (-2) (by norm_num), F1_m2]; field_simp; ring
  · rw [E1_3, F1_pos 3 (by norm_num)]; field_simp; linear_combination (-(12 : ℂ) * r) * h
  · rw [E1_neg (-3) (by norm_num), F1_m3]; field_simp; linear_combination (-(12 : ℂ)) * h

/-- `W n = ∫ h₀² zⁿ/ρ` for `0 ≤ n ≤ 6`. -/
lemma Wc_vals : Wc 0 = 0 ∧ Wc 1 = 0 ∧ Wc 2 = 0 ∧ Wc 3 = 1 / 2 ∧ Wc 4 = 0 ∧ Wc 5 = -1 / 2 ∧
    Wc 6 = 4 * r / 3 := by
  have hr := r_ne
  have h := rr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Wc_eq]
  · rw [E3_0]; simp
  · rw [E3_1]; simp
  · rw [E3_2]; simp
  · rw [E3_3]; field_simp
  · rw [E3_4]; simp
  · rw [E3_5]; field_simp
  · rw [E3_6]; field_simp; linear_combination (-(72 : ℂ)) * h

end Harris
