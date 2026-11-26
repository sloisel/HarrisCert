module

public import HarrisCert.Core.Q3
public import Mathlib

/-!
# `ℚ(√3)` and `ℂ` over it: real interpretation and the exactness of the sign test
-/

@[expose] public section

namespace Harris

namespace Q3

/-- The real number `p + q √3`. -/
noncomputable def toReal (a : Q3) : ℝ := a.p + a.q * Real.sqrt 3

lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
lemma sqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3

@[simp] lemma toReal_add (a b : Q3) : (a + b).toReal = a.toReal + b.toReal := by
  simp [toReal]; ring
@[simp] lemma toReal_sub (a b : Q3) : (a - b).toReal = a.toReal - b.toReal := by
  simp [toReal]; ring
@[simp] lemma toReal_neg (a : Q3) : (-a).toReal = -a.toReal := by
  simp [toReal]; ring
@[simp] lemma toReal_zero : (0 : Q3).toReal = 0 := by simp [toReal]
@[simp] lemma toReal_ofRat (x : ℚ) : (ofRat x).toReal = x := by simp [toReal]
@[simp] lemma toReal_smul (s : ℚ) (a : Q3) : (smul s a).toReal = s * a.toReal := by
  simp [toReal]; ring
@[simp] lemma toReal_mul (a b : Q3) : (a * b).toReal = a.toReal * b.toReal := by
  simp only [toReal, mul_p, mul_q]; push_cast
  have h := sqrt3_sq
  linear_combination (-(↑a.q * ↑b.q)) * h

lemma nonneg_iff (a : Q3) : a.nonneg = true ↔ 0 ≤ a.toReal := by
  have hs := sqrt3_sq
  have hs0 := sqrt3_nonneg
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold nonneg toReal
  by_cases hp : 0 ≤ a.p
  · have hp' : (0 : ℝ) ≤ a.p := by exact_mod_cast hp
    by_cases hq : 0 ≤ a.q
    · have hq' : (0 : ℝ) ≤ a.q := by exact_mod_cast hq
      simp only [hp, hq, ite_true, true_iff]; positivity
    · have hq' : (a.q : ℝ) < 0 := by exact_mod_cast (not_le.mp hq)
      simp only [hp, hq, ite_true, ite_false, decide_eq_true_eq]
      constructor
      · intro h
        have h' : (3 : ℝ) * (a.q : ℝ) ^ 2 ≤ (a.p : ℝ) ^ 2 := by exact_mod_cast h
        -- (-q √3)² = 3 q² ≤ p², both sides nonnegative
        have hx : 0 ≤ -(a.q : ℝ) * Real.sqrt 3 := by nlinarith
        nlinarith [sq_nonneg ((a.p : ℝ) - (-(a.q : ℝ) * Real.sqrt 3))]
      · intro h
        have hx : 0 ≤ -(a.q : ℝ) * Real.sqrt 3 := by nlinarith
        have : (-(a.q : ℝ) * Real.sqrt 3) ^ 2 ≤ (a.p : ℝ) ^ 2 := by
          exact pow_le_pow_left₀ hx (by linarith) 2
        have h3 : (3 : ℝ) * (a.q : ℝ) ^ 2 ≤ (a.p : ℝ) ^ 2 := by nlinarith
        exact_mod_cast h3
  · have hp' : (a.p : ℝ) < 0 := by exact_mod_cast (not_le.mp hp)
    by_cases hq : 0 < a.q
    · have hq' : (0 : ℝ) < a.q := by exact_mod_cast hq
      simp only [hp, hq, ite_true, ite_false, decide_eq_true_eq]
      constructor
      · intro h
        have h' : (a.p : ℝ) ^ 2 ≤ 3 * (a.q : ℝ) ^ 2 := by exact_mod_cast h
        have hx : 0 ≤ (a.q : ℝ) * Real.sqrt 3 := by positivity
        nlinarith [sq_nonneg (-(a.p : ℝ) - (a.q : ℝ) * Real.sqrt 3)]
      · intro h
        have hx : 0 ≤ -(a.p : ℝ) := by linarith
        have : (-(a.p : ℝ)) ^ 2 ≤ ((a.q : ℝ) * Real.sqrt 3) ^ 2 :=
          pow_le_pow_left₀ hx (by linarith) 2
        have h3 : (a.p : ℝ) ^ 2 ≤ 3 * (a.q : ℝ) ^ 2 := by nlinarith
        exact_mod_cast h3
    · have hq' : (a.q : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp hq)
      simp only [hp, hq, ite_false]
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; nlinarith

lemma le_qmax (κ : Q3) (l h : ℚ) (z : ℝ) (hl : (l : ℝ) ≤ z) (hh : z ≤ h) :
    κ.toReal * z ≤ (qmax κ l h).toReal := by
  unfold qmax
  split_ifs with hk
  · have := (nonneg_iff κ).mp hk
    simp only [toReal_mul, toReal_ofRat]; exact mul_le_mul_of_nonneg_left hh this
  · have : κ.toReal < 0 := by
      by_contra hc; exact hk ((nonneg_iff κ).mpr (not_lt.mp hc))
    simp only [toReal_mul, toReal_ofRat]; nlinarith

end Q3

namespace C3

noncomputable def toC (a : C3) : ℂ := ⟨a.re.toReal, a.im.toReal⟩

@[simp] lemma toC_re (a : C3) : (toC a).re = a.re.toReal := rfl
@[simp] lemma toC_im (a : C3) : (toC a).im = a.im.toReal := rfl
@[simp] lemma toC_add (a b : C3) : toC (a + b) = toC a + toC b := by
  apply Complex.ext <;> simp
@[simp] lemma toC_neg (a : C3) : toC (-a) = -toC a := by
  apply Complex.ext <;> simp
@[simp] lemma toC_mul (a b : C3) : toC (a * b) = toC a * toC b := by
  apply Complex.ext <;> simp
@[simp] lemma toC_zero : toC 0 = 0 := by apply Complex.ext <;> simp
@[simp] lemma toC_conj (a : C3) : toC (conj a) = (starRingEnd ℂ) (toC a) := by
  apply Complex.ext <;> simp
@[simp] lemma toC_smul (s : ℚ) (a : C3) : toC (smul s a) = (s : ℂ) * toC a := by
  apply Complex.ext <;> simp
@[simp] lemma toC_ofQ3 (x : Q3) : toC (ofQ3 x) = (x.toReal : ℂ) := by
  apply Complex.ext <;> simp

end C3

end Harris
