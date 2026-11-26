module

public import HarrisCert.Local4

/-!
# Local theorem, part 5: `ℚ(√3)` as `QuadraticAlgebra ℚ 3 0`, and the Gram matrix

The seven basis functions are `Re(h₀ z^k)` (`k = 0..3`) and `Im(h₀ z^k)` (`k = 0, 2, 3`). Their Gram
matrix in `L²(1/ρ)` is `σ(Γk)` for an explicit matrix `Γk` over `ℚ(√3)`, where `σ : ℚ(√3) → ℝ`.
-/

open MeasureTheory Complex Filter Topology

@[expose] public section

namespace Harris

abbrev K3 := QuadraticAlgebra ℚ 3 0

noncomputable def σ : K3 →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 3, by rw [Real.mul_self_sqrt (by norm_num)]; simp⟩

lemma σ_apply (x : K3) : σ x = x.re + x.im * Real.sqrt 3 := by
  simp [σ, QuadraticAlgebra.lift_apply_apply, Rat.smul_def]

lemma sqrt3_eq : Real.sqrt 3 = 3 * r := by unfold r; ring

/-- Exact sign test in `ℚ(√3)`. -/
def K3.nn (x : K3) : Bool := Q3.nonneg ⟨x.re, x.im⟩

lemma K3.nn_iff (x : K3) : x.nn = true ↔ 0 ≤ σ x := by
  rw [K3.nn, Q3.nonneg_iff, σ_apply]; simp [Q3.toReal]

/-- `U n` and `W n` as elements of `ℚ(√3)`. -/
def Uk : ℤ → K3
  | 0 => ⟨0, 3 / 4⟩
  | 1 => ⟨-3 / 4, 0⟩
  | -1 => ⟨-3 / 4, 0⟩
  | 2 => ⟨0, 1 / 4⟩
  | -2 => ⟨0, 1 / 4⟩
  | 3 => ⟨-1 / 4, 0⟩
  | -3 => ⟨-1 / 4, 0⟩
  | _ => 0

def Wk : ℤ → K3
  | 3 => ⟨1 / 2, 0⟩
  | 5 => ⟨-1 / 2, 0⟩
  | 6 => ⟨0, 4 / 9⟩
  | _ => 0

lemma σ_mk (p q : ℚ) : σ (⟨p, q⟩ : K3) = p + q * (3 * r) := by rw [σ_apply, sqrt3_eq]

lemma Uc_σ (n : ℤ) (hn : -3 ≤ n ∧ n ≤ 3) : Uc n = ((σ (Uk n) : ℝ) : ℂ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Uc_vals
  have hn' : n = -3 ∨ n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Uk, σ_mk, h1, h2, h3, h4, h5, h6, h7] <;> push_cast <;> ring

lemma Wc_σ (n : ℤ) (hn : 0 ≤ n ∧ n ≤ 6) : Wc n = ((σ (Wk n) : ℝ) : ℂ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := Wc_vals
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Wk, σ_mk, h0, h1, h2, h3, h4, h5, h6] <;> ring

/-! ## The basis and its Gram matrix -/

noncomputable def hzk (k : ℕ) (t : 𝕋) : ℂ := h0 t * fourier (k : ℤ) t

/-- Frequencies and real/imaginary flags of the seven basis functions. -/
def bj (a : Fin 7) : ℕ := if a.val < 4 then a.val else if a.val = 4 then 0 else a.val - 3
def bim (a : Fin 7) : Bool := decide (4 ≤ a.val)

lemma bj_le (a : Fin 7) : bj a ≤ 3 := by unfold bj; split_ifs <;> omega

noncomputable def φb (a : Fin 7) (t : 𝕋) : ℝ := if bim a then (hzk (bj a) t).im else (hzk (bj a) t).re

/-- The Gram matrix over `ℚ(√3)`. -/
def Γk (a b : Fin 7) : K3 :=
  let j : ℤ := bj a; let k : ℤ := bj b
  if bim a = false ∧ bim b = false then (1 / 2 : ℚ) • (Wk (j + k) + Uk (j - k))
  else if bim a = true ∧ bim b = true then (1 / 2 : ℚ) • (Uk (j - k) - Wk (j + k))
  else 0

lemma prod_parts (A B : ℂ) :
    A.re * B.re = ((A * B).re + (A * (starRingEnd ℂ) B).re) / 2 ∧
    A.im * B.im = ((A * (starRingEnd ℂ) B).re - (A * B).re) / 2 ∧
    A.re * B.im = ((A * B).im - (A * (starRingEnd ℂ) B).im) / 2 ∧
    A.im * B.re = ((A * B).im + (A * (starRingEnd ℂ) B).im) / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma hzk_mul (j k : ℕ) (t : 𝕋) :
    hzk j t * hzk k t / (ρf t : ℂ) = fourier ((j : ℤ) + k) t * h0sqρ t := by
  unfold hzk h0sqρ; rw [fourier_add]; ring

lemma hzk_mul_conj (j k : ℕ) (t : 𝕋) :
    hzk j t * (starRingEnd ℂ) (hzk k t) / (ρf t : ℂ) = fourier ((j : ℤ) - k) t * invρ t := by
  unfold hzk invρ
  rw [sub_eq_add_neg, fourier_add, fourier_neg, map_mul]
  have := h0_conj_mul t
  calc h0 t * fourier (j : ℤ) t * ((starRingEnd ℂ) (h0 t) * (starRingEnd ℂ) (fourier (k : ℤ) t)) / ↑(ρf t)
      = ((starRingEnd ℂ) (h0 t) * h0 t) * (fourier (j : ℤ) t * (starRingEnd ℂ) (fourier (k : ℤ) t) *
          (1 / ↑(ρf t))) := by ring
    _ = _ := by rw [this, one_mul]

lemma integral_re_div (F : 𝕋 → ℂ) (hF : Continuous F) :
    ∫ t, (F t).re ∂η = (∫ t, F t ∂η).re := by
  exact integral_re (integrable_cont hF)

lemma integral_im_div (F : 𝕋 → ℂ) (hF : Continuous F) :
    ∫ t, (F t).im ∂η = (∫ t, F t ∂η).im := by
  exact integral_im (integrable_cont hF)

end Harris
