module

public import HarrisCert.Data.LocalData

/-!
# Local theorem, part 7: the finite-dimensional estimate

Real images (under `σ`) of the exact data, completing the square, and the core inequality

`ξᵀHξ + 2X t·ξ ≥ -(Λ + (ε + 2)·3/κₙ) X²`

for `ξ` with `|c_κ·ξ| ≤ √3 X`, provided `|t·ξ_κ| ≤ √3` and `(Cᵀt)ᵀ Âᵢ (Cᵀt) ≤ Λ`.
-/

open Matrix

@[expose] public section

namespace Harris

noncomputable abbrev σR : K3 →+* ℝ := σ.toRingHom

noncomputable def mR {m n : ℕ} (A : Matrix (Fin m) (Fin n) K3) : Matrix (Fin m) (Fin n) ℝ := A.map σR
noncomputable def vR {n : ℕ} (v : Fin n → K3) : Fin n → ℝ := fun i => σR (v i)

lemma mR_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) K3) (B : Matrix (Fin m) (Fin n) K3) :
    mR (A * B) = mR A * mR B := Matrix.map_mul
lemma mR_one {n : ℕ} : mR (1 : Matrix (Fin n) (Fin n) K3) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
lemma mR_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) K3) : mR A.transpose = (mR A).transpose := rfl
lemma mR_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) K3) (v : Fin n → K3) :
    vR (A.mulVec v) = (mR A).mulVec (vR v) := by
  funext i; simp [vR, mR, Matrix.mulVec, dotProduct, map_sum]

/-! ## Completing the square -/

lemma psd_of_ldl {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hA : L * Matrix.diagonal d * L.transpose = A) (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ A *ᵥ v := by
  rw [← hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  simp only [Matrix.vecMul_diagonal, dotProduct]
  apply Finset.sum_nonneg; intro i _
  have := hd i
  nlinarith [sq_nonneg ((L.transpose *ᵥ v) i)]

lemma complete_sq {n : ℕ} (A Ai : Matrix (Fin n) (Fin n) ℝ) (hA : A * Ai = 1) (hAs : A.transpose = A)
    (hpsd : ∀ v, 0 ≤ v ⬝ᵥ A *ᵥ v) (η u : Fin n → ℝ) (X : ℝ) :
    -X ^ 2 * (u ⬝ᵥ Ai *ᵥ u) ≤ η ⬝ᵥ A *ᵥ η + 2 * X * (u ⬝ᵥ η) := by
  have hsym : ∀ a b : Fin n → ℝ, a ⬝ᵥ A *ᵥ b = b ⬝ᵥ A *ᵥ a := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAs, dotProduct_comm]
  set w := Ai *ᵥ u with hw
  have hAw : A *ᵥ w = u := by rw [hw, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  have h := hpsd (η + X • w)
  have e1 : (η + X • w) ⬝ᵥ A *ᵥ (η + X • w) =
      η ⬝ᵥ A *ᵥ η + 2 * X * (η ⬝ᵥ A *ᵥ w) + X ^ 2 * (w ⬝ᵥ A *ᵥ w) := by
    have := hsym w η
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, this]
    ring
  rw [e1, hAw, dotProduct_comm η u, dotProduct_comm w u] at h
  nlinarith [sq_nonneg X]

/-! ## Real images of the data -/

noncomputable def Gir := mR Gim
noncomputable def Γr := mR Γm
noncomputable def D7r := mR D7m
noncomputable def Hr := mR Hm
noncomputable def Cr := mR Cm
noncomputable def Selr := mR Selm
noncomputable def Ahr := mR Ahm
noncomputable def Air := mR Aim
noncomputable def cκr := vR cκ
noncomputable def ξκr := vR ξκ
noncomputable def εR : ℝ := 7 / 50
noncomputable def κnR : ℝ := 2 / 9 * Real.sqrt 3

lemma vR_dot {n : ℕ} (v w : Fin n → K3) : vR v ⬝ᵥ vR w = σR (v ⬝ᵥ w) := by
  simp [vR, dotProduct, map_sum]

lemma σR_mk (p q : ℚ) : σR (⟨p, q⟩ : K3) = p + q * Real.sqrt 3 := σ_apply _

lemma κn_pos : 0 < κnR := by unfold κnR; positivity

lemma κn_eq : cκr ⬝ᵥ ξκr = κnR := by
  rw [cκr, ξκr, vR_dot, κn_val, σR_mk]; unfold κnR; push_cast; ring

lemma ε_eq : σR εk = εR := by rw [ε_val, σR_mk]; unfold εR; push_cast; ring

lemma Hr_eq : Hr = (1 - εR) • Gir - D7r := by
  unfold Hr Gir D7r mR Hm
  ext i j
  simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, ← ε_eq]

lemma GiΓ : Gir * Γr = 1 := by
  have h : Γr * Gir = 1 := by unfold Γr Gir; rw [← mR_mul, Γ_Gi, mR_one]
  exact mul_eq_one_comm.mp h

lemma Gi_symm_r : Gir.transpose = Gir := by unfold Gir; rw [← mR_transpose, Gi_symm]
lemma D7_symm_r : D7r.transpose = D7r := by unfold D7r; rw [← mR_transpose, D7_symm]
lemma H_symm_r : Hr.transpose = Hr := by
  rw [Hr_eq, Matrix.transpose_sub, Matrix.transpose_smul, Gi_symm_r, D7_symm_r]

lemma Gi_ξκ : Gir *ᵥ ξκr = cκr := by
  have h1 : Γr *ᵥ cκr = ξκr := by unfold Γr cκr ξκr; rw [← mR_mulVec, Γ_cκ]
  rw [← h1, Matrix.mulVec_mulVec, GiΓ, Matrix.one_mulVec]

lemma D7_ξκ_r : D7r *ᵥ ξκr = cκr := by unfold D7r cκr ξκr; rw [← mR_mulVec, D7_ξκ]

lemma H_ξκ : Hr *ᵥ ξκr = (-εR) • cκr := by
  rw [Hr_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, Gi_ξκ, D7_ξκ_r]
  ext i; simp; ring

lemma Ah_eq : Ahr = Cr.transpose * Hr * Cr := by
  unfold Ahr Cr Hr Ahm; rw [mR_mul, mR_mul, mR_transpose]

lemma Ah_Ai : Ahr * Air = 1 := by unfold Ahr Air; rw [← mR_mul, A_Ai, mR_one]

lemma Ah_symm : Ahr.transpose = Ahr := by
  rw [Ah_eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, H_symm_r,
    Matrix.mul_assoc]

lemma Ah_psd (v : Fin 6 → ℝ) : 0 ≤ v ⬝ᵥ Ahr *ᵥ v := by
  apply psd_of_ldl Ahr (mR Lm) (vR dm)
  · intro i; exact (K3.nn_iff _).mp (d_nn i)
  · have : mR (Matrix.diagonal dm) = Matrix.diagonal (vR dm) := by
      ext i j; by_cases h : i = j <;> simp [mR, vR, Matrix.diagonal, h]
    unfold Ahr; rw [← A_ldl, mR_mul, mR_mul, mR_transpose, this]

lemma C_sel_r (v : Fin 7 → ℝ) (hv : cκr ⬝ᵥ v = 0) : Cr *ᵥ (Selr *ᵥ v) = v := by
  have h : Cr * Selr + Matrix.vecMulVec (vR uv) cκr = 1 := by
    have := congrArg mR C_sel
    rw [mR_one] at this; rw [← this]
    unfold Cr Selr cκr mR
    ext i j; simp [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, vR,
      map_sum]
  have := congrArg (fun M => M *ᵥ v) h
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at this
  rw [Matrix.vecMulVec_mulVec, hv, MulOpposite.op_zero, zero_smul, add_zero] at this
  exact this

/-! ## The core inequality -/

theorem core_ineq (ξ t : Fin 7 → ℝ) (X Λ : ℝ) (hX : 0 ≤ X) (hs : |cκr ⬝ᵥ ξ| ≤ Real.sqrt 3 * X)
    (ht : |t ⬝ᵥ ξκr| ≤ Real.sqrt 3) (hΛ : (Cr.transpose *ᵥ t) ⬝ᵥ Air *ᵥ (Cr.transpose *ᵥ t) ≤ Λ) :
    -(Λ + (εR + 2) * 3 / κnR) * X ^ 2 ≤ ξ ⬝ᵥ Hr *ᵥ ξ + 2 * X * (t ⬝ᵥ ξ) := by
  have hκ := κn_pos
  set s := (cκr ⬝ᵥ ξ) / κnR with hsdef
  set v := ξ - s • ξκr with hvdef
  have hv : cκr ⬝ᵥ v = 0 := by
    rw [hvdef, dotProduct_sub, dotProduct_smul, κn_eq, smul_eq_mul, hsdef]; field_simp; ring
  set η := Selr *ᵥ v
  have hCη : Cr *ᵥ η = v := C_sel_r v hv
  have hξ : ξ = v + s • ξκr := by rw [hvdef]; abel
  have hsym : ∀ a b : Fin 7 → ℝ, a ⬝ᵥ Hr *ᵥ b = b ⬝ᵥ Hr *ᵥ a := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, H_symm_r, dotProduct_comm]
  -- the quadratic form splits
  have hvκ : v ⬝ᵥ Hr *ᵥ ξκr = 0 := by
    rw [H_ξκ, dotProduct_smul, dotProduct_comm, hv, smul_zero]
  have hκκ : ξκr ⬝ᵥ Hr *ᵥ ξκr = -εR * κnR := by
    rw [H_ξκ, dotProduct_smul, dotProduct_comm, κn_eq, smul_eq_mul]
  have hQ : ξ ⬝ᵥ Hr *ᵥ ξ = η ⬝ᵥ Ahr *ᵥ η + s ^ 2 * (-εR * κnR) := by
    have e1 : ξ ⬝ᵥ Hr *ᵥ ξ = v ⬝ᵥ Hr *ᵥ v + 2 * s * (v ⬝ᵥ Hr *ᵥ ξκr) + s ^ 2 * (ξκr ⬝ᵥ Hr *ᵥ ξκr) := by
      have := hsym ξκr v
      rw [hξ]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, this]
      ring
    have e2 : v ⬝ᵥ Hr *ᵥ v = η ⬝ᵥ Ahr *ᵥ η := by
      rw [← hCη, Ah_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec η,
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
    rw [e1, e2, hvκ, hκκ]; ring
  have hT : t ⬝ᵥ ξ = (Cr.transpose *ᵥ t) ⬝ᵥ η + s * (t ⬝ᵥ ξκr) := by
    rw [hξ, dotProduct_add, dotProduct_smul, smul_eq_mul, ← hCη, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
  have hcs := complete_sq Ahr Air Ah_Ai Ah_symm Ah_psd η (Cr.transpose *ᵥ t) X
  -- bounds on s
  have habs_s : |s| ≤ Real.sqrt 3 * X / κnR := by
    rw [hsdef, abs_div, abs_of_pos hκ]; exact div_le_div_of_nonneg_right hs hκ.le
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs2 : s ^ 2 ≤ 3 * X ^ 2 / κnR ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le habs_s) (le_of_abs_le habs_s)
    calc s ^ 2 ≤ (Real.sqrt 3 * X / κnR) ^ 2 := this
      _ = 3 * X ^ 2 / κnR ^ 2 := by rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  have hst : -(2 * X * (Real.sqrt 3 * X / κnR) * Real.sqrt 3) ≤ 2 * X * (s * (t ⬝ᵥ ξκr)) := by
    have := abs_mul s (t ⬝ᵥ ξκr)
    have h1 : |s * (t ⬝ᵥ ξκr)| ≤ (Real.sqrt 3 * X / κnR) * Real.sqrt 3 :=
      this ▸ mul_le_mul habs_s ht (abs_nonneg _) (by positivity)
    have := neg_abs_le (s * (t ⬝ᵥ ξκr))
    nlinarith
  have hΛ' : -X ^ 2 * ((Cr.transpose *ᵥ t) ⬝ᵥ Air *ᵥ (Cr.transpose *ᵥ t)) ≥ -X ^ 2 * Λ := by
    nlinarith [sq_nonneg X]
  have hεκ : 0 ≤ εR := by unfold εR; norm_num
  rw [hQ, hT]
  have key : (εR + 2) * 3 / κnR * X ^ 2 = εR * κnR * (3 * X ^ 2 / κnR ^ 2) +
      2 * X * (Real.sqrt 3 * X / κnR) * Real.sqrt 3 := by
    field_simp; rw [show Real.sqrt 3 ^ 2 = 3 by rw [Real.sq_sqrt (by norm_num)]]; ring
  have hεs : s ^ 2 * (-εR * κnR) ≥ -(εR * κnR * (3 * X ^ 2 / κnR ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hεκ hκ.le); nlinarith
  nlinarith

end Harris
