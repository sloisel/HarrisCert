module

public import HarrisCert.Core.Nbar
public import HarrisCert.Defs

/-!
# Evaluation lemmas for coefficient-list polynomials
-/

@[expose] public section

namespace Harris

/-- Horner evaluation at a real point. -/
noncomputable def peval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: p, t => a + t * peval p t

@[simp] lemma peval_nil (t : ℝ) : peval [] t = 0 := rfl
@[simp] lemma peval_cons (a : ℚ) (p : List ℚ) (t : ℝ) : peval (a :: p) t = a + t * peval p t := rfl

lemma peval_add : ∀ (p q : List ℚ) (t : ℝ), peval (pAdd p q) t = peval p t + peval q t
  | [], q, t => by simp [pAdd]
  | a :: p, [], t => by simp [pAdd]
  | a :: p, b :: q, t => by simp [pAdd, peval_add p q t]; ring

lemma peval_scale (c : ℚ) : ∀ (p : List ℚ) (t : ℝ), peval (pScale c p) t = c * peval p t
  | [], t => by simp [pScale]
  | a :: p, t => by
    have := peval_scale c p t
    simp only [pScale, List.map_cons] at this ⊢
    simp [this]; ring

lemma peval_mul : ∀ (p q : List ℚ) (t : ℝ), peval (pMul p q) t = peval p t * peval q t
  | [], q, t => by simp [pMul]
  | a :: p, q, t => by
    simp only [pMul, peval_add, peval_scale, peval_cons, peval_mul p q t]; ring

lemma peval_pow (p : List ℚ) (t : ℝ) : ∀ n, peval (pPow p n) t = peval p t ^ n
  | 0 => by simp [pPow]
  | n + 1 => by simp [pPow, peval_mul, peval_pow p t n]; ring

lemma continuous_peval (p : List ℚ) : Continuous (fun t => peval p t) := by
  induction p with
  | nil => simp only [peval_nil]; exact continuous_const
  | cons a p ih => simp only [peval_cons]; exact continuous_const.add (continuous_id.mul ih)

/-- `peval` as a power sum with an index offset. -/
lemma zipIdx_sum (t : ℝ) : ∀ (p : List ℚ) (n : ℕ),
    ((p.zipIdx n).map fun ci => (ci.1 : ℝ) * t ^ ci.2).sum = t ^ n * peval p t
  | [], n => by simp
  | a :: p, n => by
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum t p (n + 1), peval_cons]
    ring

lemma peval_eq_sum (p : List ℚ) (t : ℝ) :
    peval p t = ((p.zipIdx).map fun ci => (ci.1 : ℝ) * t ^ ci.2).sum := by
  rw [show p.zipIdx = p.zipIdx 0 from rfl, zipIdx_sum]; simp

/-- Tail bound: `|Σ_{k≥n} c_k s^{k+1}| ≤ Σ |c_k| δ^{k+1}` for `|s| ≤ δ`. -/
lemma tail_bound (s δ : ℝ) (hs : |s| ≤ δ) : ∀ (l : List ℚ) (n : ℕ),
    |s ^ (n + 1) * peval l s| ≤ ((l.zipIdx n).map fun ck => |(ck.1 : ℝ)| * δ ^ (ck.2 + 1)).sum
  | [], n => by simp
  | c :: l, n => by
    have ih := tail_bound s δ hs l (n + 1)
    have hδ : 0 ≤ δ := le_trans (abs_nonneg s) hs
    have hpow : |s| ^ (n + 1) ≤ δ ^ (n + 1) := pow_le_pow_left₀ (abs_nonneg s) hs _
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, peval_cons]
    push_cast at ih ⊢
    calc |s ^ (n + 1) * (c + s * peval l s)|
        = |c * s ^ (n + 1) + s ^ (n + 1 + 1) * peval l s| := by ring_nf
      _ ≤ |c * s ^ (n + 1)| + |s ^ (n + 1 + 1) * peval l s| := abs_add_le _ _
      _ ≤ |(c : ℝ)| * δ ^ (n + 1) + _ := by
          gcongr
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)

lemma peval_ge_tail (K : List ℚ) (s : ℝ) (δ : ℚ) (hs : |s| ≤ δ) :
    ((K.getD 0 0 - tailAbs K δ : ℚ) : ℝ) ≤ peval K s := by
  rcases K with _ | ⟨c, l⟩
  · simp [tailAbs]
  · have := tail_bound s δ hs l 0
    simp only [zero_add, pow_one] at this
    have hc : ((tailAbs (c :: l) δ : ℚ) : ℝ) =
        (l.zipIdx.map fun ck => |(ck.1 : ℝ)| * (δ : ℝ) ^ (ck.2 + 1)).sum := by
      simp only [tailAbs, List.drop_one, List.tail_cons]
      rw [Rat.cast_list_sum, List.map_map]; congr 1; apply List.map_congr_left; intro x _; simp
    rw [Rat.cast_sub, hc]; simp only [List.getD_cons_zero, peval_cons]
    have h2 := neg_abs_le (s * peval l s)
    linarith

lemma peval_split2 (G : List ℚ) (s : ℝ) :
    peval G s = (G.getD 0 0 : ℝ) + s * (G.getD 1 0 : ℝ) + s ^ 2 * peval (G.drop 2) s := by
  rcases G with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp <;> ring

end Harris
