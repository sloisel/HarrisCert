module

public import HarrisCert.Circle

/-!
# Soundness of the cut check, and of the whole certificate check
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace Harris

lemma piLo_le_pi : (piLo : ℝ) ≤ Real.pi := by
  have h := Real.pi_gt_d20
  have : (piLo : ℝ) = 3.14159265358979323846 := by norm_num [piLo]
  rw [this]; exact h.le

lemma piLo_pos : (0 : ℝ) < piLo := by norm_num [piLo]

/-- `N(γ) ≤ N̄(γ)`. -/
lemma nbar_sound (n : ℕ) (hn : 0 < n) (hcells : cellsOK (mkCells n) = true) (g : Array ℚ)
    (h1 : (absSq (Psig g 1)).length ≤ 13) (h2 : (absSq (Psig g (-1))).length ≤ 13) :
    Nsupp (gammaC g) ≤ (nbar (mkCells n) g : ℝ) := by
  rw [Nsupp_eq]
  have hp := integral_le_cells n hn hcells (absSq (Psig g 1)) (absSq_nonneg _) h1
  have hm := integral_le_cells n hn hcells (absSq (Psig g (-1))) (absSq_nonneg _) h2
  have nonneg (σ : ℚ) : 0 ≤ ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g σ)) t) * wfun t :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t _ => mul_nonneg (Real.sqrt_nonneg _) (wfun_pos t).le)
  have n1 := nonneg 1
  have n2 := nonneg (-1)
  set Ip := ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g 1)) t) * wfun t
  set Im := ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig g (-1))) t) * wfun t
  set S := ((((mkCells n).toList.foldl (fun s c => s + cellBound (absSq (Psig g 1)) c) 0 : ℚ) : ℝ) +
    (((mkCells n).toList.foldl (fun s c => s + cellBound (absSq (Psig g (-1))) c) 0 : ℚ) : ℝ))
  have hS : Ip + Im ≤ S := by linarith
  have hnbar : (nbar (mkCells n) g : ℝ) = S / piLo := by
    simp only [nbar, S]; push_cast; ring
  rw [hnbar]
  have hpi := Real.pi_pos
  have hS0 : 0 ≤ S := by linarith
  calc 1 / Real.pi * (Ip + Im) ≤ 1 / Real.pi * S := by
        apply mul_le_mul_of_nonneg_left hS; positivity
    _ = S / Real.pi := by ring
    _ ≤ S / piLo := div_le_div_of_nonneg_left hS0 piLo_pos piLo_le_pi

lemma chunkOK_get (C : Cert) (lo hi : ℕ) (h : chunkOK C lo hi = true) (i : ℕ) (h1 : lo ≤ i)
    (h2 : i < hi) : cutOK (mkCells C.cells) (C.cuts.getD i default) = true := by
  unfold chunkOK at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨h1, by omega⟩)

/-- The certificate check implies the goal for every point satisfying the hypotheses. -/
theorem certificate_sound (C : Cert) (hbase : baseOK C = true)
    (hcuts : ∀ i < C.cuts.size, cutOK (mkCells C.cells) (C.cuts.getD i default) = true) :
    ∀ x, Hyps x → Goal x := by
  unfold baseOK at hbase
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbase
  obtain ⟨⟨⟨hx0, hn⟩, hcells⟩, htree⟩ := hbase
  have hgood : CutsGood C := by
    intro i hi
    have h := hcuts i hi
    unfold cutOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact le_trans (nbar_sound _ hn hcells _ h1 h2) (by exact_mod_cast h3)
  intro x hH
  exact checkNode_sound C hx0 hgood _ 0 rootLo rootHi htree x hH.box hH

end Harris
