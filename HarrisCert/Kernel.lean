module

public import HarrisCert.Core.Kernel
public import HarrisCert.NbarZSound

/-!
# Soundness of the kernel-checked certificate format
-/

@[expose] public section

namespace Harris

/-! ## Soundness -/

/-- Every point of the box satisfying the hypotheses satisfies the goal. -/
def Covered (lo hi : Fin 7 → ℚ) : Prop := ∀ x, InBox lo hi x → Hyps x → Goal x

lemma Tables.cellsFor_mk (T : Tables) (hT : T.Valid) (n : ℕ)
    (hn : n = 32 ∨ n = 64 ∨ n = 128 ∨ n = 256) :
    T.cellsFor n = (mkCells n).toList.map CellData.toZ ∧ cellsOK (mkCells n) = true := by
  obtain ⟨h1, h2, h3, h4, k1, k2, k3, k4⟩ := hT
  unfold Tables.cellsFor
  rcases hn with rfl | rfl | rfl | rfl
  · simp [h1, k1]
  · simp [h2, k2]
  · simp [h3, k3]
  · simp [h4, k4]

lemma ALeaf.check_sound (T : Tables) (hT : T.Valid) (L : ALeaf) (lo hi : Fin 7 → ℚ)
    (h : L.check T lo hi = true) : Covered lo hi := by
  intro x hx hH
  unfold ALeaf.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hnb⟩, hys⟩, hym⟩, hb⟩ := h
  obtain ⟨hcf, hok⟩ := T.cellsFor_mk hT L.cells hn
  rw [hcf] at hnb
  have hN : Nsupp (gammaC (gammaQ L.G L.e)) ≤ (L.NN : ℝ) / 2 ^ L.f :=
    nbarZ_sound _ (by rcases hn with h | h | h | h <;> rw [h] <;> norm_num) hok _ _ _ _ hnb
  have hrows : ∀ yr ∈ L.rows T lo hi, 0 ≤ yr.1 ∧ RowOK (zOf x) yr.2 := by
    intro yr hyr
    unfold ALeaf.rows at hyr
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_filterMap] at hyr
    rcases hyr with rfl | (⟨⟨i, y⟩, hmem, rfl⟩ | ⟨⟨j, k, y⟩, hmem, hsome⟩)
    · refine ⟨by norm_num, ?_⟩
      unfold RowOK; rw [cutRow_dot]; simp only [cutRow, Q3.toReal_ofRat]
      refine le_trans (hH.supp _) (le_of_le_of_eq hN ?_); push_cast; ring
    · exact ⟨hys _ hmem, slabRow_ok T.cert rfl i x hH⟩
    · have hy := hym _ hmem
      split_ifs at hsome with hj
      cases hsome
      exact ⟨hy, mccRow_ok lo hi x hx ⟨j, hj⟩ k⟩
  have key := accum_spec (zOf x) (objVec L.opt) (L.rows T lo hi) (objVec L.opt) 0 hrows (by simp)
  have hbox := box_bound lo hi x hx (accum (objVec L.opt, 0) (L.rows T lo hi)).1
  have hbound : dotR (objVec L.opt) (zOf x) ≤ (L.bound T lo hi).toReal := by
    unfold ALeaf.bound
    rw [foldl_add_toReal, sum_finRange_eq]
    linarith
  unfold Goal
  cases hopt : L.opt
  · rw [hopt] at hb hbound
    simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true'] at hb
    have hneg : (L.bound T lo hi).toReal < 0 := by
      by_contra hc
      have := (Q3.nonneg_iff _).mpr (not_lt.mp hc)
      rw [this] at hb; exact absurd hb (by decide)
    rw [objVec_false] at hbound
    linarith
  · rw [hopt] at hb hbound
    simp only [ite_true] at hb
    have := (Q3.nonneg_iff _).mp hb
    rw [Q3.toReal_sub, toReal_Mq] at this
    rw [objVec_dot] at hbound
    linarith

lemma covered_split (lo hi : Fin 7 → ℚ) (v : Fin 7) (m : ℚ)
    (hl : Covered lo (Function.update hi v m)) (hr : Covered (Function.update lo v m) hi) :
    Covered lo hi := by
  intro x hx hH
  rcases le_total (x v) (m : ℝ) with hxm | hxm
  · apply hl x _ hH
    intro j
    by_cases hj : j = v
    · subst hj; simp [Function.update_self]; exact ⟨(hx _).1, hxm⟩
    · simp [Function.update_of_ne hj]; exact hx j
  · apply hr x _ hH
    intro j
    by_cases hj : j = v
    · subst hj; simp [Function.update_self]; exact ⟨hxm, (hx _).2⟩
    · simp [Function.update_of_ne hj]; exact hx j

lemma ATree.check_sound (T : Tables) (hT : T.Valid) :
    ∀ (t : ATree) (lo hi : Fin 7 → ℚ), t.check T lo hi = true → Covered lo hi
  | .leaf L, lo, hi, h => L.check_sound T hT lo hi h
  | .split v m l r, lo, hi, h => by
    unfold ATree.check at h
    split_ifs at h with hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨_, hl⟩, hr⟩ := h
    exact covered_split lo hi ⟨v, hv⟩ m (ATree.check_sound T hT l _ _ hl) (ATree.check_sound T hT r _ _ hr)

/-! ## Skeleton joining separately checked subtrees -/

lemma Skel.check_sound (boxes : ℕ → (Fin 7 → ℚ) × (Fin 7 → ℚ))
    (hsub : ∀ k, Covered (boxes k).1 (boxes k).2) :
    ∀ (s : Skel) (lo hi : Fin 7 → ℚ), s.check boxes lo hi = true → Covered lo hi
  | .sub k, lo, hi, h => by
    unfold Skel.check at h
    simp only [decide_eq_true_eq] at h
    have e1 : lo = (boxes k).1 := funext fun j => (h j).1
    have e2 : hi = (boxes k).2 := funext fun j => (h j).2
    rw [e1, e2]; exact hsub k
  | .split v m l r, lo, hi, h => by
    unfold Skel.check at h
    split_ifs at h with hv
    simp only [Bool.and_eq_true] at h
    exact covered_split lo hi ⟨v, hv⟩ m (Skel.check_sound boxes hsub l _ _ h.1)
      (Skel.check_sound boxes hsub r _ _ h.2)

/-- An empty box is covered. -/
lemma covered_empty (lo hi : Fin 7 → ℚ) (j : Fin 7) (h : hi j < lo j) : Covered lo hi := by
  intro x hx _
  have := hx j
  have : (hi j : ℝ) < lo j := by exact_mod_cast h
  linarith [(hx j).1, (hx j).2]

end Harris
