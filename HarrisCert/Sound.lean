module

public import HarrisCert.Core.Nbar
public import HarrisCert.Defs

/-!
# Soundness of the leaf and tree checks

`checkNode C fuel 0 rootLo rootHi = true`, together with valid cut bounds, implies the goal for every
point satisfying the hypotheses.
-/

open Complex

@[expose] public section

namespace Harris

/-! ## Linear algebra over `ℚ(√3)` -/

noncomputable def dotR (κ : Vec) (z : Fin 10 → ℝ) : ℝ := ∑ j, (κ j).toReal * z j

def RowOK (z : Fin 10 → ℝ) (A : Row) : Prop := dotR A.1 z ≤ A.2.toReal

lemma dotR_sub_smul (κ A : Vec) (y : ℚ) (z : Fin 10 → ℝ) :
    dotR (fun j => κ j - Q3.smul y (A j)) z = dotR κ z - y * dotR A z := by
  simp only [dotR, Q3.toReal_sub, Q3.toReal_smul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

lemma accum_spec (z : Fin 10 → ℝ) (c0 : Vec) :
    ∀ (rows : List (ℚ × Row)) (κ : Vec) (b : Q3),
      (∀ yr ∈ rows, 0 ≤ yr.1 ∧ RowOK z yr.2) →
      dotR c0 z ≤ b.toReal + dotR κ z →
      dotR c0 z ≤ (accum (κ, b) rows).2.toReal + dotR (accum (κ, b) rows).1 z := by
  intro rows
  induction rows with
  | nil => intro κ b _ h; simpa [accum] using h
  | cons yr rows ih =>
    intro κ b hrows h
    have hyr := hrows yr (by simp)
    have := ih (fun j => κ j - Q3.smul yr.1 (yr.2.1 j)) (b + Q3.smul yr.1 yr.2.2)
      (fun r hr => hrows r (by simp [hr])) (by
        rw [dotR_sub_smul, Q3.toReal_add, Q3.toReal_smul]
        have hy : (0 : ℝ) ≤ yr.1 := by exact_mod_cast hyr.1
        have hrow := hyr.2
        unfold RowOK at hrow
        nlinarith)
    simpa [accum, List.foldl] using this

lemma foldl_add_toReal (g : Fin 10 → Q3) :
    ∀ (l : List (Fin 10)) (b : Q3),
      (l.foldl (fun s j => s + g j) b).toReal = b.toReal + (l.map fun j => (g j).toReal).sum := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons j l ih => intro b; simp [List.foldl, ih]; ring

lemma sum_finRange_eq (f : Fin 10 → ℝ) : ((List.finRange 10).map f).sum = ∑ j, f j := by
  rw [Fin.sum_univ_def]

/-! ## The lifted point `z = (x, w)` -/

noncomputable def zOf (x : Fin 7 → ℝ) : Fin 10 → ℝ := fun j =>
  if h : j.val < 7 then x ⟨j.val, h⟩ else
    x (pairP ⟨j.val - 7, by omega⟩) * x (pairS ⟨j.val - 7, by omega⟩)

lemma mul_le_max_of_mem {a b x c : ℝ} (ha : a ≤ x) (hb : x ≤ b) : x * c ≤ max (a * c) (b * c) := by
  rcases le_total 0 c with hc | hc
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hb hc)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_right ha hc)

lemma min_le_mul_of_mem {a b x c : ℝ} (ha : a ≤ x) (hb : x ≤ b) : min (a * c) (b * c) ≤ x * c := by
  rcases le_total 0 c with hc | hc
  · exact min_le_of_left_le (mul_le_mul_of_nonneg_right ha hc)
  · exact min_le_of_right_le (mul_le_mul_of_nonpos_right hb hc)

lemma prod_bounds {lp hp ls hs x y : ℝ} (h1 : lp ≤ x) (h2 : x ≤ hp) (h3 : ls ≤ y) (h4 : y ≤ hs) :
    min (min (lp * ls) (lp * hs)) (min (hp * ls) (hp * hs)) ≤ x * y ∧
    x * y ≤ max (max (lp * ls) (lp * hs)) (max (hp * ls) (hp * hs)) := by
  constructor
  · have hx := min_le_mul_of_mem (c := y) h1 h2
    have hl : min (lp * ls) (lp * hs) ≤ lp * y := by
      have := min_le_mul_of_mem (c := lp) h3 h4; rw [mul_comm ls, mul_comm hs, mul_comm y] at this
      exact this
    have hh : min (hp * ls) (hp * hs) ≤ hp * y := by
      have := min_le_mul_of_mem (c := hp) h3 h4; rw [mul_comm ls, mul_comm hs, mul_comm y] at this
      exact this
    calc min (min (lp * ls) (lp * hs)) (min (hp * ls) (hp * hs)) ≤ min (lp * y) (hp * y) :=
          min_le_min hl hh
      _ ≤ x * y := hx
  · have hx := mul_le_max_of_mem (c := y) h1 h2
    have hl : lp * y ≤ max (lp * ls) (lp * hs) := by
      have := mul_le_max_of_mem (c := lp) h3 h4; rw [mul_comm ls, mul_comm hs, mul_comm y] at this
      exact this
    have hh : hp * y ≤ max (hp * ls) (hp * hs) := by
      have := mul_le_max_of_mem (c := hp) h3 h4; rw [mul_comm ls, mul_comm hs, mul_comm y] at this
      exact this
    calc x * y ≤ max (lp * y) (hp * y) := hx
      _ ≤ _ := max_le_max hl hh

lemma zOf_mem (lo hi : Fin 7 → ℚ) (x : Fin 7 → ℝ) (hx : InBox lo hi x) (j : Fin 10) :
    ((zLo lo hi j : ℚ) : ℝ) ≤ zOf x j ∧ zOf x j ≤ ((zHi lo hi j : ℚ) : ℝ) := by
  unfold zLo zHi zOf
  split_ifs with h
  · exact hx _
  · set jj : Fin 3 := ⟨j.val - 7, by omega⟩
    obtain ⟨a1, a2⟩ := hx (pairP jj)
    obtain ⟨b1, b2⟩ := hx (pairS jj)
    have := prod_bounds a1 a2 b1 b2
    push_cast
    exact this

lemma box_bound (lo hi : Fin 7 → ℚ) (x : Fin 7 → ℝ) (hx : InBox lo hi x) (κ : Vec) :
    dotR κ (zOf x) ≤ ∑ j, (Q3.qmax (κ j) (zLo lo hi j) (zHi lo hi j)).toReal := by
  unfold dotR
  apply Finset.sum_le_sum; intro j _
  obtain ⟨h1, h2⟩ := zOf_mem lo hi x hx j
  exact Q3.le_qmax _ _ _ _ h1 h2

/-! ## Validity of the rows -/

lemma toReal_Mq : Mq.toReal = M := by simp [Mq, Q3.toReal, M]; ring
lemma toReal_rq : rq.toReal = r := by simp [rq, Q3.toReal, r]; ring

/-- The complex vector of a cut. -/
noncomputable def gammaC (g : Array ℚ) : Fin 4 → ℂ := fun k => ⟨g.getD k 0, g.getD (k.val + 4) 0⟩

lemma cutRow_dot (g : Array ℚ) (nup : ℚ) (x : Fin 7 → ℝ) :
    dotR (cutRow g nup).1 (zOf x) = (∑ k, gammaC g k * amom x k).re := by
  simp [dotR, cutRow, zOf, Fin.sum_univ_succ, gammaC, amom, Complex.mul_re]
  ring

lemma uOf_norm (t : Option ℚ) : ‖(⟨(uOf t).1, (uOf t).2⟩ : ℂ)‖ = 1 := by
  rcases t with _ | t
  · rw [Complex.norm_def, Complex.normSq_apply]; simp [uOf]
  · have hpos : (0 : ℝ) < 1 + (t : ℝ) ^ 2 := by positivity
    have hsq : ((1 - (t : ℝ) ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
      field_simp; ring
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [uOf]; push_cast
    rw [show ((1 - (t : ℝ) ^ 2) / (1 + t ^ 2)) * ((1 - (t : ℝ) ^ 2) / (1 + t ^ 2)) +
        (2 * t / (1 + t ^ 2)) * (2 * t / (1 + t ^ 2)) = 1 by nlinarith [hsq]]
    simp

lemma aorbC_toC (u : ℚ × ℚ) : (fun k => C3.toC (aorbC u k)) = aorb ⟨u.1, u.2⟩ := by
  funext k
  fin_cases k <;>
    simp [aorbC, aorb, toReal_rq, Complex.ext_iff, C3.toC, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val, pow_succ] <;> ring_nf <;> simp [Q3.toReal] <;> ring

lemma reflC_toC (b : Fin 4 → C3) : (fun k => C3.toC (reflC b k)) = refl (fun k => C3.toC (b k)) := by
  funext k; simp [reflC, refl]

lemma slabRow_dot (x0 : ℚ) (b : Fin 4 → C3) (x : Fin 7 → ℝ) :
    dotR (slabRow x0 b).1 (zOf x) = -(phiB (amom x) (fun k => C3.toC (b k))).re := by
  simp [dotR, slabRow, slabS, zOf, Fin.sum_univ_succ, phiB, amom, Complex.mul_re, Complex.mul_im]
  ring

lemma slabRow_ok (C : Cert) (hx0 : C.x0 = X0) (i : ℕ) (x : Fin 7 → ℝ) (hH : Hyps x) :
    RowOK (zOf x) (slabRowOf C i) := by
  unfold RowOK slabRowOf
  set u := uOf (C.slabT.getD (i / 2) none)
  have hu := uOf_norm (C.slabT.getD (i / 2) none)
  obtain ⟨h1, h2⟩ := hH.slab ⟨u.1, u.2⟩ hu
  rw [slabRow_dot]
  simp only [slabRow, Q3.toReal_sub, Q3.toReal_ofRat, toReal_Mq, hx0]
  split_ifs
  · rw [aorbC_toC]; unfold Xslab at h1; linarith
  · rw [reflC_toC, aorbC_toC]; unfold Xslab at h2; linarith

lemma vec3_dot (iw : Fin 10) (cw : Q3) (is : Fin 10) (cs : Q3) (ip : Fin 10) (cp : Q3)
    (h1 : iw ≠ is) (h2 : iw ≠ ip) (h3 : is ≠ ip) (z : Fin 10 → ℝ) :
    dotR (vec3 iw cw is cs ip cp) z = cw.toReal * z iw + cs.toReal * z is + cp.toReal * z ip := by
  have key : ∀ j, (vec3 iw cw is cs ip cp j).toReal * z j =
      (if j = iw then cw.toReal * z j else 0) + (if j = is then cs.toReal * z j else 0) +
      (if j = ip then cp.toReal * z j else 0) := by
    intro j
    unfold vec3
    by_cases a : j = iw
    · subst a; simp [h1, h2]
    · by_cases b : j = is
      · subst b; simp [a, h3]
      · by_cases c : j = ip
        · subst c; simp [a, b]
        · simp [a, b, c]
  unfold dotR
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']

lemma mccRow_ok (lo hi : Fin 7 → ℚ) (x : Fin 7 → ℝ) (hx : InBox lo hi x) (j : Fin 3) (k : ℕ) :
    RowOK (zOf x) (mccRow lo hi j k) := by
  have hz_w : zOf x (wIdx j) = x (pairP j) * x (pairS j) := by
    fin_cases j <;> simp [zOf, wIdx, pairP, pairS]
  have hz_s : zOf x (xIdx (pairS j)) = x (pairS j) := by
    simp [zOf, xIdx]
  have hz_p : zOf x (xIdx (pairP j)) = x (pairP j) := by
    simp [zOf, xIdx]
  have hne1 : wIdx j ≠ xIdx (pairS j) := by
    fin_cases j <;> simp [wIdx, xIdx, pairS, Fin.ext_iff]
  have hne2 : wIdx j ≠ xIdx (pairP j) := by
    fin_cases j <;> simp [wIdx, xIdx, pairP, Fin.ext_iff]
  have hne3 : xIdx (pairS j) ≠ xIdx (pairP j) := by
    fin_cases j <;> simp [xIdx, pairP, pairS, Fin.ext_iff]
  obtain ⟨p1, p2⟩ := hx (pairP j)
  obtain ⟨s1, s2⟩ := hx (pairS j)
  unfold RowOK mccRow
  rcases k with _ | _ | _ | k <;>
  · simp only
    rw [vec3_dot _ _ _ _ _ _ hne1 hne2 hne3, hz_w, hz_s, hz_p]
    simp only [Q3.toReal_ofRat]; push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr p1) (sub_nonneg.mpr s1),
      mul_nonneg (sub_nonneg.mpr p2) (sub_nonneg.mpr s2),
      mul_nonneg (sub_nonneg.mpr p2) (sub_nonneg.mpr s1),
      mul_nonneg (sub_nonneg.mpr p1) (sub_nonneg.mpr s2)]

/-! ## Leaves -/

/-- Valid cut bounds: `N(γ) ≤ Nup` for every cut of the certificate. -/
def CutsGood (C : Cert) : Prop := ∀ i < C.cuts.size, Nsupp (gammaC (C.cuts.getD i default).gamma) ≤
  (C.cuts.getD i default).nup

lemma objVec_dot (x : Fin 7 → ℝ) :
    dotR (objVec true) (zOf x) = -(qform (amom x)).re := by
  simp [dotR, objVec, zOf, Fin.sum_univ_succ, qform, amom, pairP, pairS, Complex.mul_re,
    Complex.mul_im]
  ring

lemma objVec_false (z : Fin 10 → ℝ) : dotR (objVec false) z = 0 := by simp [dotR, objVec]

lemma leafRows_ok (C : Cert) (hx0 : C.x0 = X0) (hC : CutsGood C) (L : Leaf) (lo hi : Fin 7 → ℚ)
    (hL : leafIndicesOK C L = true) (x : Fin 7 → ℝ) (hx : InBox lo hi x) (hH : Hyps x) :
    ∀ yr ∈ leafRows C L lo hi, 0 ≤ yr.1 ∧ RowOK (zOf x) yr.2 := by
  unfold leafIndicesOK at hL
  simp only [Bool.and_eq_true, Array.all_eq_true, decide_eq_true_eq] at hL
  obtain ⟨⟨hc, hs⟩, hm⟩ := hL
  intro yr hyr
  unfold leafRows at hyr
  simp only [List.mem_append, List.mem_map, List.mem_filterMap, Array.mem_toList_iff] at hyr
  rcases hyr with (⟨⟨i, y⟩, hmem, rfl⟩ | ⟨⟨i, y⟩, hmem, rfl⟩) | ⟨⟨j, k, y⟩, hmem, hsome⟩
  · obtain ⟨n, hn, hnE⟩ := Array.mem_iff_getElem.mp hmem
    obtain ⟨hi1, hy⟩ := hc n hn
    rw [hnE] at hi1 hy
    refine ⟨hy, ?_⟩
    unfold RowOK
    rw [cutRow_dot]
    simp only [cutRow, Q3.toReal_ofRat]
    exact le_trans (hH.supp _) (hC i hi1)
  · obtain ⟨n, hn, hnE⟩ := Array.mem_iff_getElem.mp hmem
    obtain ⟨_, hy⟩ := hs n hn
    rw [hnE] at hy
    exact ⟨hy, slabRow_ok C hx0 i x hH⟩
  · obtain ⟨n, hn, hnE⟩ := Array.mem_iff_getElem.mp hmem
    have hy := hm n hn
    rw [hnE] at hy
    split_ifs at hsome with hj
    · cases hsome
      exact ⟨hy, mccRow_ok lo hi x hx ⟨j, hj⟩ k⟩

lemma checkLeaf_sound (C : Cert) (hx0 : C.x0 = X0) (hC : CutsGood C) (L : Leaf) (lo hi : Fin 7 → ℚ)
    (h : checkLeaf C L lo hi = true) (x : Fin 7 → ℝ) (hx : InBox lo hi x) (hH : Hyps x) : Goal x := by
  unfold checkLeaf at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hidx, hb⟩ := h
  have hrows := leafRows_ok C hx0 hC L lo hi hidx x hx hH
  have key := accum_spec (zOf x) (objVec L.opt) (leafRows C L lo hi) (objVec L.opt) 0 hrows
    (by simp)
  have hbox := box_bound lo hi x hx (accum (objVec L.opt, 0) (leafRows C L lo hi)).1
  have hbound : dotR (objVec L.opt) (zOf x) ≤ (leafBound C L lo hi).toReal := by
    unfold leafBound
    rw [foldl_add_toReal, sum_finRange_eq]
    linarith
  unfold Goal
  cases hopt : L.opt
  · rw [hopt] at hb hbound
    simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true'] at hb
    have hneg : (leafBound C L lo hi).toReal < 0 := by
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

/-! ## Tree -/

lemma checkNode_sound (C : Cert) (hx0 : C.x0 = X0) (hC : CutsGood C) :
    ∀ (fuel id : ℕ) (lo hi : Fin 7 → ℚ), checkNode C fuel id lo hi = true →
      ∀ x, InBox lo hi x → Hyps x → Goal x := by
  intro fuel
  induction fuel with
  | zero => intro id lo hi h; simp [checkNode] at h
  | succ fuel ih =>
    intro id lo hi h x hx hH
    unfold checkNode at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · exact checkLeaf_sound C hx0 hC _ lo hi h x hx hH
    · split_ifs at h with hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, _⟩, hl⟩, hr⟩ := h
      set vf : Fin 7 := ⟨_, hv⟩
      rcases le_total (x vf) (_ : ℚ) with hxm | hxm
      · apply ih _ lo (Function.update hi vf _) hl x _ hH
        intro j
        by_cases hj : j = vf
        · subst hj; simp [Function.update_self]; exact ⟨(hx _).1, hxm⟩
        · simp [Function.update_of_ne hj]; exact hx j
      · apply ih _ (Function.update lo vf _) hi hr x _ hH
        intro j
        by_cases hj : j = vf
        · subst hj; simp [Function.update_self]; exact ⟨hxm, (hx _).2⟩
        · simp [Function.update_of_ne hj]; exact hx j

end Harris
