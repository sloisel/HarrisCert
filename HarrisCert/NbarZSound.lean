module

public import HarrisCert.Core.NbarZ
public import HarrisCert.NbarSound

/-!
# Soundness of the integer `N̄` check
-/

open Complex MeasureTheory intervalIntegral

@[expose] public section

namespace Harris

/-! ## Integer polynomials as rational ones -/

abbrev zq (p : List ℤ) : List ℚ := p.map (Int.cast : ℤ → ℚ)

lemma zAdd_map : ∀ p q : List ℤ, zq (zAdd p q) = pAdd (zq p) (zq q)
  | [], q => by simp [zAdd, pAdd]
  | a :: p, [] => by simp [zAdd, pAdd]
  | a :: p, b :: q => by simp [zAdd, pAdd, zAdd_map p q]

lemma zScale_map (c : ℤ) (p : List ℤ) : zq (zScale c p) = pScale c (zq p) := by
  simp [zScale, pScale, List.map_map, Function.comp_def]

lemma zMul_map : ∀ p q : List ℤ, zq (zMul p q) = pMul (zq p) (zq q)
  | [], q => by simp [zMul, pMul]
  | a :: p, q => by
    simp only [zMul, pMul, List.map_cons, zAdd_map, zScale_map, zMul_map p q]
    simp

noncomputable def cevalZ (P : ZPoly) (t : ℝ) : ℂ := cevalC (zq P.1, zq P.2) t

lemma cevalZ_mul (a b : ZPoly) (t : ℝ) : cevalZ (zcMul a b) t = cevalZ a t * cevalZ b t := by
  unfold cevalZ zcMul
  simp only [zAdd_map, zMul_map, zScale_map]
  rw [← cevalC_mul]; rfl

lemma cevalZ_pow (p : ZPoly) (t : ℝ) : ∀ n, cevalZ (zcPow p n) t = cevalZ p t ^ n
  | 0 => by apply Complex.ext <;> simp [cevalZ, cevalC, zcPow]
  | n + 1 => by rw [zcPow, cevalZ_mul, cevalZ_pow p t n]; ring

lemma cevalZ_basis (k : ℕ) (t : ℝ) :
    cevalZ (basisZ k) t = (1 + (t : ℂ) * I) ^ (2 * k) * (1 + (t : ℂ) ^ 2) ^ (3 - k) := by
  have h1 : cevalZ ([1], [0, 1]) t = 1 + (t : ℂ) * I := by apply Complex.ext <;> simp [cevalZ, cevalC]
  have h2 : cevalZ ([1, 0, 1], []) t = 1 + (t : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [cevalZ, cevalC, pow_two]
  rw [basisZ, cevalZ_mul, cevalZ_pow, cevalZ_pow, h1, h2]

noncomputable def psigTermZ (G : Array ℤ) (σ : ℤ) (t : ℝ) (k : ℕ) : ℂ :=
  (((σ ^ k : ℤ) : ℂ) * ⟨G.getD k 0, G.getD (k + 4) 0⟩) * cevalZ (basisZ k) t

lemma intpow_re (σ : ℤ) (k : ℕ) : ((σ : ℂ) ^ k).re = (σ : ℝ) ^ k := by
  rw [show (σ : ℂ) = ((σ : ℝ) : ℂ) by simp, ← Complex.ofReal_pow, Complex.ofReal_re]

lemma intpow_im (σ : ℤ) (k : ℕ) : ((σ : ℂ) ^ k).im = 0 := by
  rw [show (σ : ℂ) = ((σ : ℝ) : ℂ) by simp, ← Complex.ofReal_pow, Complex.ofReal_im]

lemma cevalZ_step (G : Array ℤ) (σ : ℤ) (acc : ZPoly) (k : ℕ) (t : ℝ) :
    cevalZ (psigStepZ G σ acc k) t = cevalZ acc t + psigTermZ G σ t k := by
  unfold cevalZ psigStepZ psigTermZ cevalZ
  apply Complex.ext <;>
    simp [cevalC, zAdd_map, zScale_map, peval_add, peval_scale, intpow_re, intpow_im] <;> ring

lemma cevalZ_foldl (G : Array ℤ) (σ : ℤ) (t : ℝ) :
    ∀ (l : List ℕ) (acc : ZPoly),
      cevalZ (l.foldl (psigStepZ G σ) acc) t = cevalZ acc t + (l.map (psigTermZ G σ t)).sum
  | [], acc => by simp
  | k :: l, acc => by rw [List.foldl_cons, cevalZ_foldl G σ t l, cevalZ_step]; simp; ring


lemma gammaQ_getD (G : Array ℤ) (e : ℕ) (k : ℕ) :
    (gammaQ G e).getD k 0 = (G.getD k 0 : ℚ) / 2 ^ e := by
  unfold gammaQ
  by_cases hk : k < G.size
  · simp [Array.getD, hk]
  · simp [Array.getD, hk]

/-- `P_σ` from the integer data is `2^e` times `P_σ` from `γ = G/2^e`. -/
lemma cevalZ_Psig (G : Array ℤ) (e : ℕ) (σ : ℤ) (t : ℝ) :
    cevalZ (PsigZ G σ) t = (2 : ℂ) ^ e * cevalC (Psig (gammaQ G e) σ) t := by
  have h0 : cevalZ (([], []) : ZPoly) t = 0 := by apply Complex.ext <;> simp [cevalZ, cevalC]
  rw [PsigZ, cevalZ_foldl, h0, zero_add, cevalC_Psig]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Fin.sum_univ_four, psigTermZ,
    cevalZ_basis, gammaC, gammaQ_getD, Complex.mk_eq_add_mul_I]
  have h2 : (2 : ℂ) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  push_cast
  field_simp
  ring

lemma pevalZ_absSq (P : ZPoly) (t : ℝ) : peval (zq (absSqZ P)) t = ‖cevalZ P t‖ ^ 2 := by
  unfold absSqZ
  rw [zAdd_map, zMul_map, zMul_map]
  have := peval_absSq (zq P.1, zq P.2) t
  unfold absSq at this
  exact this

lemma sqrt_absSqZ (G : Array ℤ) (e : ℕ) (σ : ℤ) (t : ℝ) :
    Real.sqrt (peval (zq (absSqZ (PsigZ G σ))) t) =
      2 ^ e * Real.sqrt (peval (absSq (Psig (gammaQ G e) σ)) t) := by
  rw [pevalZ_absSq, Real.sqrt_sq (norm_nonneg _), cevalZ_Psig G e, norm_mul, norm_pow, sqrt_absSq]
  simp

/-! ## Cells -/

lemma roundUp_scaled (x : ℚ) : (((roundUp x 96 * 2 ^ 96).num : ℤ) : ℚ) / 2 ^ 96 = roundUp x 96 := by
  have h : roundUp x 96 * 2 ^ 96 = ((⌈x * 2 ^ 96⌉ : ℤ) : ℚ) := by
    unfold roundUp; field_simp
  rw [h, Rat.num_intCast, ← h]; field_simp

lemma roundDn_scaled (x : ℚ) : (((roundDn x 96 * 2 ^ 96).num : ℤ) : ℚ) / 2 ^ 96 = roundDn x 96 := by
  have h : roundDn x 96 * 2 ^ 96 = ((⌊x * 2 ^ 96⌋ : ℤ) : ℚ) := by
    unfold roundDn; field_simp
  rw [h, Rat.num_intCast, ← h]; field_simp

lemma toZ_hi (n j i : ℕ) :
    (((mkCell n j).toZ.hi.getD i 0 : ℤ) : ℚ) / 2 ^ 96 = (mkCell n j).muHi.getD i 0 := by
  by_cases hi : i < 13
  · simp [CellData.toZ, mkCell, Array.getD, hi, roundUp_scaled]
  · simp [CellData.toZ, mkCell, Array.getD, hi]

lemma toZ_lo (n j i : ℕ) :
    (((mkCell n j).toZ.lo.getD i 0 : ℤ) : ℚ) / 2 ^ 96 = (mkCell n j).muLo.getD i 0 := by
  by_cases hi : i < 13
  · simp [CellData.toZ, mkCell, Array.getD, hi, roundDn_scaled]
  · simp [CellData.toZ, mkCell, Array.getD, hi]

lemma zip_cast_sum (hi lo : ℕ → ℤ) (mh ml : ℕ → ℚ) (hh : ∀ i, (hi i : ℚ) / 2 ^ 96 = mh i)
    (hl : ∀ i, (lo i : ℚ) / 2 ^ 96 = ml i) : ∀ (Q : List ℤ) (n : ℕ),
    (((zq Q).zipIdx n).map fun qi => qi.1 * (if 0 ≤ qi.1 then mh qi.2 else ml qi.2)).sum =
      (((Q.zipIdx n).map fun qi => qi.1 * (if 0 ≤ qi.1 then hi qi.2 else lo qi.2)).sum : ℤ) / 2 ^ 96
  | [], n => by simp
  | q :: Q, n => by
    simp only [zq, List.map_cons, List.zipIdx_cons, List.sum_cons]
    have ih := zip_cast_sum hi lo mh ml hh hl Q (n + 1)
    simp only [zq] at ih
    rw [ih]; push_cast
    by_cases h : 0 ≤ q
    · have h' : (0 : ℚ) ≤ q := by exact_mod_cast h
      simp only [h, h', if_true]; rw [← hh]; ring
    · have h' : ¬ (0 : ℚ) ≤ q := by exact_mod_cast h
      simp only [h, h', if_false]; rw [← hl]; ring

/-- One cell with integer data: `∫ √Q w ≤ S / 2⁹⁶`. -/
lemma cellZ_bound (n j : ℕ) (hn : 0 < n) (hok : (mkCell n j).ok = true) (Q : List ℤ)
    (hQ : ∀ t, 0 ≤ peval (zq Q) t) (hlen : Q.length ≤ 13) (hz : cellOKZ Q (mkCell n j).toZ = true) :
    ∫ t in ((mkCell n j).a : ℝ)..((mkCell n j).b : ℝ), Real.sqrt (peval (zq Q) t) * wfun t ≤
      ((cellS Q (mkCell n j).toZ : ℕ) : ℝ) / 2 ^ 96 := by
  unfold cellOKZ at hz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
  obtain ⟨hA, hAB⟩ := hz
  set S := cellS Q (mkCell n j).toZ with hSdef
  set A := (mkCell n j).toZ.hi.getD 0 0 with hAdef
  set B := cellB Q (mkCell n j).toZ with hBdef
  have hS : 1 ≤ S := by simp [hSdef, cellS, isqrtUp]
  set a : ℚ := (A : ℚ) / 2 ^ 96 with ha
  set s : ℚ := (S : ℚ) / 2 ^ 96 with hs
  set b : ℚ := (B : ℚ) / 2 ^ 96 with hb
  have ha0 : 0 < a := by
    have : (0 : ℚ) < A := by exact_mod_cast hA
    positivity
  have hs0 : 0 < s := by
    have : (0 : ℚ) < S := by exact_mod_cast hS
    positivity
  have hlenq : (zq Q).length ≤ 13 := by simpa using hlen
  have key := mkCell_bound_lam n j hn hok (zq Q) hQ hlenq (s / a) (by positivity)
  have hBq : ((zq Q).zipIdx.map fun qi => qi.1 * (if 0 ≤ qi.1 then (mkCell n j).muHi.getD qi.2 0
      else (mkCell n j).muLo.getD qi.2 0)).sum = b := by
    have := zip_cast_sum (fun i => (mkCell n j).toZ.hi.getD i 0) (fun i => (mkCell n j).toZ.lo.getD i 0)
      (fun i => (mkCell n j).muHi.getD i 0) (fun i => (mkCell n j).muLo.getD i 0)
      (fun i => toZ_hi n j i) (fun i => toZ_lo n j i) Q 0
    rw [show (zq Q).zipIdx = (zq Q).zipIdx 0 from rfl, this, hb, hBdef]; rfl
  have hA0 : (mkCell n j).muHi.getD 0 0 = a := by rw [← toZ_hi]
  rw [hBq, hA0] at key
  have hab : a * b ≤ s ^ 2 := by
    have h1 : (A : ℚ) * B ≤ (S : ℚ) * S := by exact_mod_cast hAB
    have e1 : a * b = (A : ℚ) * B / (2 ^ 96 * 2 ^ 96) := by rw [ha, hb]; ring
    have e2 : s ^ 2 = (S : ℚ) * S / (2 ^ 96 * 2 ^ 96) := by rw [hs]; ring
    rw [e1, e2]; exact div_le_div_of_nonneg_right h1 (by positivity)
  have hq : b / (2 * (s / a)) + s / a * a / 2 ≤ s := by
    have e : b / (2 * (s / a)) + s / a * a / 2 = a * b / (2 * s) + s / 2 := by field_simp
    rw [e]
    have : a * b / (2 * s) ≤ s ^ 2 / (2 * s) := div_le_div_of_nonneg_right hab (by positivity)
    have e2 : s ^ 2 / (2 * s) = s / 2 := by field_simp
    linarith
  calc _ ≤ _ := key
    _ ≤ ((s : ℚ) : ℝ) := by exact_mod_cast hq
    _ = _ := by rw [hs]; push_cast; ring


lemma sum_range_mapN (g : ℕ → ℕ) : ∀ m, ((List.range m).map g).sum = ∑ k ∈ Finset.range m, g k
  | 0 => by simp
  | m + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_mapN g m,
      Finset.sum_range_succ]; simp

lemma sumS_eq (Q : List ℤ) (n : ℕ) :
    sumS Q ((mkCells n).toList.map CellData.toZ) = ∑ k ∈ Finset.range n, cellS Q (mkCell n k).toZ := by
  unfold sumS mkCells
  simp only [List.map_toArray, List.toList_toArray, List.map_map]
  exact sum_range_mapN _ n

/-- The integral over `[-1,1]` with integer cells. -/
lemma integral_le_cellsZ (n : ℕ) (hn : 0 < n) (hok : cellsOK (mkCells n) = true) (Q : List ℤ)
    (hQ : ∀ t, 0 ≤ peval (zq Q) t) (hlen : Q.length ≤ 13)
    (hz : ((mkCells n).toList.map CellData.toZ).all (cellOKZ Q) = true) :
    ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (zq Q) t) * wfun t ≤
      ((sumS Q ((mkCells n).toList.map CellData.toZ) : ℕ) : ℝ) / 2 ^ 96 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set pt : ℕ → ℝ := fun k => -1 + 2 * k / n with hpt
  have hcont : Continuous fun t => Real.sqrt (peval (zq Q) t) * wfun t :=
    (Real.continuous_sqrt.comp (continuous_peval _)).mul continuous_wfun
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t => Real.sqrt (peval (zq Q) t) * wfun t) (a := pt) (n := n)
    (fun k _ => hcont.intervalIntegrable _ _)
  have h0 : pt 0 = -1 := by simp [hpt]
  have hN : pt n = 1 := by simp only [hpt]; field_simp; ring
  rw [h0, hN] at hsum
  rw [← hsum, sumS_eq]; push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [List.all_eq_true] at hz
  have hzk := hz _ (by
    simp only [mkCells, List.map_toArray, List.toList_toArray, List.map_map, List.mem_map,
      List.mem_range, Function.comp_apply]; exact ⟨k, hk', rfl⟩)
  have := cellZ_bound n k hn (cellsOK_get n hok k hk') Q hQ hlen hzk
  have ha : ((mkCell n k).a : ℝ) = pt k := by rw [mkCell_a]; push_cast; rfl
  have hb : ((mkCell n k).b : ℝ) = pt (k + 1) := by
    rw [mkCell_b]; push_cast; simp only [hpt]; push_cast; ring
  rw [ha, hb] at this
  exact this

set_option maxHeartbeats 2000000 in
/-- `N(G / 2^e) ≤ NN / 2^f` from the integer check. -/
theorem nbarZ_sound (n : ℕ) (hn : 0 < n) (hok : cellsOK (mkCells n) = true) (G : Array ℤ) (e : ℕ)
    (NN : ℤ) (f : ℕ) (h : nbarZOK ((mkCells n).toList.map CellData.toZ) G e NN f = true) :
    Nsupp (gammaC (gammaQ G e)) ≤ (NN : ℝ) / 2 ^ f := by
  simp only [nbarZOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hl1, hl2⟩, hz1⟩, hz2⟩, hfin⟩ := h
  set cz := (mkCells n).toList.map CellData.toZ
  have hQ (σ : ℤ) : ∀ t, 0 ≤ peval (zq (absSqZ (PsigZ G σ))) t := fun t => by
    rw [pevalZ_absSq]; positivity
  have i1 := integral_le_cellsZ n hn hok _ (hQ 1) hl1 hz1
  have i2 := integral_le_cellsZ n hn hok _ (hQ (-1)) hl2 hz2
  have r1 : ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (zq (absSqZ (PsigZ G 1))) t) * wfun t =
      2 ^ e * ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig (gammaQ G e) 1)) t) * wfun t := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; rw [sqrt_absSqZ]; push_cast; ring
  have r2 : ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (zq (absSqZ (PsigZ G (-1)))) t) * wfun t =
      2 ^ e * ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig (gammaQ G e) (-1))) t) * wfun t := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; rw [sqrt_absSqZ]; push_cast; ring
  rw [Nsupp_eq]
  set Ip := ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig (gammaQ G e) 1)) t) * wfun t
  set Im := ∫ t in (-1 : ℝ)..1, Real.sqrt (peval (absSq (Psig (gammaQ G e) (-1))) t) * wfun t
  set Sp := sumS (absSqZ (PsigZ G 1)) cz
  set Sm := sumS (absSqZ (PsigZ G (-1))) cz
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  have hIp : 2 ^ e * Ip ≤ (Sp : ℝ) / 2 ^ 96 := by rw [← r1]; exact i1
  have hIm : 2 ^ e * Im ≤ (Sm : ℝ) / 2 ^ 96 := by rw [← r2]; exact i2
  have hfinR : ((Sp + Sm : ℕ) : ℝ) * 10 ^ 20 * 2 ^ f ≤
      (NN : ℝ) * 314159265358979323846 * 2 ^ (96 + e) := by exact_mod_cast hfin
  have hpi := piLo_le_pi
  have hpi0 := piLo_pos
  have hpiLo : (piLo : ℝ) = 314159265358979323846 / 10 ^ 20 := by norm_num [piLo]
  set T : ℝ := ((Sp + Sm : ℕ) : ℝ)
  have hT0 : 0 ≤ T := by positivity
  have hIpm : Ip + Im ≤ T / 2 ^ (96 + e) := by
    have : 2 ^ e * (Ip + Im) ≤ T / 2 ^ 96 := by simp only [T]; push_cast; linarith
    rw [pow_add, ← div_div, le_div_iff₀ h2e]; linarith
  have hpos : (0 : ℝ) < 2 ^ (96 + e) := by positivity
  calc 1 / Real.pi * (Ip + Im) ≤ 1 / Real.pi * (T / 2 ^ (96 + e)) :=
        mul_le_mul_of_nonneg_left hIpm (by positivity)
    _ ≤ 1 / piLo * (T / 2 ^ (96 + e)) :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hpi0 hpi) (by positivity)
    _ = T * 10 ^ 20 / (314159265358979323846 * 2 ^ (96 + e)) := by rw [hpiLo]; field_simp
    _ ≤ (NN : ℝ) / 2 ^ f := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hfinR]

end Harris
