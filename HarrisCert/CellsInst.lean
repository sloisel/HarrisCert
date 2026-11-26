module

public import HarrisCert.Cells

/-!
# The cells computed by `mkCell`, and the integral over `[-1,1]`
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace Harris

lemma roundUp_ge (x : ℚ) (e : ℕ) : x ≤ roundUp x e := by
  unfold roundUp
  have h : (0 : ℚ) < 2 ^ e := by positivity
  rw [le_div_iff₀ h]; exact Int.le_ceil _

lemma roundDn_le (x : ℚ) (e : ℕ) : roundDn x e ≤ x := by
  unfold roundDn
  have h : (0 : ℚ) < 2 ^ e := by positivity
  rw [div_le_iff₀ h]; exact Int.floor_le _

lemma lamOf_pos (A B : ℚ) : 0 < lamOf A B := by
  unfold lamOf
  dsimp only
  split_ifs with h1 h2
  · norm_num
  · apply div_pos
    · exact_mod_cast Nat.pos_of_ne_zero h2
    · positivity
  · norm_num

lemma mkCell_a (n j : ℕ) : (mkCell n j).a = -1 + 2 * j / n := rfl
lemma mkCell_b (n j : ℕ) : (mkCell n j).b = -1 + 2 * j / n + 2 / n := rfl

/-- One cell of `mkCell`. -/
lemma mkCell_bound (n j : ℕ) (hn : 0 < n) (hok : (mkCell n j).ok = true) (Q : List ℚ)
    (hQ : ∀ t, 0 ≤ peval Q t) (hlen : Q.length ≤ 13) :
    ∫ t in ((mkCell n j).a : ℝ)..((mkCell n j).b : ℝ), Real.sqrt (peval Q t) * wfun t ≤
      (cellBound Q (mkCell n j) : ℝ) := by
  set c := mkCell n j with hc
  -- the quadratic U
  set Uf : ℝ → ℝ := fun t => (c.w0 : ℝ) + c.w1 * (t - c.m) + c.c2 * (t - c.m) ^ 2 with hUf
  have hUc : Continuous Uf := by rw [hUf]; fun_prop
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : (c.a : ℝ) ≤ c.b := by
    rw [hc, mkCell_a, mkCell_b]; push_cast
    have : (0 : ℝ) ≤ 2 / n := by positivity
    linarith
  -- w ≤ U on the cell, from the `ok` flag
  have hwU : ∀ t ∈ Set.Icc (c.a : ℝ) c.b, wfun t ≤ Uf t := by
    intro t ht
    have ha : (c.a : ℝ) = -1 + 2 * (j : ℝ) / n := by rw [hc, mkCell_a]; push_cast; ring
    have hb : (c.b : ℝ) = -1 + 2 * (j : ℝ) / n + 2 / n := by rw [hc, mkCell_b]; push_cast; ring
    have hm : (c.m : ℝ) = -1 + 2 * (j : ℝ) / n + 1 / n := by
      have : c.m = ((-1 + 2 * j / n) + (-1 + 2 * j / n + 2 / n)) / 2 := by rw [hc]; rfl
      rw [this]; push_cast; ring
    have htm : |t - c.m| ≤ ((1 / n : ℚ) : ℝ) := by
      obtain ⟨h1, h2⟩ := ht
      rw [ha] at h1; rw [hb] at h2; rw [hm]; push_cast
      have e : (2 : ℝ) / n = 2 * (1 / n) := by ring
      rw [abs_le]; constructor <;> linarith
    have hok' := hok
    simp only [hc, mkCell, Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨⟨hG0, hG1⟩, _⟩, hK⟩ := hok'
    exact w_le_U _ _ _ _ _ _ _ _ rfl rfl rfl hG0 hG1 hK t htm
  -- exact moments
  have hmom : ∀ i, ∫ t in (c.a : ℝ)..c.b, t ^ i * Uf t =
      ((c.w0 - c.w1 * c.m + c.c2 * c.m ^ 2) * powInt c.a c.b i +
        (c.w1 - 2 * c.c2 * c.m) * powInt c.a c.b (i + 1) + c.c2 * powInt c.a c.b (i + 2) : ℚ) := by
    intro i
    rw [← moment_formula]
    congr 1; funext t; rw [hUf]; push_cast; ring
  have hhi : ∀ i < 13, ∫ t in (c.a : ℝ)..c.b, t ^ i * Uf t ≤ (c.muHi.getD i 0 : ℝ) := by
    intro i hi
    rw [hmom]
    have : c.muHi.getD i 0 = roundUp ((c.w0 - c.w1 * c.m + c.c2 * c.m ^ 2) * powInt c.a c.b i +
        (c.w1 - 2 * c.c2 * c.m) * powInt c.a c.b (i + 1) + c.c2 * powInt c.a c.b (i + 2)) 96 := by
      simp [hc, mkCell, Array.getD, hi]
    rw [this]; exact_mod_cast roundUp_ge _ _
  have hlo : ∀ i < 13, (c.muLo.getD i 0 : ℝ) ≤ ∫ t in (c.a : ℝ)..c.b, t ^ i * Uf t := by
    intro i hi
    rw [hmom]
    have : c.muLo.getD i 0 = roundDn ((c.w0 - c.w1 * c.m + c.c2 * c.m ^ 2) * powInt c.a c.b i +
        (c.w1 - 2 * c.c2 * c.m) * powInt c.a c.b (i + 1) + c.c2 * powInt c.a c.b (i + 2)) 96 := by
      simp [hc, mkCell, Array.getD, hi]
    rw [this]; exact_mod_cast roundDn_le _ _
  have key := cell_bound c.a c.b hab Uf hUc hwU Q hQ (fun i => c.muHi.getD i 0)
    (fun i => c.muLo.getD i 0) (fun i hi => hhi i (by omega)) (fun i hi => hlo i (by omega))
    (hhi 0 (by norm_num)) _ (lamOf_pos (c.muHi.getD 0 0)
      ((Q.zipIdx.map fun qi => qi.1 * (if 0 ≤ qi.1 then c.muHi.getD qi.2 0 else c.muLo.getD qi.2 0)).sum))
  convert key using 2
  simp only [cellBound]


/-- One cell of `mkCell`, with an arbitrary `λ > 0`. -/
lemma mkCell_bound_lam (n j : ℕ) (hn : 0 < n) (hok : (mkCell n j).ok = true) (Q : List ℚ)
    (hQ : ∀ t, 0 ≤ peval Q t) (hlen : Q.length ≤ 13) (lam : ℚ) (hlam : 0 < lam) :
    ∫ t in ((mkCell n j).a : ℝ)..((mkCell n j).b : ℝ), Real.sqrt (peval Q t) * wfun t ≤
      ((((Q.zipIdx.map fun qi => qi.1 * (if 0 ≤ qi.1 then (mkCell n j).muHi.getD qi.2 0
        else (mkCell n j).muLo.getD qi.2 0)).sum) / (2 * lam) +
        lam * (mkCell n j).muHi.getD 0 0 / 2 : ℚ) : ℝ) := by
  set c := mkCell n j with hc
  -- the quadratic U
  set Uf : ℝ → ℝ := fun t => (c.w0 : ℝ) + c.w1 * (t - c.m) + c.c2 * (t - c.m) ^ 2 with hUf
  have hUc : Continuous Uf := by rw [hUf]; fun_prop
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : (c.a : ℝ) ≤ c.b := by
    rw [hc, mkCell_a, mkCell_b]; push_cast
    have : (0 : ℝ) ≤ 2 / n := by positivity
    linarith
  -- w ≤ U on the cell, from the `ok` flag
  have hwU : ∀ t ∈ Set.Icc (c.a : ℝ) c.b, wfun t ≤ Uf t := by
    intro t ht
    have ha : (c.a : ℝ) = -1 + 2 * (j : ℝ) / n := by rw [hc, mkCell_a]; push_cast; ring
    have hb : (c.b : ℝ) = -1 + 2 * (j : ℝ) / n + 2 / n := by rw [hc, mkCell_b]; push_cast; ring
    have hm : (c.m : ℝ) = -1 + 2 * (j : ℝ) / n + 1 / n := by
      have : c.m = ((-1 + 2 * j / n) + (-1 + 2 * j / n + 2 / n)) / 2 := by rw [hc]; rfl
      rw [this]; push_cast; ring
    have htm : |t - c.m| ≤ ((1 / n : ℚ) : ℝ) := by
      obtain ⟨h1, h2⟩ := ht
      rw [ha] at h1; rw [hb] at h2; rw [hm]; push_cast
      have e : (2 : ℝ) / n = 2 * (1 / n) := by ring
      rw [abs_le]; constructor <;> linarith
    have hok' := hok
    simp only [hc, mkCell, Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨⟨hG0, hG1⟩, _⟩, hK⟩ := hok'
    exact w_le_U _ _ _ _ _ _ _ _ rfl rfl rfl hG0 hG1 hK t htm
  -- exact moments
  have hmom : ∀ i, ∫ t in (c.a : ℝ)..c.b, t ^ i * Uf t =
      ((c.w0 - c.w1 * c.m + c.c2 * c.m ^ 2) * powInt c.a c.b i +
        (c.w1 - 2 * c.c2 * c.m) * powInt c.a c.b (i + 1) + c.c2 * powInt c.a c.b (i + 2) : ℚ) := by
    intro i
    rw [← moment_formula]
    congr 1; funext t; rw [hUf]; push_cast; ring
  have hhi : ∀ i < 13, ∫ t in (c.a : ℝ)..c.b, t ^ i * Uf t ≤ (c.muHi.getD i 0 : ℝ) := by
    intro i hi
    rw [hmom]
    have : c.muHi.getD i 0 = roundUp ((c.w0 - c.w1 * c.m + c.c2 * c.m ^ 2) * powInt c.a c.b i +
        (c.w1 - 2 * c.c2 * c.m) * powInt c.a c.b (i + 1) + c.c2 * powInt c.a c.b (i + 2)) 96 := by
      simp [hc, mkCell, Array.getD, hi]
    rw [this]; exact_mod_cast roundUp_ge _ _
  have hlo : ∀ i < 13, (c.muLo.getD i 0 : ℝ) ≤ ∫ t in (c.a : ℝ)..c.b, t ^ i * Uf t := by
    intro i hi
    rw [hmom]
    have : c.muLo.getD i 0 = roundDn ((c.w0 - c.w1 * c.m + c.c2 * c.m ^ 2) * powInt c.a c.b i +
        (c.w1 - 2 * c.c2 * c.m) * powInt c.a c.b (i + 1) + c.c2 * powInt c.a c.b (i + 2)) 96 := by
      simp [hc, mkCell, Array.getD, hi]
    rw [this]; exact_mod_cast roundDn_le _ _
  have key := cell_bound c.a c.b hab Uf hUc hwU Q hQ (fun i => c.muHi.getD i 0)
    (fun i => c.muLo.getD i 0) (fun i hi => hhi i (by omega)) (fun i hi => hlo i (by omega))
    (hhi 0 (by norm_num)) lam hlam
  exact key

lemma foldl_add_sum {α : Type*} (f : α → ℚ) :
    ∀ (l : List α) (s : ℚ), l.foldl (fun s c => s + f c) s = s + (l.map f).sum
  | [], s => by simp
  | x :: l, s => by simp [List.foldl, foldl_add_sum f l]; ring

lemma sum_range_map (g : ℕ → ℚ) : ∀ n, ((List.range n).map g).sum = ∑ k ∈ Finset.range n, g k
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_map g n,
      Finset.sum_range_succ]; simp

lemma mkCells_foldl (n : ℕ) (Q : List ℚ) :
    (mkCells n).toList.foldl (fun s c => s + cellBound Q c) 0 = ∑ k ∈ Finset.range n, cellBound Q (mkCell n k) := by
  unfold mkCells
  simp only [List.map_toArray, List.toList_toArray]
  rw [foldl_add_sum, List.map_map, zero_add]
  exact sum_range_map _ n

lemma cellsOK_get (n : ℕ) (h : cellsOK (mkCells n) = true) (k : ℕ) (hk : k < n) :
    (mkCell n k).ok = true := by
  unfold cellsOK mkCells at h
  rw [List.all_eq_true] at h
  exact h _ (by simp only [List.map_toArray, List.toList_toArray, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩)

/-- The integral over `[-1,1]` is bounded by the sum of the cell bounds. -/
lemma integral_le_cells (n : ℕ) (hn : 0 < n) (hok : cellsOK (mkCells n) = true) (Q : List ℚ)
    (hQ : ∀ t, 0 ≤ peval Q t) (hlen : Q.length ≤ 13) :
    ∫ t in (-1 : ℝ)..1, Real.sqrt (peval Q t) * wfun t ≤
      (((mkCells n).toList.foldl (fun s c => s + cellBound Q c) 0 : ℚ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set pt : ℕ → ℝ := fun k => -1 + 2 * k / n with hpt
  have hcont : Continuous fun t => Real.sqrt (peval Q t) * wfun t :=
    (Real.continuous_sqrt.comp (continuous_peval Q)).mul continuous_wfun
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t => Real.sqrt (peval Q t) * wfun t) (a := pt) (n := n)
    (fun k _ => hcont.intervalIntegrable _ _)
  have h0 : pt 0 = -1 := by simp [hpt]
  have hN : pt n = 1 := by simp only [hpt]; field_simp; ring
  rw [h0, hN] at hsum
  rw [← hsum, mkCells_foldl]; push_cast
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have := mkCell_bound n k hn (cellsOK_get n hok k hk') Q hQ hlen
  have ha : ((mkCell n k).a : ℝ) = pt k := by rw [mkCell_a]; push_cast; rfl
  have hb : ((mkCell n k).b : ℝ) = pt (k + 1) := by
    rw [mkCell_b]; push_cast; simp only [hpt]; push_cast; ring
  rw [ha, hb] at this
  exact this

end Harris
