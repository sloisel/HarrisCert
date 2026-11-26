module

public import HarrisCert.Data.Skel
public import HarrisCert.Cover0
public import HarrisCert.Cover1
public import HarrisCert.Cover2
public import HarrisCert.Cover3

/-!
# The global step (Proposition 11 of `harris_sharp.tex`), checked by the kernel
-/

@[expose] public section

namespace Harris

theorem cr_0_1313 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 1313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 656 then cr_0_656 k h1 h else cr_656_1313 k (by omega) h2
theorem cr_1313_2627 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1970 then cr_1313_1970 k h1 h else cr_1970_2627 k (by omega) h2
theorem cr_0_2627 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1313 then cr_0_1313 k h1 h else cr_1313_2627 k (by omega) h2

theorem all_cov (k : ℕ) : Covered (boxes k).1 (boxes k).2 := by
  by_cases hk : k < 2627
  · exact cr_0_2627 k (Nat.zero_le _) hk
  · have : boxes k = (fun _ => 1, fun _ => 0) := by
      unfold boxes; rw [List.getD_eq_default]; rw [boxList_length]; omega
    rw [this]; exact covered_empty _ _ 0 (by norm_num)

/-- **The global step.** -/
theorem global_step (x : Fin 7 → ℝ) (h : Hyps x) : Goal x :=
  Skel.check_sound boxes all_cov skel rootLo rootHi skel_ok x h.box h

end Harris
