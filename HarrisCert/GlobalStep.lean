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

theorem pr_0_1 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 1) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 0 := by omega
  exact Skel.check_sound boxes all_cov skp0 _ _ skp0_ok
theorem pr_1_2 (i : ℕ) (h1 : 1 ≤ i) (h2 : i < 2) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 1 := by omega
  exact Skel.check_sound boxes all_cov skp1 _ _ skp1_ok
theorem pr_0_2 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 2) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 1 then pr_0_1 i h1 h else pr_1_2 i (by omega) h2
theorem pr_2_3 (i : ℕ) (h1 : 2 ≤ i) (h2 : i < 3) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 2 := by omega
  exact Skel.check_sound boxes all_cov skp2 _ _ skp2_ok
theorem pr_3_4 (i : ℕ) (h1 : 3 ≤ i) (h2 : i < 4) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 3 := by omega
  exact Skel.check_sound boxes all_cov skp3 _ _ skp3_ok
theorem pr_2_4 (i : ℕ) (h1 : 2 ≤ i) (h2 : i < 4) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 3 then pr_2_3 i h1 h else pr_3_4 i (by omega) h2
theorem pr_0_4 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 4) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 2 then pr_0_2 i h1 h else pr_2_4 i (by omega) h2
theorem pr_4_5 (i : ℕ) (h1 : 4 ≤ i) (h2 : i < 5) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 4 := by omega
  exact Skel.check_sound boxes all_cov skp4 _ _ skp4_ok
theorem pr_5_6 (i : ℕ) (h1 : 5 ≤ i) (h2 : i < 6) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 5 := by omega
  exact Skel.check_sound boxes all_cov skp5 _ _ skp5_ok
theorem pr_4_6 (i : ℕ) (h1 : 4 ≤ i) (h2 : i < 6) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 5 then pr_4_5 i h1 h else pr_5_6 i (by omega) h2
theorem pr_6_7 (i : ℕ) (h1 : 6 ≤ i) (h2 : i < 7) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 6 := by omega
  exact Skel.check_sound boxes all_cov skp6 _ _ skp6_ok
theorem pr_7_8 (i : ℕ) (h1 : 7 ≤ i) (h2 : i < 8) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 7 := by omega
  exact Skel.check_sound boxes all_cov skp7 _ _ skp7_ok
theorem pr_8_9 (i : ℕ) (h1 : 8 ≤ i) (h2 : i < 9) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 8 := by omega
  exact Skel.check_sound boxes all_cov skp8 _ _ skp8_ok
theorem pr_7_9 (i : ℕ) (h1 : 7 ≤ i) (h2 : i < 9) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 8 then pr_7_8 i h1 h else pr_8_9 i (by omega) h2
theorem pr_6_9 (i : ℕ) (h1 : 6 ≤ i) (h2 : i < 9) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 7 then pr_6_7 i h1 h else pr_7_9 i (by omega) h2
theorem pr_4_9 (i : ℕ) (h1 : 4 ≤ i) (h2 : i < 9) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 6 then pr_4_6 i h1 h else pr_6_9 i (by omega) h2
theorem pr_0_9 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 9) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 4 then pr_0_4 i h1 h else pr_4_9 i (by omega) h2
theorem pr_9_10 (i : ℕ) (h1 : 9 ≤ i) (h2 : i < 10) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 9 := by omega
  exact Skel.check_sound boxes all_cov skp9 _ _ skp9_ok
theorem pr_10_11 (i : ℕ) (h1 : 10 ≤ i) (h2 : i < 11) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 10 := by omega
  exact Skel.check_sound boxes all_cov skp10 _ _ skp10_ok
theorem pr_9_11 (i : ℕ) (h1 : 9 ≤ i) (h2 : i < 11) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 10 then pr_9_10 i h1 h else pr_10_11 i (by omega) h2
theorem pr_11_12 (i : ℕ) (h1 : 11 ≤ i) (h2 : i < 12) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 11 := by omega
  exact Skel.check_sound boxes all_cov skp11 _ _ skp11_ok
theorem pr_12_13 (i : ℕ) (h1 : 12 ≤ i) (h2 : i < 13) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 12 := by omega
  exact Skel.check_sound boxes all_cov skp12 _ _ skp12_ok
theorem pr_13_14 (i : ℕ) (h1 : 13 ≤ i) (h2 : i < 14) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 13 := by omega
  exact Skel.check_sound boxes all_cov skp13 _ _ skp13_ok
theorem pr_12_14 (i : ℕ) (h1 : 12 ≤ i) (h2 : i < 14) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 13 then pr_12_13 i h1 h else pr_13_14 i (by omega) h2
theorem pr_11_14 (i : ℕ) (h1 : 11 ≤ i) (h2 : i < 14) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 12 then pr_11_12 i h1 h else pr_12_14 i (by omega) h2
theorem pr_9_14 (i : ℕ) (h1 : 9 ≤ i) (h2 : i < 14) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 11 then pr_9_11 i h1 h else pr_11_14 i (by omega) h2
theorem pr_14_15 (i : ℕ) (h1 : 14 ≤ i) (h2 : i < 15) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 14 := by omega
  exact Skel.check_sound boxes all_cov skp14 _ _ skp14_ok
theorem pr_15_16 (i : ℕ) (h1 : 15 ≤ i) (h2 : i < 16) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 15 := by omega
  exact Skel.check_sound boxes all_cov skp15 _ _ skp15_ok
theorem pr_14_16 (i : ℕ) (h1 : 14 ≤ i) (h2 : i < 16) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 15 then pr_14_15 i h1 h else pr_15_16 i (by omega) h2
theorem pr_16_17 (i : ℕ) (h1 : 16 ≤ i) (h2 : i < 17) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 16 := by omega
  exact Skel.check_sound boxes all_cov skp16 _ _ skp16_ok
theorem pr_17_18 (i : ℕ) (h1 : 17 ≤ i) (h2 : i < 18) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 17 := by omega
  exact Skel.check_sound boxes all_cov skp17 _ _ skp17_ok
theorem pr_18_19 (i : ℕ) (h1 : 18 ≤ i) (h2 : i < 19) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 18 := by omega
  exact Skel.check_sound boxes all_cov skp18 _ _ skp18_ok
theorem pr_17_19 (i : ℕ) (h1 : 17 ≤ i) (h2 : i < 19) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 18 then pr_17_18 i h1 h else pr_18_19 i (by omega) h2
theorem pr_16_19 (i : ℕ) (h1 : 16 ≤ i) (h2 : i < 19) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 17 then pr_16_17 i h1 h else pr_17_19 i (by omega) h2
theorem pr_14_19 (i : ℕ) (h1 : 14 ≤ i) (h2 : i < 19) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 16 then pr_14_16 i h1 h else pr_16_19 i (by omega) h2
theorem pr_9_19 (i : ℕ) (h1 : 9 ≤ i) (h2 : i < 19) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 14 then pr_9_14 i h1 h else pr_14_19 i (by omega) h2
theorem pr_0_19 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 19) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 9 then pr_0_9 i h1 h else pr_9_19 i (by omega) h2
theorem pr_19_20 (i : ℕ) (h1 : 19 ≤ i) (h2 : i < 20) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 19 := by omega
  exact Skel.check_sound boxes all_cov skp19 _ _ skp19_ok
theorem pr_20_21 (i : ℕ) (h1 : 20 ≤ i) (h2 : i < 21) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 20 := by omega
  exact Skel.check_sound boxes all_cov skp20 _ _ skp20_ok
theorem pr_19_21 (i : ℕ) (h1 : 19 ≤ i) (h2 : i < 21) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 20 then pr_19_20 i h1 h else pr_20_21 i (by omega) h2
theorem pr_21_22 (i : ℕ) (h1 : 21 ≤ i) (h2 : i < 22) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 21 := by omega
  exact Skel.check_sound boxes all_cov skp21 _ _ skp21_ok
theorem pr_22_23 (i : ℕ) (h1 : 22 ≤ i) (h2 : i < 23) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 22 := by omega
  exact Skel.check_sound boxes all_cov skp22 _ _ skp22_ok
theorem pr_23_24 (i : ℕ) (h1 : 23 ≤ i) (h2 : i < 24) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 23 := by omega
  exact Skel.check_sound boxes all_cov skp23 _ _ skp23_ok
theorem pr_22_24 (i : ℕ) (h1 : 22 ≤ i) (h2 : i < 24) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 23 then pr_22_23 i h1 h else pr_23_24 i (by omega) h2
theorem pr_21_24 (i : ℕ) (h1 : 21 ≤ i) (h2 : i < 24) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 22 then pr_21_22 i h1 h else pr_22_24 i (by omega) h2
theorem pr_19_24 (i : ℕ) (h1 : 19 ≤ i) (h2 : i < 24) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 21 then pr_19_21 i h1 h else pr_21_24 i (by omega) h2
theorem pr_24_25 (i : ℕ) (h1 : 24 ≤ i) (h2 : i < 25) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 24 := by omega
  exact Skel.check_sound boxes all_cov skp24 _ _ skp24_ok
theorem pr_25_26 (i : ℕ) (h1 : 25 ≤ i) (h2 : i < 26) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 25 := by omega
  exact Skel.check_sound boxes all_cov skp25 _ _ skp25_ok
theorem pr_24_26 (i : ℕ) (h1 : 24 ≤ i) (h2 : i < 26) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 25 then pr_24_25 i h1 h else pr_25_26 i (by omega) h2
theorem pr_26_27 (i : ℕ) (h1 : 26 ≤ i) (h2 : i < 27) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 26 := by omega
  exact Skel.check_sound boxes all_cov skp26 _ _ skp26_ok
theorem pr_27_28 (i : ℕ) (h1 : 27 ≤ i) (h2 : i < 28) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 27 := by omega
  exact Skel.check_sound boxes all_cov skp27 _ _ skp27_ok
theorem pr_28_29 (i : ℕ) (h1 : 28 ≤ i) (h2 : i < 29) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 28 := by omega
  exact Skel.check_sound boxes all_cov skp28 _ _ skp28_ok
theorem pr_27_29 (i : ℕ) (h1 : 27 ≤ i) (h2 : i < 29) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 28 then pr_27_28 i h1 h else pr_28_29 i (by omega) h2
theorem pr_26_29 (i : ℕ) (h1 : 26 ≤ i) (h2 : i < 29) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 27 then pr_26_27 i h1 h else pr_27_29 i (by omega) h2
theorem pr_24_29 (i : ℕ) (h1 : 24 ≤ i) (h2 : i < 29) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 26 then pr_24_26 i h1 h else pr_26_29 i (by omega) h2
theorem pr_19_29 (i : ℕ) (h1 : 19 ≤ i) (h2 : i < 29) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 24 then pr_19_24 i h1 h else pr_24_29 i (by omega) h2
theorem pr_29_30 (i : ℕ) (h1 : 29 ≤ i) (h2 : i < 30) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 29 := by omega
  exact Skel.check_sound boxes all_cov skp29 _ _ skp29_ok
theorem pr_30_31 (i : ℕ) (h1 : 30 ≤ i) (h2 : i < 31) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 30 := by omega
  exact Skel.check_sound boxes all_cov skp30 _ _ skp30_ok
theorem pr_29_31 (i : ℕ) (h1 : 29 ≤ i) (h2 : i < 31) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 30 then pr_29_30 i h1 h else pr_30_31 i (by omega) h2
theorem pr_31_32 (i : ℕ) (h1 : 31 ≤ i) (h2 : i < 32) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 31 := by omega
  exact Skel.check_sound boxes all_cov skp31 _ _ skp31_ok
theorem pr_32_33 (i : ℕ) (h1 : 32 ≤ i) (h2 : i < 33) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 32 := by omega
  exact Skel.check_sound boxes all_cov skp32 _ _ skp32_ok
theorem pr_33_34 (i : ℕ) (h1 : 33 ≤ i) (h2 : i < 34) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 33 := by omega
  exact Skel.check_sound boxes all_cov skp33 _ _ skp33_ok
theorem pr_32_34 (i : ℕ) (h1 : 32 ≤ i) (h2 : i < 34) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 33 then pr_32_33 i h1 h else pr_33_34 i (by omega) h2
theorem pr_31_34 (i : ℕ) (h1 : 31 ≤ i) (h2 : i < 34) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 32 then pr_31_32 i h1 h else pr_32_34 i (by omega) h2
theorem pr_29_34 (i : ℕ) (h1 : 29 ≤ i) (h2 : i < 34) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 31 then pr_29_31 i h1 h else pr_31_34 i (by omega) h2
theorem pr_34_35 (i : ℕ) (h1 : 34 ≤ i) (h2 : i < 35) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 34 := by omega
  exact Skel.check_sound boxes all_cov skp34 _ _ skp34_ok
theorem pr_35_36 (i : ℕ) (h1 : 35 ≤ i) (h2 : i < 36) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 35 := by omega
  exact Skel.check_sound boxes all_cov skp35 _ _ skp35_ok
theorem pr_34_36 (i : ℕ) (h1 : 34 ≤ i) (h2 : i < 36) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 35 then pr_34_35 i h1 h else pr_35_36 i (by omega) h2
theorem pr_36_37 (i : ℕ) (h1 : 36 ≤ i) (h2 : i < 37) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 36 := by omega
  exact Skel.check_sound boxes all_cov skp36 _ _ skp36_ok
theorem pr_37_38 (i : ℕ) (h1 : 37 ≤ i) (h2 : i < 38) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 37 := by omega
  exact Skel.check_sound boxes all_cov skp37 _ _ skp37_ok
theorem pr_38_39 (i : ℕ) (h1 : 38 ≤ i) (h2 : i < 39) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 38 := by omega
  exact Skel.check_sound boxes all_cov skp38 _ _ skp38_ok
theorem pr_37_39 (i : ℕ) (h1 : 37 ≤ i) (h2 : i < 39) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 38 then pr_37_38 i h1 h else pr_38_39 i (by omega) h2
theorem pr_36_39 (i : ℕ) (h1 : 36 ≤ i) (h2 : i < 39) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 37 then pr_36_37 i h1 h else pr_37_39 i (by omega) h2
theorem pr_34_39 (i : ℕ) (h1 : 34 ≤ i) (h2 : i < 39) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 36 then pr_34_36 i h1 h else pr_36_39 i (by omega) h2
theorem pr_29_39 (i : ℕ) (h1 : 29 ≤ i) (h2 : i < 39) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 34 then pr_29_34 i h1 h else pr_34_39 i (by omega) h2
theorem pr_19_39 (i : ℕ) (h1 : 19 ≤ i) (h2 : i < 39) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 29 then pr_19_29 i h1 h else pr_29_39 i (by omega) h2
theorem pr_0_39 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 39) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 19 then pr_0_19 i h1 h else pr_19_39 i (by omega) h2
theorem pr_39_40 (i : ℕ) (h1 : 39 ≤ i) (h2 : i < 40) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 39 := by omega
  exact Skel.check_sound boxes all_cov skp39 _ _ skp39_ok
theorem pr_40_41 (i : ℕ) (h1 : 40 ≤ i) (h2 : i < 41) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 40 := by omega
  exact Skel.check_sound boxes all_cov skp40 _ _ skp40_ok
theorem pr_39_41 (i : ℕ) (h1 : 39 ≤ i) (h2 : i < 41) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 40 then pr_39_40 i h1 h else pr_40_41 i (by omega) h2
theorem pr_41_42 (i : ℕ) (h1 : 41 ≤ i) (h2 : i < 42) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 41 := by omega
  exact Skel.check_sound boxes all_cov skp41 _ _ skp41_ok
theorem pr_42_43 (i : ℕ) (h1 : 42 ≤ i) (h2 : i < 43) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 42 := by omega
  exact Skel.check_sound boxes all_cov skp42 _ _ skp42_ok
theorem pr_41_43 (i : ℕ) (h1 : 41 ≤ i) (h2 : i < 43) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 42 then pr_41_42 i h1 h else pr_42_43 i (by omega) h2
theorem pr_39_43 (i : ℕ) (h1 : 39 ≤ i) (h2 : i < 43) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 41 then pr_39_41 i h1 h else pr_41_43 i (by omega) h2
theorem pr_43_44 (i : ℕ) (h1 : 43 ≤ i) (h2 : i < 44) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 43 := by omega
  exact Skel.check_sound boxes all_cov skp43 _ _ skp43_ok
theorem pr_44_45 (i : ℕ) (h1 : 44 ≤ i) (h2 : i < 45) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 44 := by omega
  exact Skel.check_sound boxes all_cov skp44 _ _ skp44_ok
theorem pr_43_45 (i : ℕ) (h1 : 43 ≤ i) (h2 : i < 45) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 44 then pr_43_44 i h1 h else pr_44_45 i (by omega) h2
theorem pr_45_46 (i : ℕ) (h1 : 45 ≤ i) (h2 : i < 46) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 45 := by omega
  exact Skel.check_sound boxes all_cov skp45 _ _ skp45_ok
theorem pr_46_47 (i : ℕ) (h1 : 46 ≤ i) (h2 : i < 47) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 46 := by omega
  exact Skel.check_sound boxes all_cov skp46 _ _ skp46_ok
theorem pr_47_48 (i : ℕ) (h1 : 47 ≤ i) (h2 : i < 48) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 47 := by omega
  exact Skel.check_sound boxes all_cov skp47 _ _ skp47_ok
theorem pr_46_48 (i : ℕ) (h1 : 46 ≤ i) (h2 : i < 48) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 47 then pr_46_47 i h1 h else pr_47_48 i (by omega) h2
theorem pr_45_48 (i : ℕ) (h1 : 45 ≤ i) (h2 : i < 48) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 46 then pr_45_46 i h1 h else pr_46_48 i (by omega) h2
theorem pr_43_48 (i : ℕ) (h1 : 43 ≤ i) (h2 : i < 48) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 45 then pr_43_45 i h1 h else pr_45_48 i (by omega) h2
theorem pr_39_48 (i : ℕ) (h1 : 39 ≤ i) (h2 : i < 48) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 43 then pr_39_43 i h1 h else pr_43_48 i (by omega) h2
theorem pr_48_49 (i : ℕ) (h1 : 48 ≤ i) (h2 : i < 49) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 48 := by omega
  exact Skel.check_sound boxes all_cov skp48 _ _ skp48_ok
theorem pr_49_50 (i : ℕ) (h1 : 49 ≤ i) (h2 : i < 50) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 49 := by omega
  exact Skel.check_sound boxes all_cov skp49 _ _ skp49_ok
theorem pr_48_50 (i : ℕ) (h1 : 48 ≤ i) (h2 : i < 50) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 49 then pr_48_49 i h1 h else pr_49_50 i (by omega) h2
theorem pr_50_51 (i : ℕ) (h1 : 50 ≤ i) (h2 : i < 51) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 50 := by omega
  exact Skel.check_sound boxes all_cov skp50 _ _ skp50_ok
theorem pr_51_52 (i : ℕ) (h1 : 51 ≤ i) (h2 : i < 52) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 51 := by omega
  exact Skel.check_sound boxes all_cov skp51 _ _ skp51_ok
theorem pr_52_53 (i : ℕ) (h1 : 52 ≤ i) (h2 : i < 53) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 52 := by omega
  exact Skel.check_sound boxes all_cov skp52 _ _ skp52_ok
theorem pr_51_53 (i : ℕ) (h1 : 51 ≤ i) (h2 : i < 53) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 52 then pr_51_52 i h1 h else pr_52_53 i (by omega) h2
theorem pr_50_53 (i : ℕ) (h1 : 50 ≤ i) (h2 : i < 53) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 51 then pr_50_51 i h1 h else pr_51_53 i (by omega) h2
theorem pr_48_53 (i : ℕ) (h1 : 48 ≤ i) (h2 : i < 53) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 50 then pr_48_50 i h1 h else pr_50_53 i (by omega) h2
theorem pr_53_54 (i : ℕ) (h1 : 53 ≤ i) (h2 : i < 54) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 53 := by omega
  exact Skel.check_sound boxes all_cov skp53 _ _ skp53_ok
theorem pr_54_55 (i : ℕ) (h1 : 54 ≤ i) (h2 : i < 55) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 54 := by omega
  exact Skel.check_sound boxes all_cov skp54 _ _ skp54_ok
theorem pr_53_55 (i : ℕ) (h1 : 53 ≤ i) (h2 : i < 55) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 54 then pr_53_54 i h1 h else pr_54_55 i (by omega) h2
theorem pr_55_56 (i : ℕ) (h1 : 55 ≤ i) (h2 : i < 56) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 55 := by omega
  exact Skel.check_sound boxes all_cov skp55 _ _ skp55_ok
theorem pr_56_57 (i : ℕ) (h1 : 56 ≤ i) (h2 : i < 57) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 56 := by omega
  exact Skel.check_sound boxes all_cov skp56 _ _ skp56_ok
theorem pr_57_58 (i : ℕ) (h1 : 57 ≤ i) (h2 : i < 58) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 57 := by omega
  exact Skel.check_sound boxes all_cov skp57 _ _ skp57_ok
theorem pr_56_58 (i : ℕ) (h1 : 56 ≤ i) (h2 : i < 58) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 57 then pr_56_57 i h1 h else pr_57_58 i (by omega) h2
theorem pr_55_58 (i : ℕ) (h1 : 55 ≤ i) (h2 : i < 58) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 56 then pr_55_56 i h1 h else pr_56_58 i (by omega) h2
theorem pr_53_58 (i : ℕ) (h1 : 53 ≤ i) (h2 : i < 58) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 55 then pr_53_55 i h1 h else pr_55_58 i (by omega) h2
theorem pr_48_58 (i : ℕ) (h1 : 48 ≤ i) (h2 : i < 58) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 53 then pr_48_53 i h1 h else pr_53_58 i (by omega) h2
theorem pr_39_58 (i : ℕ) (h1 : 39 ≤ i) (h2 : i < 58) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 48 then pr_39_48 i h1 h else pr_48_58 i (by omega) h2
theorem pr_58_59 (i : ℕ) (h1 : 58 ≤ i) (h2 : i < 59) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 58 := by omega
  exact Skel.check_sound boxes all_cov skp58 _ _ skp58_ok
theorem pr_59_60 (i : ℕ) (h1 : 59 ≤ i) (h2 : i < 60) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 59 := by omega
  exact Skel.check_sound boxes all_cov skp59 _ _ skp59_ok
theorem pr_58_60 (i : ℕ) (h1 : 58 ≤ i) (h2 : i < 60) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 59 then pr_58_59 i h1 h else pr_59_60 i (by omega) h2
theorem pr_60_61 (i : ℕ) (h1 : 60 ≤ i) (h2 : i < 61) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 60 := by omega
  exact Skel.check_sound boxes all_cov skp60 _ _ skp60_ok
theorem pr_61_62 (i : ℕ) (h1 : 61 ≤ i) (h2 : i < 62) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 61 := by omega
  exact Skel.check_sound boxes all_cov skp61 _ _ skp61_ok
theorem pr_62_63 (i : ℕ) (h1 : 62 ≤ i) (h2 : i < 63) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 62 := by omega
  exact Skel.check_sound boxes all_cov skp62 _ _ skp62_ok
theorem pr_61_63 (i : ℕ) (h1 : 61 ≤ i) (h2 : i < 63) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 62 then pr_61_62 i h1 h else pr_62_63 i (by omega) h2
theorem pr_60_63 (i : ℕ) (h1 : 60 ≤ i) (h2 : i < 63) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 61 then pr_60_61 i h1 h else pr_61_63 i (by omega) h2
theorem pr_58_63 (i : ℕ) (h1 : 58 ≤ i) (h2 : i < 63) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 60 then pr_58_60 i h1 h else pr_60_63 i (by omega) h2
theorem pr_63_64 (i : ℕ) (h1 : 63 ≤ i) (h2 : i < 64) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 63 := by omega
  exact Skel.check_sound boxes all_cov skp63 _ _ skp63_ok
theorem pr_64_65 (i : ℕ) (h1 : 64 ≤ i) (h2 : i < 65) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 64 := by omega
  exact Skel.check_sound boxes all_cov skp64 _ _ skp64_ok
theorem pr_63_65 (i : ℕ) (h1 : 63 ≤ i) (h2 : i < 65) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 64 then pr_63_64 i h1 h else pr_64_65 i (by omega) h2
theorem pr_65_66 (i : ℕ) (h1 : 65 ≤ i) (h2 : i < 66) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 65 := by omega
  exact Skel.check_sound boxes all_cov skp65 _ _ skp65_ok
theorem pr_66_67 (i : ℕ) (h1 : 66 ≤ i) (h2 : i < 67) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 66 := by omega
  exact Skel.check_sound boxes all_cov skp66 _ _ skp66_ok
theorem pr_67_68 (i : ℕ) (h1 : 67 ≤ i) (h2 : i < 68) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 67 := by omega
  exact Skel.check_sound boxes all_cov skp67 _ _ skp67_ok
theorem pr_66_68 (i : ℕ) (h1 : 66 ≤ i) (h2 : i < 68) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 67 then pr_66_67 i h1 h else pr_67_68 i (by omega) h2
theorem pr_65_68 (i : ℕ) (h1 : 65 ≤ i) (h2 : i < 68) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 66 then pr_65_66 i h1 h else pr_66_68 i (by omega) h2
theorem pr_63_68 (i : ℕ) (h1 : 63 ≤ i) (h2 : i < 68) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 65 then pr_63_65 i h1 h else pr_65_68 i (by omega) h2
theorem pr_58_68 (i : ℕ) (h1 : 58 ≤ i) (h2 : i < 68) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 63 then pr_58_63 i h1 h else pr_63_68 i (by omega) h2
theorem pr_68_69 (i : ℕ) (h1 : 68 ≤ i) (h2 : i < 69) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 68 := by omega
  exact Skel.check_sound boxes all_cov skp68 _ _ skp68_ok
theorem pr_69_70 (i : ℕ) (h1 : 69 ≤ i) (h2 : i < 70) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 69 := by omega
  exact Skel.check_sound boxes all_cov skp69 _ _ skp69_ok
theorem pr_68_70 (i : ℕ) (h1 : 68 ≤ i) (h2 : i < 70) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 69 then pr_68_69 i h1 h else pr_69_70 i (by omega) h2
theorem pr_70_71 (i : ℕ) (h1 : 70 ≤ i) (h2 : i < 71) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 70 := by omega
  exact Skel.check_sound boxes all_cov skp70 _ _ skp70_ok
theorem pr_71_72 (i : ℕ) (h1 : 71 ≤ i) (h2 : i < 72) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 71 := by omega
  exact Skel.check_sound boxes all_cov skp71 _ _ skp71_ok
theorem pr_72_73 (i : ℕ) (h1 : 72 ≤ i) (h2 : i < 73) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 72 := by omega
  exact Skel.check_sound boxes all_cov skp72 _ _ skp72_ok
theorem pr_71_73 (i : ℕ) (h1 : 71 ≤ i) (h2 : i < 73) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 72 then pr_71_72 i h1 h else pr_72_73 i (by omega) h2
theorem pr_70_73 (i : ℕ) (h1 : 70 ≤ i) (h2 : i < 73) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 71 then pr_70_71 i h1 h else pr_71_73 i (by omega) h2
theorem pr_68_73 (i : ℕ) (h1 : 68 ≤ i) (h2 : i < 73) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 70 then pr_68_70 i h1 h else pr_70_73 i (by omega) h2
theorem pr_73_74 (i : ℕ) (h1 : 73 ≤ i) (h2 : i < 74) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 73 := by omega
  exact Skel.check_sound boxes all_cov skp73 _ _ skp73_ok
theorem pr_74_75 (i : ℕ) (h1 : 74 ≤ i) (h2 : i < 75) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 74 := by omega
  exact Skel.check_sound boxes all_cov skp74 _ _ skp74_ok
theorem pr_73_75 (i : ℕ) (h1 : 73 ≤ i) (h2 : i < 75) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 74 then pr_73_74 i h1 h else pr_74_75 i (by omega) h2
theorem pr_75_76 (i : ℕ) (h1 : 75 ≤ i) (h2 : i < 76) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 75 := by omega
  exact Skel.check_sound boxes all_cov skp75 _ _ skp75_ok
theorem pr_76_77 (i : ℕ) (h1 : 76 ≤ i) (h2 : i < 77) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 76 := by omega
  exact Skel.check_sound boxes all_cov skp76 _ _ skp76_ok
theorem pr_77_78 (i : ℕ) (h1 : 77 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 77 := by omega
  exact Skel.check_sound boxes all_cov skp77 _ _ skp77_ok
theorem pr_76_78 (i : ℕ) (h1 : 76 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 77 then pr_76_77 i h1 h else pr_77_78 i (by omega) h2
theorem pr_75_78 (i : ℕ) (h1 : 75 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 76 then pr_75_76 i h1 h else pr_76_78 i (by omega) h2
theorem pr_73_78 (i : ℕ) (h1 : 73 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 75 then pr_73_75 i h1 h else pr_75_78 i (by omega) h2
theorem pr_68_78 (i : ℕ) (h1 : 68 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 73 then pr_68_73 i h1 h else pr_73_78 i (by omega) h2
theorem pr_58_78 (i : ℕ) (h1 : 58 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 68 then pr_58_68 i h1 h else pr_68_78 i (by omega) h2
theorem pr_39_78 (i : ℕ) (h1 : 39 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 58 then pr_39_58 i h1 h else pr_58_78 i (by omega) h2
theorem pr_0_78 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 78) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 39 then pr_0_39 i h1 h else pr_39_78 i (by omega) h2
theorem pr_78_79 (i : ℕ) (h1 : 78 ≤ i) (h2 : i < 79) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 78 := by omega
  exact Skel.check_sound boxes all_cov skp78 _ _ skp78_ok
theorem pr_79_80 (i : ℕ) (h1 : 79 ≤ i) (h2 : i < 80) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 79 := by omega
  exact Skel.check_sound boxes all_cov skp79 _ _ skp79_ok
theorem pr_78_80 (i : ℕ) (h1 : 78 ≤ i) (h2 : i < 80) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 79 then pr_78_79 i h1 h else pr_79_80 i (by omega) h2
theorem pr_80_81 (i : ℕ) (h1 : 80 ≤ i) (h2 : i < 81) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 80 := by omega
  exact Skel.check_sound boxes all_cov skp80 _ _ skp80_ok
theorem pr_81_82 (i : ℕ) (h1 : 81 ≤ i) (h2 : i < 82) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 81 := by omega
  exact Skel.check_sound boxes all_cov skp81 _ _ skp81_ok
theorem pr_80_82 (i : ℕ) (h1 : 80 ≤ i) (h2 : i < 82) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 81 then pr_80_81 i h1 h else pr_81_82 i (by omega) h2
theorem pr_78_82 (i : ℕ) (h1 : 78 ≤ i) (h2 : i < 82) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 80 then pr_78_80 i h1 h else pr_80_82 i (by omega) h2
theorem pr_82_83 (i : ℕ) (h1 : 82 ≤ i) (h2 : i < 83) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 82 := by omega
  exact Skel.check_sound boxes all_cov skp82 _ _ skp82_ok
theorem pr_83_84 (i : ℕ) (h1 : 83 ≤ i) (h2 : i < 84) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 83 := by omega
  exact Skel.check_sound boxes all_cov skp83 _ _ skp83_ok
theorem pr_82_84 (i : ℕ) (h1 : 82 ≤ i) (h2 : i < 84) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 83 then pr_82_83 i h1 h else pr_83_84 i (by omega) h2
theorem pr_84_85 (i : ℕ) (h1 : 84 ≤ i) (h2 : i < 85) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 84 := by omega
  exact Skel.check_sound boxes all_cov skp84 _ _ skp84_ok
theorem pr_85_86 (i : ℕ) (h1 : 85 ≤ i) (h2 : i < 86) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 85 := by omega
  exact Skel.check_sound boxes all_cov skp85 _ _ skp85_ok
theorem pr_86_87 (i : ℕ) (h1 : 86 ≤ i) (h2 : i < 87) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 86 := by omega
  exact Skel.check_sound boxes all_cov skp86 _ _ skp86_ok
theorem pr_85_87 (i : ℕ) (h1 : 85 ≤ i) (h2 : i < 87) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 86 then pr_85_86 i h1 h else pr_86_87 i (by omega) h2
theorem pr_84_87 (i : ℕ) (h1 : 84 ≤ i) (h2 : i < 87) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 85 then pr_84_85 i h1 h else pr_85_87 i (by omega) h2
theorem pr_82_87 (i : ℕ) (h1 : 82 ≤ i) (h2 : i < 87) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 84 then pr_82_84 i h1 h else pr_84_87 i (by omega) h2
theorem pr_78_87 (i : ℕ) (h1 : 78 ≤ i) (h2 : i < 87) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 82 then pr_78_82 i h1 h else pr_82_87 i (by omega) h2
theorem pr_87_88 (i : ℕ) (h1 : 87 ≤ i) (h2 : i < 88) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 87 := by omega
  exact Skel.check_sound boxes all_cov skp87 _ _ skp87_ok
theorem pr_88_89 (i : ℕ) (h1 : 88 ≤ i) (h2 : i < 89) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 88 := by omega
  exact Skel.check_sound boxes all_cov skp88 _ _ skp88_ok
theorem pr_87_89 (i : ℕ) (h1 : 87 ≤ i) (h2 : i < 89) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 88 then pr_87_88 i h1 h else pr_88_89 i (by omega) h2
theorem pr_89_90 (i : ℕ) (h1 : 89 ≤ i) (h2 : i < 90) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 89 := by omega
  exact Skel.check_sound boxes all_cov skp89 _ _ skp89_ok
theorem pr_90_91 (i : ℕ) (h1 : 90 ≤ i) (h2 : i < 91) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 90 := by omega
  exact Skel.check_sound boxes all_cov skp90 _ _ skp90_ok
theorem pr_91_92 (i : ℕ) (h1 : 91 ≤ i) (h2 : i < 92) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 91 := by omega
  exact Skel.check_sound boxes all_cov skp91 _ _ skp91_ok
theorem pr_90_92 (i : ℕ) (h1 : 90 ≤ i) (h2 : i < 92) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 91 then pr_90_91 i h1 h else pr_91_92 i (by omega) h2
theorem pr_89_92 (i : ℕ) (h1 : 89 ≤ i) (h2 : i < 92) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 90 then pr_89_90 i h1 h else pr_90_92 i (by omega) h2
theorem pr_87_92 (i : ℕ) (h1 : 87 ≤ i) (h2 : i < 92) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 89 then pr_87_89 i h1 h else pr_89_92 i (by omega) h2
theorem pr_92_93 (i : ℕ) (h1 : 92 ≤ i) (h2 : i < 93) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 92 := by omega
  exact Skel.check_sound boxes all_cov skp92 _ _ skp92_ok
theorem pr_93_94 (i : ℕ) (h1 : 93 ≤ i) (h2 : i < 94) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 93 := by omega
  exact Skel.check_sound boxes all_cov skp93 _ _ skp93_ok
theorem pr_92_94 (i : ℕ) (h1 : 92 ≤ i) (h2 : i < 94) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 93 then pr_92_93 i h1 h else pr_93_94 i (by omega) h2
theorem pr_94_95 (i : ℕ) (h1 : 94 ≤ i) (h2 : i < 95) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 94 := by omega
  exact Skel.check_sound boxes all_cov skp94 _ _ skp94_ok
theorem pr_95_96 (i : ℕ) (h1 : 95 ≤ i) (h2 : i < 96) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 95 := by omega
  exact Skel.check_sound boxes all_cov skp95 _ _ skp95_ok
theorem pr_96_97 (i : ℕ) (h1 : 96 ≤ i) (h2 : i < 97) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 96 := by omega
  exact Skel.check_sound boxes all_cov skp96 _ _ skp96_ok
theorem pr_95_97 (i : ℕ) (h1 : 95 ≤ i) (h2 : i < 97) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 96 then pr_95_96 i h1 h else pr_96_97 i (by omega) h2
theorem pr_94_97 (i : ℕ) (h1 : 94 ≤ i) (h2 : i < 97) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 95 then pr_94_95 i h1 h else pr_95_97 i (by omega) h2
theorem pr_92_97 (i : ℕ) (h1 : 92 ≤ i) (h2 : i < 97) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 94 then pr_92_94 i h1 h else pr_94_97 i (by omega) h2
theorem pr_87_97 (i : ℕ) (h1 : 87 ≤ i) (h2 : i < 97) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 92 then pr_87_92 i h1 h else pr_92_97 i (by omega) h2
theorem pr_78_97 (i : ℕ) (h1 : 78 ≤ i) (h2 : i < 97) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 87 then pr_78_87 i h1 h else pr_87_97 i (by omega) h2
theorem pr_97_98 (i : ℕ) (h1 : 97 ≤ i) (h2 : i < 98) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 97 := by omega
  exact Skel.check_sound boxes all_cov skp97 _ _ skp97_ok
theorem pr_98_99 (i : ℕ) (h1 : 98 ≤ i) (h2 : i < 99) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 98 := by omega
  exact Skel.check_sound boxes all_cov skp98 _ _ skp98_ok
theorem pr_97_99 (i : ℕ) (h1 : 97 ≤ i) (h2 : i < 99) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 98 then pr_97_98 i h1 h else pr_98_99 i (by omega) h2
theorem pr_99_100 (i : ℕ) (h1 : 99 ≤ i) (h2 : i < 100) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 99 := by omega
  exact Skel.check_sound boxes all_cov skp99 _ _ skp99_ok
theorem pr_100_101 (i : ℕ) (h1 : 100 ≤ i) (h2 : i < 101) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 100 := by omega
  exact Skel.check_sound boxes all_cov skp100 _ _ skp100_ok
theorem pr_101_102 (i : ℕ) (h1 : 101 ≤ i) (h2 : i < 102) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 101 := by omega
  exact Skel.check_sound boxes all_cov skp101 _ _ skp101_ok
theorem pr_100_102 (i : ℕ) (h1 : 100 ≤ i) (h2 : i < 102) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 101 then pr_100_101 i h1 h else pr_101_102 i (by omega) h2
theorem pr_99_102 (i : ℕ) (h1 : 99 ≤ i) (h2 : i < 102) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 100 then pr_99_100 i h1 h else pr_100_102 i (by omega) h2
theorem pr_97_102 (i : ℕ) (h1 : 97 ≤ i) (h2 : i < 102) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 99 then pr_97_99 i h1 h else pr_99_102 i (by omega) h2
theorem pr_102_103 (i : ℕ) (h1 : 102 ≤ i) (h2 : i < 103) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 102 := by omega
  exact Skel.check_sound boxes all_cov skp102 _ _ skp102_ok
theorem pr_103_104 (i : ℕ) (h1 : 103 ≤ i) (h2 : i < 104) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 103 := by omega
  exact Skel.check_sound boxes all_cov skp103 _ _ skp103_ok
theorem pr_102_104 (i : ℕ) (h1 : 102 ≤ i) (h2 : i < 104) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 103 then pr_102_103 i h1 h else pr_103_104 i (by omega) h2
theorem pr_104_105 (i : ℕ) (h1 : 104 ≤ i) (h2 : i < 105) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 104 := by omega
  exact Skel.check_sound boxes all_cov skp104 _ _ skp104_ok
theorem pr_105_106 (i : ℕ) (h1 : 105 ≤ i) (h2 : i < 106) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 105 := by omega
  exact Skel.check_sound boxes all_cov skp105 _ _ skp105_ok
theorem pr_106_107 (i : ℕ) (h1 : 106 ≤ i) (h2 : i < 107) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 106 := by omega
  exact Skel.check_sound boxes all_cov skp106 _ _ skp106_ok
theorem pr_105_107 (i : ℕ) (h1 : 105 ≤ i) (h2 : i < 107) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 106 then pr_105_106 i h1 h else pr_106_107 i (by omega) h2
theorem pr_104_107 (i : ℕ) (h1 : 104 ≤ i) (h2 : i < 107) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 105 then pr_104_105 i h1 h else pr_105_107 i (by omega) h2
theorem pr_102_107 (i : ℕ) (h1 : 102 ≤ i) (h2 : i < 107) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 104 then pr_102_104 i h1 h else pr_104_107 i (by omega) h2
theorem pr_97_107 (i : ℕ) (h1 : 97 ≤ i) (h2 : i < 107) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 102 then pr_97_102 i h1 h else pr_102_107 i (by omega) h2
theorem pr_107_108 (i : ℕ) (h1 : 107 ≤ i) (h2 : i < 108) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 107 := by omega
  exact Skel.check_sound boxes all_cov skp107 _ _ skp107_ok
theorem pr_108_109 (i : ℕ) (h1 : 108 ≤ i) (h2 : i < 109) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 108 := by omega
  exact Skel.check_sound boxes all_cov skp108 _ _ skp108_ok
theorem pr_107_109 (i : ℕ) (h1 : 107 ≤ i) (h2 : i < 109) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 108 then pr_107_108 i h1 h else pr_108_109 i (by omega) h2
theorem pr_109_110 (i : ℕ) (h1 : 109 ≤ i) (h2 : i < 110) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 109 := by omega
  exact Skel.check_sound boxes all_cov skp109 _ _ skp109_ok
theorem pr_110_111 (i : ℕ) (h1 : 110 ≤ i) (h2 : i < 111) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 110 := by omega
  exact Skel.check_sound boxes all_cov skp110 _ _ skp110_ok
theorem pr_111_112 (i : ℕ) (h1 : 111 ≤ i) (h2 : i < 112) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 111 := by omega
  exact Skel.check_sound boxes all_cov skp111 _ _ skp111_ok
theorem pr_110_112 (i : ℕ) (h1 : 110 ≤ i) (h2 : i < 112) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 111 then pr_110_111 i h1 h else pr_111_112 i (by omega) h2
theorem pr_109_112 (i : ℕ) (h1 : 109 ≤ i) (h2 : i < 112) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 110 then pr_109_110 i h1 h else pr_110_112 i (by omega) h2
theorem pr_107_112 (i : ℕ) (h1 : 107 ≤ i) (h2 : i < 112) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 109 then pr_107_109 i h1 h else pr_109_112 i (by omega) h2
theorem pr_112_113 (i : ℕ) (h1 : 112 ≤ i) (h2 : i < 113) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 112 := by omega
  exact Skel.check_sound boxes all_cov skp112 _ _ skp112_ok
theorem pr_113_114 (i : ℕ) (h1 : 113 ≤ i) (h2 : i < 114) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 113 := by omega
  exact Skel.check_sound boxes all_cov skp113 _ _ skp113_ok
theorem pr_112_114 (i : ℕ) (h1 : 112 ≤ i) (h2 : i < 114) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 113 then pr_112_113 i h1 h else pr_113_114 i (by omega) h2
theorem pr_114_115 (i : ℕ) (h1 : 114 ≤ i) (h2 : i < 115) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 114 := by omega
  exact Skel.check_sound boxes all_cov skp114 _ _ skp114_ok
theorem pr_115_116 (i : ℕ) (h1 : 115 ≤ i) (h2 : i < 116) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 115 := by omega
  exact Skel.check_sound boxes all_cov skp115 _ _ skp115_ok
theorem pr_116_117 (i : ℕ) (h1 : 116 ≤ i) (h2 : i < 117) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 116 := by omega
  exact Skel.check_sound boxes all_cov skp116 _ _ skp116_ok
theorem pr_115_117 (i : ℕ) (h1 : 115 ≤ i) (h2 : i < 117) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 116 then pr_115_116 i h1 h else pr_116_117 i (by omega) h2
theorem pr_114_117 (i : ℕ) (h1 : 114 ≤ i) (h2 : i < 117) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 115 then pr_114_115 i h1 h else pr_115_117 i (by omega) h2
theorem pr_112_117 (i : ℕ) (h1 : 112 ≤ i) (h2 : i < 117) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 114 then pr_112_114 i h1 h else pr_114_117 i (by omega) h2
theorem pr_107_117 (i : ℕ) (h1 : 107 ≤ i) (h2 : i < 117) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 112 then pr_107_112 i h1 h else pr_112_117 i (by omega) h2
theorem pr_97_117 (i : ℕ) (h1 : 97 ≤ i) (h2 : i < 117) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 107 then pr_97_107 i h1 h else pr_107_117 i (by omega) h2
theorem pr_78_117 (i : ℕ) (h1 : 78 ≤ i) (h2 : i < 117) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 97 then pr_78_97 i h1 h else pr_97_117 i (by omega) h2
theorem pr_117_118 (i : ℕ) (h1 : 117 ≤ i) (h2 : i < 118) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 117 := by omega
  exact Skel.check_sound boxes all_cov skp117 _ _ skp117_ok
theorem pr_118_119 (i : ℕ) (h1 : 118 ≤ i) (h2 : i < 119) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 118 := by omega
  exact Skel.check_sound boxes all_cov skp118 _ _ skp118_ok
theorem pr_117_119 (i : ℕ) (h1 : 117 ≤ i) (h2 : i < 119) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 118 then pr_117_118 i h1 h else pr_118_119 i (by omega) h2
theorem pr_119_120 (i : ℕ) (h1 : 119 ≤ i) (h2 : i < 120) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 119 := by omega
  exact Skel.check_sound boxes all_cov skp119 _ _ skp119_ok
theorem pr_120_121 (i : ℕ) (h1 : 120 ≤ i) (h2 : i < 121) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 120 := by omega
  exact Skel.check_sound boxes all_cov skp120 _ _ skp120_ok
theorem pr_121_122 (i : ℕ) (h1 : 121 ≤ i) (h2 : i < 122) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 121 := by omega
  exact Skel.check_sound boxes all_cov skp121 _ _ skp121_ok
theorem pr_120_122 (i : ℕ) (h1 : 120 ≤ i) (h2 : i < 122) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 121 then pr_120_121 i h1 h else pr_121_122 i (by omega) h2
theorem pr_119_122 (i : ℕ) (h1 : 119 ≤ i) (h2 : i < 122) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 120 then pr_119_120 i h1 h else pr_120_122 i (by omega) h2
theorem pr_117_122 (i : ℕ) (h1 : 117 ≤ i) (h2 : i < 122) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 119 then pr_117_119 i h1 h else pr_119_122 i (by omega) h2
theorem pr_122_123 (i : ℕ) (h1 : 122 ≤ i) (h2 : i < 123) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 122 := by omega
  exact Skel.check_sound boxes all_cov skp122 _ _ skp122_ok
theorem pr_123_124 (i : ℕ) (h1 : 123 ≤ i) (h2 : i < 124) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 123 := by omega
  exact Skel.check_sound boxes all_cov skp123 _ _ skp123_ok
theorem pr_122_124 (i : ℕ) (h1 : 122 ≤ i) (h2 : i < 124) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 123 then pr_122_123 i h1 h else pr_123_124 i (by omega) h2
theorem pr_124_125 (i : ℕ) (h1 : 124 ≤ i) (h2 : i < 125) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 124 := by omega
  exact Skel.check_sound boxes all_cov skp124 _ _ skp124_ok
theorem pr_125_126 (i : ℕ) (h1 : 125 ≤ i) (h2 : i < 126) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 125 := by omega
  exact Skel.check_sound boxes all_cov skp125 _ _ skp125_ok
theorem pr_126_127 (i : ℕ) (h1 : 126 ≤ i) (h2 : i < 127) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 126 := by omega
  exact Skel.check_sound boxes all_cov skp126 _ _ skp126_ok
theorem pr_125_127 (i : ℕ) (h1 : 125 ≤ i) (h2 : i < 127) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 126 then pr_125_126 i h1 h else pr_126_127 i (by omega) h2
theorem pr_124_127 (i : ℕ) (h1 : 124 ≤ i) (h2 : i < 127) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 125 then pr_124_125 i h1 h else pr_125_127 i (by omega) h2
theorem pr_122_127 (i : ℕ) (h1 : 122 ≤ i) (h2 : i < 127) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 124 then pr_122_124 i h1 h else pr_124_127 i (by omega) h2
theorem pr_117_127 (i : ℕ) (h1 : 117 ≤ i) (h2 : i < 127) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 122 then pr_117_122 i h1 h else pr_122_127 i (by omega) h2
theorem pr_127_128 (i : ℕ) (h1 : 127 ≤ i) (h2 : i < 128) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 127 := by omega
  exact Skel.check_sound boxes all_cov skp127 _ _ skp127_ok
theorem pr_128_129 (i : ℕ) (h1 : 128 ≤ i) (h2 : i < 129) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 128 := by omega
  exact Skel.check_sound boxes all_cov skp128 _ _ skp128_ok
theorem pr_127_129 (i : ℕ) (h1 : 127 ≤ i) (h2 : i < 129) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 128 then pr_127_128 i h1 h else pr_128_129 i (by omega) h2
theorem pr_129_130 (i : ℕ) (h1 : 129 ≤ i) (h2 : i < 130) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 129 := by omega
  exact Skel.check_sound boxes all_cov skp129 _ _ skp129_ok
theorem pr_130_131 (i : ℕ) (h1 : 130 ≤ i) (h2 : i < 131) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 130 := by omega
  exact Skel.check_sound boxes all_cov skp130 _ _ skp130_ok
theorem pr_131_132 (i : ℕ) (h1 : 131 ≤ i) (h2 : i < 132) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 131 := by omega
  exact Skel.check_sound boxes all_cov skp131 _ _ skp131_ok
theorem pr_130_132 (i : ℕ) (h1 : 130 ≤ i) (h2 : i < 132) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 131 then pr_130_131 i h1 h else pr_131_132 i (by omega) h2
theorem pr_129_132 (i : ℕ) (h1 : 129 ≤ i) (h2 : i < 132) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 130 then pr_129_130 i h1 h else pr_130_132 i (by omega) h2
theorem pr_127_132 (i : ℕ) (h1 : 127 ≤ i) (h2 : i < 132) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 129 then pr_127_129 i h1 h else pr_129_132 i (by omega) h2
theorem pr_132_133 (i : ℕ) (h1 : 132 ≤ i) (h2 : i < 133) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 132 := by omega
  exact Skel.check_sound boxes all_cov skp132 _ _ skp132_ok
theorem pr_133_134 (i : ℕ) (h1 : 133 ≤ i) (h2 : i < 134) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 133 := by omega
  exact Skel.check_sound boxes all_cov skp133 _ _ skp133_ok
theorem pr_132_134 (i : ℕ) (h1 : 132 ≤ i) (h2 : i < 134) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 133 then pr_132_133 i h1 h else pr_133_134 i (by omega) h2
theorem pr_134_135 (i : ℕ) (h1 : 134 ≤ i) (h2 : i < 135) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 134 := by omega
  exact Skel.check_sound boxes all_cov skp134 _ _ skp134_ok
theorem pr_135_136 (i : ℕ) (h1 : 135 ≤ i) (h2 : i < 136) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 135 := by omega
  exact Skel.check_sound boxes all_cov skp135 _ _ skp135_ok
theorem pr_136_137 (i : ℕ) (h1 : 136 ≤ i) (h2 : i < 137) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 136 := by omega
  exact Skel.check_sound boxes all_cov skp136 _ _ skp136_ok
theorem pr_135_137 (i : ℕ) (h1 : 135 ≤ i) (h2 : i < 137) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 136 then pr_135_136 i h1 h else pr_136_137 i (by omega) h2
theorem pr_134_137 (i : ℕ) (h1 : 134 ≤ i) (h2 : i < 137) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 135 then pr_134_135 i h1 h else pr_135_137 i (by omega) h2
theorem pr_132_137 (i : ℕ) (h1 : 132 ≤ i) (h2 : i < 137) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 134 then pr_132_134 i h1 h else pr_134_137 i (by omega) h2
theorem pr_127_137 (i : ℕ) (h1 : 127 ≤ i) (h2 : i < 137) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 132 then pr_127_132 i h1 h else pr_132_137 i (by omega) h2
theorem pr_117_137 (i : ℕ) (h1 : 117 ≤ i) (h2 : i < 137) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 127 then pr_117_127 i h1 h else pr_127_137 i (by omega) h2
theorem pr_137_138 (i : ℕ) (h1 : 137 ≤ i) (h2 : i < 138) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 137 := by omega
  exact Skel.check_sound boxes all_cov skp137 _ _ skp137_ok
theorem pr_138_139 (i : ℕ) (h1 : 138 ≤ i) (h2 : i < 139) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 138 := by omega
  exact Skel.check_sound boxes all_cov skp138 _ _ skp138_ok
theorem pr_137_139 (i : ℕ) (h1 : 137 ≤ i) (h2 : i < 139) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 138 then pr_137_138 i h1 h else pr_138_139 i (by omega) h2
theorem pr_139_140 (i : ℕ) (h1 : 139 ≤ i) (h2 : i < 140) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 139 := by omega
  exact Skel.check_sound boxes all_cov skp139 _ _ skp139_ok
theorem pr_140_141 (i : ℕ) (h1 : 140 ≤ i) (h2 : i < 141) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 140 := by omega
  exact Skel.check_sound boxes all_cov skp140 _ _ skp140_ok
theorem pr_141_142 (i : ℕ) (h1 : 141 ≤ i) (h2 : i < 142) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 141 := by omega
  exact Skel.check_sound boxes all_cov skp141 _ _ skp141_ok
theorem pr_140_142 (i : ℕ) (h1 : 140 ≤ i) (h2 : i < 142) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 141 then pr_140_141 i h1 h else pr_141_142 i (by omega) h2
theorem pr_139_142 (i : ℕ) (h1 : 139 ≤ i) (h2 : i < 142) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 140 then pr_139_140 i h1 h else pr_140_142 i (by omega) h2
theorem pr_137_142 (i : ℕ) (h1 : 137 ≤ i) (h2 : i < 142) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 139 then pr_137_139 i h1 h else pr_139_142 i (by omega) h2
theorem pr_142_143 (i : ℕ) (h1 : 142 ≤ i) (h2 : i < 143) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 142 := by omega
  exact Skel.check_sound boxes all_cov skp142 _ _ skp142_ok
theorem pr_143_144 (i : ℕ) (h1 : 143 ≤ i) (h2 : i < 144) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 143 := by omega
  exact Skel.check_sound boxes all_cov skp143 _ _ skp143_ok
theorem pr_142_144 (i : ℕ) (h1 : 142 ≤ i) (h2 : i < 144) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 143 then pr_142_143 i h1 h else pr_143_144 i (by omega) h2
theorem pr_144_145 (i : ℕ) (h1 : 144 ≤ i) (h2 : i < 145) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 144 := by omega
  exact Skel.check_sound boxes all_cov skp144 _ _ skp144_ok
theorem pr_145_146 (i : ℕ) (h1 : 145 ≤ i) (h2 : i < 146) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 145 := by omega
  exact Skel.check_sound boxes all_cov skp145 _ _ skp145_ok
theorem pr_146_147 (i : ℕ) (h1 : 146 ≤ i) (h2 : i < 147) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 146 := by omega
  exact Skel.check_sound boxes all_cov skp146 _ _ skp146_ok
theorem pr_145_147 (i : ℕ) (h1 : 145 ≤ i) (h2 : i < 147) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 146 then pr_145_146 i h1 h else pr_146_147 i (by omega) h2
theorem pr_144_147 (i : ℕ) (h1 : 144 ≤ i) (h2 : i < 147) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 145 then pr_144_145 i h1 h else pr_145_147 i (by omega) h2
theorem pr_142_147 (i : ℕ) (h1 : 142 ≤ i) (h2 : i < 147) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 144 then pr_142_144 i h1 h else pr_144_147 i (by omega) h2
theorem pr_137_147 (i : ℕ) (h1 : 137 ≤ i) (h2 : i < 147) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 142 then pr_137_142 i h1 h else pr_142_147 i (by omega) h2
theorem pr_147_148 (i : ℕ) (h1 : 147 ≤ i) (h2 : i < 148) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 147 := by omega
  exact Skel.check_sound boxes all_cov skp147 _ _ skp147_ok
theorem pr_148_149 (i : ℕ) (h1 : 148 ≤ i) (h2 : i < 149) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 148 := by omega
  exact Skel.check_sound boxes all_cov skp148 _ _ skp148_ok
theorem pr_147_149 (i : ℕ) (h1 : 147 ≤ i) (h2 : i < 149) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 148 then pr_147_148 i h1 h else pr_148_149 i (by omega) h2
theorem pr_149_150 (i : ℕ) (h1 : 149 ≤ i) (h2 : i < 150) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 149 := by omega
  exact Skel.check_sound boxes all_cov skp149 _ _ skp149_ok
theorem pr_150_151 (i : ℕ) (h1 : 150 ≤ i) (h2 : i < 151) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 150 := by omega
  exact Skel.check_sound boxes all_cov skp150 _ _ skp150_ok
theorem pr_151_152 (i : ℕ) (h1 : 151 ≤ i) (h2 : i < 152) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 151 := by omega
  exact Skel.check_sound boxes all_cov skp151 _ _ skp151_ok
theorem pr_150_152 (i : ℕ) (h1 : 150 ≤ i) (h2 : i < 152) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 151 then pr_150_151 i h1 h else pr_151_152 i (by omega) h2
theorem pr_149_152 (i : ℕ) (h1 : 149 ≤ i) (h2 : i < 152) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 150 then pr_149_150 i h1 h else pr_150_152 i (by omega) h2
theorem pr_147_152 (i : ℕ) (h1 : 147 ≤ i) (h2 : i < 152) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 149 then pr_147_149 i h1 h else pr_149_152 i (by omega) h2
theorem pr_152_153 (i : ℕ) (h1 : 152 ≤ i) (h2 : i < 153) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 152 := by omega
  exact Skel.check_sound boxes all_cov skp152 _ _ skp152_ok
theorem pr_153_154 (i : ℕ) (h1 : 153 ≤ i) (h2 : i < 154) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 153 := by omega
  exact Skel.check_sound boxes all_cov skp153 _ _ skp153_ok
theorem pr_152_154 (i : ℕ) (h1 : 152 ≤ i) (h2 : i < 154) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 153 then pr_152_153 i h1 h else pr_153_154 i (by omega) h2
theorem pr_154_155 (i : ℕ) (h1 : 154 ≤ i) (h2 : i < 155) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 154 := by omega
  exact Skel.check_sound boxes all_cov skp154 _ _ skp154_ok
theorem pr_155_156 (i : ℕ) (h1 : 155 ≤ i) (h2 : i < 156) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 155 := by omega
  exact Skel.check_sound boxes all_cov skp155 _ _ skp155_ok
theorem pr_156_157 (i : ℕ) (h1 : 156 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 156 := by omega
  exact Skel.check_sound boxes all_cov skp156 _ _ skp156_ok
theorem pr_155_157 (i : ℕ) (h1 : 155 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 156 then pr_155_156 i h1 h else pr_156_157 i (by omega) h2
theorem pr_154_157 (i : ℕ) (h1 : 154 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 155 then pr_154_155 i h1 h else pr_155_157 i (by omega) h2
theorem pr_152_157 (i : ℕ) (h1 : 152 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 154 then pr_152_154 i h1 h else pr_154_157 i (by omega) h2
theorem pr_147_157 (i : ℕ) (h1 : 147 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 152 then pr_147_152 i h1 h else pr_152_157 i (by omega) h2
theorem pr_137_157 (i : ℕ) (h1 : 137 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 147 then pr_137_147 i h1 h else pr_147_157 i (by omega) h2
theorem pr_117_157 (i : ℕ) (h1 : 117 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 137 then pr_117_137 i h1 h else pr_137_157 i (by omega) h2
theorem pr_78_157 (i : ℕ) (h1 : 78 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 117 then pr_78_117 i h1 h else pr_117_157 i (by omega) h2
theorem pr_0_157 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 157) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 78 then pr_0_78 i h1 h else pr_78_157 i (by omega) h2
theorem pr_157_158 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 158) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 157 := by omega
  exact Skel.check_sound boxes all_cov skp157 _ _ skp157_ok
theorem pr_158_159 (i : ℕ) (h1 : 158 ≤ i) (h2 : i < 159) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 158 := by omega
  exact Skel.check_sound boxes all_cov skp158 _ _ skp158_ok
theorem pr_157_159 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 159) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 158 then pr_157_158 i h1 h else pr_158_159 i (by omega) h2
theorem pr_159_160 (i : ℕ) (h1 : 159 ≤ i) (h2 : i < 160) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 159 := by omega
  exact Skel.check_sound boxes all_cov skp159 _ _ skp159_ok
theorem pr_160_161 (i : ℕ) (h1 : 160 ≤ i) (h2 : i < 161) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 160 := by omega
  exact Skel.check_sound boxes all_cov skp160 _ _ skp160_ok
theorem pr_159_161 (i : ℕ) (h1 : 159 ≤ i) (h2 : i < 161) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 160 then pr_159_160 i h1 h else pr_160_161 i (by omega) h2
theorem pr_157_161 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 161) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 159 then pr_157_159 i h1 h else pr_159_161 i (by omega) h2
theorem pr_161_162 (i : ℕ) (h1 : 161 ≤ i) (h2 : i < 162) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 161 := by omega
  exact Skel.check_sound boxes all_cov skp161 _ _ skp161_ok
theorem pr_162_163 (i : ℕ) (h1 : 162 ≤ i) (h2 : i < 163) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 162 := by omega
  exact Skel.check_sound boxes all_cov skp162 _ _ skp162_ok
theorem pr_161_163 (i : ℕ) (h1 : 161 ≤ i) (h2 : i < 163) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 162 then pr_161_162 i h1 h else pr_162_163 i (by omega) h2
theorem pr_163_164 (i : ℕ) (h1 : 163 ≤ i) (h2 : i < 164) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 163 := by omega
  exact Skel.check_sound boxes all_cov skp163 _ _ skp163_ok
theorem pr_164_165 (i : ℕ) (h1 : 164 ≤ i) (h2 : i < 165) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 164 := by omega
  exact Skel.check_sound boxes all_cov skp164 _ _ skp164_ok
theorem pr_165_166 (i : ℕ) (h1 : 165 ≤ i) (h2 : i < 166) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 165 := by omega
  exact Skel.check_sound boxes all_cov skp165 _ _ skp165_ok
theorem pr_164_166 (i : ℕ) (h1 : 164 ≤ i) (h2 : i < 166) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 165 then pr_164_165 i h1 h else pr_165_166 i (by omega) h2
theorem pr_163_166 (i : ℕ) (h1 : 163 ≤ i) (h2 : i < 166) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 164 then pr_163_164 i h1 h else pr_164_166 i (by omega) h2
theorem pr_161_166 (i : ℕ) (h1 : 161 ≤ i) (h2 : i < 166) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 163 then pr_161_163 i h1 h else pr_163_166 i (by omega) h2
theorem pr_157_166 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 166) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 161 then pr_157_161 i h1 h else pr_161_166 i (by omega) h2
theorem pr_166_167 (i : ℕ) (h1 : 166 ≤ i) (h2 : i < 167) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 166 := by omega
  exact Skel.check_sound boxes all_cov skp166 _ _ skp166_ok
theorem pr_167_168 (i : ℕ) (h1 : 167 ≤ i) (h2 : i < 168) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 167 := by omega
  exact Skel.check_sound boxes all_cov skp167 _ _ skp167_ok
theorem pr_166_168 (i : ℕ) (h1 : 166 ≤ i) (h2 : i < 168) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 167 then pr_166_167 i h1 h else pr_167_168 i (by omega) h2
theorem pr_168_169 (i : ℕ) (h1 : 168 ≤ i) (h2 : i < 169) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 168 := by omega
  exact Skel.check_sound boxes all_cov skp168 _ _ skp168_ok
theorem pr_169_170 (i : ℕ) (h1 : 169 ≤ i) (h2 : i < 170) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 169 := by omega
  exact Skel.check_sound boxes all_cov skp169 _ _ skp169_ok
theorem pr_170_171 (i : ℕ) (h1 : 170 ≤ i) (h2 : i < 171) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 170 := by omega
  exact Skel.check_sound boxes all_cov skp170 _ _ skp170_ok
theorem pr_169_171 (i : ℕ) (h1 : 169 ≤ i) (h2 : i < 171) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 170 then pr_169_170 i h1 h else pr_170_171 i (by omega) h2
theorem pr_168_171 (i : ℕ) (h1 : 168 ≤ i) (h2 : i < 171) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 169 then pr_168_169 i h1 h else pr_169_171 i (by omega) h2
theorem pr_166_171 (i : ℕ) (h1 : 166 ≤ i) (h2 : i < 171) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 168 then pr_166_168 i h1 h else pr_168_171 i (by omega) h2
theorem pr_171_172 (i : ℕ) (h1 : 171 ≤ i) (h2 : i < 172) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 171 := by omega
  exact Skel.check_sound boxes all_cov skp171 _ _ skp171_ok
theorem pr_172_173 (i : ℕ) (h1 : 172 ≤ i) (h2 : i < 173) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 172 := by omega
  exact Skel.check_sound boxes all_cov skp172 _ _ skp172_ok
theorem pr_171_173 (i : ℕ) (h1 : 171 ≤ i) (h2 : i < 173) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 172 then pr_171_172 i h1 h else pr_172_173 i (by omega) h2
theorem pr_173_174 (i : ℕ) (h1 : 173 ≤ i) (h2 : i < 174) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 173 := by omega
  exact Skel.check_sound boxes all_cov skp173 _ _ skp173_ok
theorem pr_174_175 (i : ℕ) (h1 : 174 ≤ i) (h2 : i < 175) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 174 := by omega
  exact Skel.check_sound boxes all_cov skp174 _ _ skp174_ok
theorem pr_175_176 (i : ℕ) (h1 : 175 ≤ i) (h2 : i < 176) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 175 := by omega
  exact Skel.check_sound boxes all_cov skp175 _ _ skp175_ok
theorem pr_174_176 (i : ℕ) (h1 : 174 ≤ i) (h2 : i < 176) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 175 then pr_174_175 i h1 h else pr_175_176 i (by omega) h2
theorem pr_173_176 (i : ℕ) (h1 : 173 ≤ i) (h2 : i < 176) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 174 then pr_173_174 i h1 h else pr_174_176 i (by omega) h2
theorem pr_171_176 (i : ℕ) (h1 : 171 ≤ i) (h2 : i < 176) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 173 then pr_171_173 i h1 h else pr_173_176 i (by omega) h2
theorem pr_166_176 (i : ℕ) (h1 : 166 ≤ i) (h2 : i < 176) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 171 then pr_166_171 i h1 h else pr_171_176 i (by omega) h2
theorem pr_157_176 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 176) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 166 then pr_157_166 i h1 h else pr_166_176 i (by omega) h2
theorem pr_176_177 (i : ℕ) (h1 : 176 ≤ i) (h2 : i < 177) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 176 := by omega
  exact Skel.check_sound boxes all_cov skp176 _ _ skp176_ok
theorem pr_177_178 (i : ℕ) (h1 : 177 ≤ i) (h2 : i < 178) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 177 := by omega
  exact Skel.check_sound boxes all_cov skp177 _ _ skp177_ok
theorem pr_176_178 (i : ℕ) (h1 : 176 ≤ i) (h2 : i < 178) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 177 then pr_176_177 i h1 h else pr_177_178 i (by omega) h2
theorem pr_178_179 (i : ℕ) (h1 : 178 ≤ i) (h2 : i < 179) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 178 := by omega
  exact Skel.check_sound boxes all_cov skp178 _ _ skp178_ok
theorem pr_179_180 (i : ℕ) (h1 : 179 ≤ i) (h2 : i < 180) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 179 := by omega
  exact Skel.check_sound boxes all_cov skp179 _ _ skp179_ok
theorem pr_180_181 (i : ℕ) (h1 : 180 ≤ i) (h2 : i < 181) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 180 := by omega
  exact Skel.check_sound boxes all_cov skp180 _ _ skp180_ok
theorem pr_179_181 (i : ℕ) (h1 : 179 ≤ i) (h2 : i < 181) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 180 then pr_179_180 i h1 h else pr_180_181 i (by omega) h2
theorem pr_178_181 (i : ℕ) (h1 : 178 ≤ i) (h2 : i < 181) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 179 then pr_178_179 i h1 h else pr_179_181 i (by omega) h2
theorem pr_176_181 (i : ℕ) (h1 : 176 ≤ i) (h2 : i < 181) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 178 then pr_176_178 i h1 h else pr_178_181 i (by omega) h2
theorem pr_181_182 (i : ℕ) (h1 : 181 ≤ i) (h2 : i < 182) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 181 := by omega
  exact Skel.check_sound boxes all_cov skp181 _ _ skp181_ok
theorem pr_182_183 (i : ℕ) (h1 : 182 ≤ i) (h2 : i < 183) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 182 := by omega
  exact Skel.check_sound boxes all_cov skp182 _ _ skp182_ok
theorem pr_181_183 (i : ℕ) (h1 : 181 ≤ i) (h2 : i < 183) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 182 then pr_181_182 i h1 h else pr_182_183 i (by omega) h2
theorem pr_183_184 (i : ℕ) (h1 : 183 ≤ i) (h2 : i < 184) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 183 := by omega
  exact Skel.check_sound boxes all_cov skp183 _ _ skp183_ok
theorem pr_184_185 (i : ℕ) (h1 : 184 ≤ i) (h2 : i < 185) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 184 := by omega
  exact Skel.check_sound boxes all_cov skp184 _ _ skp184_ok
theorem pr_185_186 (i : ℕ) (h1 : 185 ≤ i) (h2 : i < 186) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 185 := by omega
  exact Skel.check_sound boxes all_cov skp185 _ _ skp185_ok
theorem pr_184_186 (i : ℕ) (h1 : 184 ≤ i) (h2 : i < 186) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 185 then pr_184_185 i h1 h else pr_185_186 i (by omega) h2
theorem pr_183_186 (i : ℕ) (h1 : 183 ≤ i) (h2 : i < 186) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 184 then pr_183_184 i h1 h else pr_184_186 i (by omega) h2
theorem pr_181_186 (i : ℕ) (h1 : 181 ≤ i) (h2 : i < 186) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 183 then pr_181_183 i h1 h else pr_183_186 i (by omega) h2
theorem pr_176_186 (i : ℕ) (h1 : 176 ≤ i) (h2 : i < 186) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 181 then pr_176_181 i h1 h else pr_181_186 i (by omega) h2
theorem pr_186_187 (i : ℕ) (h1 : 186 ≤ i) (h2 : i < 187) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 186 := by omega
  exact Skel.check_sound boxes all_cov skp186 _ _ skp186_ok
theorem pr_187_188 (i : ℕ) (h1 : 187 ≤ i) (h2 : i < 188) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 187 := by omega
  exact Skel.check_sound boxes all_cov skp187 _ _ skp187_ok
theorem pr_186_188 (i : ℕ) (h1 : 186 ≤ i) (h2 : i < 188) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 187 then pr_186_187 i h1 h else pr_187_188 i (by omega) h2
theorem pr_188_189 (i : ℕ) (h1 : 188 ≤ i) (h2 : i < 189) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 188 := by omega
  exact Skel.check_sound boxes all_cov skp188 _ _ skp188_ok
theorem pr_189_190 (i : ℕ) (h1 : 189 ≤ i) (h2 : i < 190) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 189 := by omega
  exact Skel.check_sound boxes all_cov skp189 _ _ skp189_ok
theorem pr_190_191 (i : ℕ) (h1 : 190 ≤ i) (h2 : i < 191) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 190 := by omega
  exact Skel.check_sound boxes all_cov skp190 _ _ skp190_ok
theorem pr_189_191 (i : ℕ) (h1 : 189 ≤ i) (h2 : i < 191) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 190 then pr_189_190 i h1 h else pr_190_191 i (by omega) h2
theorem pr_188_191 (i : ℕ) (h1 : 188 ≤ i) (h2 : i < 191) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 189 then pr_188_189 i h1 h else pr_189_191 i (by omega) h2
theorem pr_186_191 (i : ℕ) (h1 : 186 ≤ i) (h2 : i < 191) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 188 then pr_186_188 i h1 h else pr_188_191 i (by omega) h2
theorem pr_191_192 (i : ℕ) (h1 : 191 ≤ i) (h2 : i < 192) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 191 := by omega
  exact Skel.check_sound boxes all_cov skp191 _ _ skp191_ok
theorem pr_192_193 (i : ℕ) (h1 : 192 ≤ i) (h2 : i < 193) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 192 := by omega
  exact Skel.check_sound boxes all_cov skp192 _ _ skp192_ok
theorem pr_191_193 (i : ℕ) (h1 : 191 ≤ i) (h2 : i < 193) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 192 then pr_191_192 i h1 h else pr_192_193 i (by omega) h2
theorem pr_193_194 (i : ℕ) (h1 : 193 ≤ i) (h2 : i < 194) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 193 := by omega
  exact Skel.check_sound boxes all_cov skp193 _ _ skp193_ok
theorem pr_194_195 (i : ℕ) (h1 : 194 ≤ i) (h2 : i < 195) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 194 := by omega
  exact Skel.check_sound boxes all_cov skp194 _ _ skp194_ok
theorem pr_195_196 (i : ℕ) (h1 : 195 ≤ i) (h2 : i < 196) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 195 := by omega
  exact Skel.check_sound boxes all_cov skp195 _ _ skp195_ok
theorem pr_194_196 (i : ℕ) (h1 : 194 ≤ i) (h2 : i < 196) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 195 then pr_194_195 i h1 h else pr_195_196 i (by omega) h2
theorem pr_193_196 (i : ℕ) (h1 : 193 ≤ i) (h2 : i < 196) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 194 then pr_193_194 i h1 h else pr_194_196 i (by omega) h2
theorem pr_191_196 (i : ℕ) (h1 : 191 ≤ i) (h2 : i < 196) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 193 then pr_191_193 i h1 h else pr_193_196 i (by omega) h2
theorem pr_186_196 (i : ℕ) (h1 : 186 ≤ i) (h2 : i < 196) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 191 then pr_186_191 i h1 h else pr_191_196 i (by omega) h2
theorem pr_176_196 (i : ℕ) (h1 : 176 ≤ i) (h2 : i < 196) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 186 then pr_176_186 i h1 h else pr_186_196 i (by omega) h2
theorem pr_157_196 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 196) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 176 then pr_157_176 i h1 h else pr_176_196 i (by omega) h2
theorem pr_196_197 (i : ℕ) (h1 : 196 ≤ i) (h2 : i < 197) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 196 := by omega
  exact Skel.check_sound boxes all_cov skp196 _ _ skp196_ok
theorem pr_197_198 (i : ℕ) (h1 : 197 ≤ i) (h2 : i < 198) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 197 := by omega
  exact Skel.check_sound boxes all_cov skp197 _ _ skp197_ok
theorem pr_196_198 (i : ℕ) (h1 : 196 ≤ i) (h2 : i < 198) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 197 then pr_196_197 i h1 h else pr_197_198 i (by omega) h2
theorem pr_198_199 (i : ℕ) (h1 : 198 ≤ i) (h2 : i < 199) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 198 := by omega
  exact Skel.check_sound boxes all_cov skp198 _ _ skp198_ok
theorem pr_199_200 (i : ℕ) (h1 : 199 ≤ i) (h2 : i < 200) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 199 := by omega
  exact Skel.check_sound boxes all_cov skp199 _ _ skp199_ok
theorem pr_200_201 (i : ℕ) (h1 : 200 ≤ i) (h2 : i < 201) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 200 := by omega
  exact Skel.check_sound boxes all_cov skp200 _ _ skp200_ok
theorem pr_199_201 (i : ℕ) (h1 : 199 ≤ i) (h2 : i < 201) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 200 then pr_199_200 i h1 h else pr_200_201 i (by omega) h2
theorem pr_198_201 (i : ℕ) (h1 : 198 ≤ i) (h2 : i < 201) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 199 then pr_198_199 i h1 h else pr_199_201 i (by omega) h2
theorem pr_196_201 (i : ℕ) (h1 : 196 ≤ i) (h2 : i < 201) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 198 then pr_196_198 i h1 h else pr_198_201 i (by omega) h2
theorem pr_201_202 (i : ℕ) (h1 : 201 ≤ i) (h2 : i < 202) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 201 := by omega
  exact Skel.check_sound boxes all_cov skp201 _ _ skp201_ok
theorem pr_202_203 (i : ℕ) (h1 : 202 ≤ i) (h2 : i < 203) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 202 := by omega
  exact Skel.check_sound boxes all_cov skp202 _ _ skp202_ok
theorem pr_201_203 (i : ℕ) (h1 : 201 ≤ i) (h2 : i < 203) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 202 then pr_201_202 i h1 h else pr_202_203 i (by omega) h2
theorem pr_203_204 (i : ℕ) (h1 : 203 ≤ i) (h2 : i < 204) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 203 := by omega
  exact Skel.check_sound boxes all_cov skp203 _ _ skp203_ok
theorem pr_204_205 (i : ℕ) (h1 : 204 ≤ i) (h2 : i < 205) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 204 := by omega
  exact Skel.check_sound boxes all_cov skp204 _ _ skp204_ok
theorem pr_205_206 (i : ℕ) (h1 : 205 ≤ i) (h2 : i < 206) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 205 := by omega
  exact Skel.check_sound boxes all_cov skp205 _ _ skp205_ok
theorem pr_204_206 (i : ℕ) (h1 : 204 ≤ i) (h2 : i < 206) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 205 then pr_204_205 i h1 h else pr_205_206 i (by omega) h2
theorem pr_203_206 (i : ℕ) (h1 : 203 ≤ i) (h2 : i < 206) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 204 then pr_203_204 i h1 h else pr_204_206 i (by omega) h2
theorem pr_201_206 (i : ℕ) (h1 : 201 ≤ i) (h2 : i < 206) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 203 then pr_201_203 i h1 h else pr_203_206 i (by omega) h2
theorem pr_196_206 (i : ℕ) (h1 : 196 ≤ i) (h2 : i < 206) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 201 then pr_196_201 i h1 h else pr_201_206 i (by omega) h2
theorem pr_206_207 (i : ℕ) (h1 : 206 ≤ i) (h2 : i < 207) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 206 := by omega
  exact Skel.check_sound boxes all_cov skp206 _ _ skp206_ok
theorem pr_207_208 (i : ℕ) (h1 : 207 ≤ i) (h2 : i < 208) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 207 := by omega
  exact Skel.check_sound boxes all_cov skp207 _ _ skp207_ok
theorem pr_206_208 (i : ℕ) (h1 : 206 ≤ i) (h2 : i < 208) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 207 then pr_206_207 i h1 h else pr_207_208 i (by omega) h2
theorem pr_208_209 (i : ℕ) (h1 : 208 ≤ i) (h2 : i < 209) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 208 := by omega
  exact Skel.check_sound boxes all_cov skp208 _ _ skp208_ok
theorem pr_209_210 (i : ℕ) (h1 : 209 ≤ i) (h2 : i < 210) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 209 := by omega
  exact Skel.check_sound boxes all_cov skp209 _ _ skp209_ok
theorem pr_210_211 (i : ℕ) (h1 : 210 ≤ i) (h2 : i < 211) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 210 := by omega
  exact Skel.check_sound boxes all_cov skp210 _ _ skp210_ok
theorem pr_209_211 (i : ℕ) (h1 : 209 ≤ i) (h2 : i < 211) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 210 then pr_209_210 i h1 h else pr_210_211 i (by omega) h2
theorem pr_208_211 (i : ℕ) (h1 : 208 ≤ i) (h2 : i < 211) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 209 then pr_208_209 i h1 h else pr_209_211 i (by omega) h2
theorem pr_206_211 (i : ℕ) (h1 : 206 ≤ i) (h2 : i < 211) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 208 then pr_206_208 i h1 h else pr_208_211 i (by omega) h2
theorem pr_211_212 (i : ℕ) (h1 : 211 ≤ i) (h2 : i < 212) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 211 := by omega
  exact Skel.check_sound boxes all_cov skp211 _ _ skp211_ok
theorem pr_212_213 (i : ℕ) (h1 : 212 ≤ i) (h2 : i < 213) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 212 := by omega
  exact Skel.check_sound boxes all_cov skp212 _ _ skp212_ok
theorem pr_211_213 (i : ℕ) (h1 : 211 ≤ i) (h2 : i < 213) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 212 then pr_211_212 i h1 h else pr_212_213 i (by omega) h2
theorem pr_213_214 (i : ℕ) (h1 : 213 ≤ i) (h2 : i < 214) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 213 := by omega
  exact Skel.check_sound boxes all_cov skp213 _ _ skp213_ok
theorem pr_214_215 (i : ℕ) (h1 : 214 ≤ i) (h2 : i < 215) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 214 := by omega
  exact Skel.check_sound boxes all_cov skp214 _ _ skp214_ok
theorem pr_215_216 (i : ℕ) (h1 : 215 ≤ i) (h2 : i < 216) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 215 := by omega
  exact Skel.check_sound boxes all_cov skp215 _ _ skp215_ok
theorem pr_214_216 (i : ℕ) (h1 : 214 ≤ i) (h2 : i < 216) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 215 then pr_214_215 i h1 h else pr_215_216 i (by omega) h2
theorem pr_213_216 (i : ℕ) (h1 : 213 ≤ i) (h2 : i < 216) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 214 then pr_213_214 i h1 h else pr_214_216 i (by omega) h2
theorem pr_211_216 (i : ℕ) (h1 : 211 ≤ i) (h2 : i < 216) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 213 then pr_211_213 i h1 h else pr_213_216 i (by omega) h2
theorem pr_206_216 (i : ℕ) (h1 : 206 ≤ i) (h2 : i < 216) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 211 then pr_206_211 i h1 h else pr_211_216 i (by omega) h2
theorem pr_196_216 (i : ℕ) (h1 : 196 ≤ i) (h2 : i < 216) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 206 then pr_196_206 i h1 h else pr_206_216 i (by omega) h2
theorem pr_216_217 (i : ℕ) (h1 : 216 ≤ i) (h2 : i < 217) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 216 := by omega
  exact Skel.check_sound boxes all_cov skp216 _ _ skp216_ok
theorem pr_217_218 (i : ℕ) (h1 : 217 ≤ i) (h2 : i < 218) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 217 := by omega
  exact Skel.check_sound boxes all_cov skp217 _ _ skp217_ok
theorem pr_216_218 (i : ℕ) (h1 : 216 ≤ i) (h2 : i < 218) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 217 then pr_216_217 i h1 h else pr_217_218 i (by omega) h2
theorem pr_218_219 (i : ℕ) (h1 : 218 ≤ i) (h2 : i < 219) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 218 := by omega
  exact Skel.check_sound boxes all_cov skp218 _ _ skp218_ok
theorem pr_219_220 (i : ℕ) (h1 : 219 ≤ i) (h2 : i < 220) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 219 := by omega
  exact Skel.check_sound boxes all_cov skp219 _ _ skp219_ok
theorem pr_220_221 (i : ℕ) (h1 : 220 ≤ i) (h2 : i < 221) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 220 := by omega
  exact Skel.check_sound boxes all_cov skp220 _ _ skp220_ok
theorem pr_219_221 (i : ℕ) (h1 : 219 ≤ i) (h2 : i < 221) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 220 then pr_219_220 i h1 h else pr_220_221 i (by omega) h2
theorem pr_218_221 (i : ℕ) (h1 : 218 ≤ i) (h2 : i < 221) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 219 then pr_218_219 i h1 h else pr_219_221 i (by omega) h2
theorem pr_216_221 (i : ℕ) (h1 : 216 ≤ i) (h2 : i < 221) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 218 then pr_216_218 i h1 h else pr_218_221 i (by omega) h2
theorem pr_221_222 (i : ℕ) (h1 : 221 ≤ i) (h2 : i < 222) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 221 := by omega
  exact Skel.check_sound boxes all_cov skp221 _ _ skp221_ok
theorem pr_222_223 (i : ℕ) (h1 : 222 ≤ i) (h2 : i < 223) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 222 := by omega
  exact Skel.check_sound boxes all_cov skp222 _ _ skp222_ok
theorem pr_221_223 (i : ℕ) (h1 : 221 ≤ i) (h2 : i < 223) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 222 then pr_221_222 i h1 h else pr_222_223 i (by omega) h2
theorem pr_223_224 (i : ℕ) (h1 : 223 ≤ i) (h2 : i < 224) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 223 := by omega
  exact Skel.check_sound boxes all_cov skp223 _ _ skp223_ok
theorem pr_224_225 (i : ℕ) (h1 : 224 ≤ i) (h2 : i < 225) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 224 := by omega
  exact Skel.check_sound boxes all_cov skp224 _ _ skp224_ok
theorem pr_225_226 (i : ℕ) (h1 : 225 ≤ i) (h2 : i < 226) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 225 := by omega
  exact Skel.check_sound boxes all_cov skp225 _ _ skp225_ok
theorem pr_224_226 (i : ℕ) (h1 : 224 ≤ i) (h2 : i < 226) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 225 then pr_224_225 i h1 h else pr_225_226 i (by omega) h2
theorem pr_223_226 (i : ℕ) (h1 : 223 ≤ i) (h2 : i < 226) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 224 then pr_223_224 i h1 h else pr_224_226 i (by omega) h2
theorem pr_221_226 (i : ℕ) (h1 : 221 ≤ i) (h2 : i < 226) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 223 then pr_221_223 i h1 h else pr_223_226 i (by omega) h2
theorem pr_216_226 (i : ℕ) (h1 : 216 ≤ i) (h2 : i < 226) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 221 then pr_216_221 i h1 h else pr_221_226 i (by omega) h2
theorem pr_226_227 (i : ℕ) (h1 : 226 ≤ i) (h2 : i < 227) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 226 := by omega
  exact Skel.check_sound boxes all_cov skp226 _ _ skp226_ok
theorem pr_227_228 (i : ℕ) (h1 : 227 ≤ i) (h2 : i < 228) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 227 := by omega
  exact Skel.check_sound boxes all_cov skp227 _ _ skp227_ok
theorem pr_226_228 (i : ℕ) (h1 : 226 ≤ i) (h2 : i < 228) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 227 then pr_226_227 i h1 h else pr_227_228 i (by omega) h2
theorem pr_228_229 (i : ℕ) (h1 : 228 ≤ i) (h2 : i < 229) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 228 := by omega
  exact Skel.check_sound boxes all_cov skp228 _ _ skp228_ok
theorem pr_229_230 (i : ℕ) (h1 : 229 ≤ i) (h2 : i < 230) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 229 := by omega
  exact Skel.check_sound boxes all_cov skp229 _ _ skp229_ok
theorem pr_230_231 (i : ℕ) (h1 : 230 ≤ i) (h2 : i < 231) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 230 := by omega
  exact Skel.check_sound boxes all_cov skp230 _ _ skp230_ok
theorem pr_229_231 (i : ℕ) (h1 : 229 ≤ i) (h2 : i < 231) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 230 then pr_229_230 i h1 h else pr_230_231 i (by omega) h2
theorem pr_228_231 (i : ℕ) (h1 : 228 ≤ i) (h2 : i < 231) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 229 then pr_228_229 i h1 h else pr_229_231 i (by omega) h2
theorem pr_226_231 (i : ℕ) (h1 : 226 ≤ i) (h2 : i < 231) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 228 then pr_226_228 i h1 h else pr_228_231 i (by omega) h2
theorem pr_231_232 (i : ℕ) (h1 : 231 ≤ i) (h2 : i < 232) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 231 := by omega
  exact Skel.check_sound boxes all_cov skp231 _ _ skp231_ok
theorem pr_232_233 (i : ℕ) (h1 : 232 ≤ i) (h2 : i < 233) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 232 := by omega
  exact Skel.check_sound boxes all_cov skp232 _ _ skp232_ok
theorem pr_231_233 (i : ℕ) (h1 : 231 ≤ i) (h2 : i < 233) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 232 then pr_231_232 i h1 h else pr_232_233 i (by omega) h2
theorem pr_233_234 (i : ℕ) (h1 : 233 ≤ i) (h2 : i < 234) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 233 := by omega
  exact Skel.check_sound boxes all_cov skp233 _ _ skp233_ok
theorem pr_234_235 (i : ℕ) (h1 : 234 ≤ i) (h2 : i < 235) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 234 := by omega
  exact Skel.check_sound boxes all_cov skp234 _ _ skp234_ok
theorem pr_235_236 (i : ℕ) (h1 : 235 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 235 := by omega
  exact Skel.check_sound boxes all_cov skp235 _ _ skp235_ok
theorem pr_234_236 (i : ℕ) (h1 : 234 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 235 then pr_234_235 i h1 h else pr_235_236 i (by omega) h2
theorem pr_233_236 (i : ℕ) (h1 : 233 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 234 then pr_233_234 i h1 h else pr_234_236 i (by omega) h2
theorem pr_231_236 (i : ℕ) (h1 : 231 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 233 then pr_231_233 i h1 h else pr_233_236 i (by omega) h2
theorem pr_226_236 (i : ℕ) (h1 : 226 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 231 then pr_226_231 i h1 h else pr_231_236 i (by omega) h2
theorem pr_216_236 (i : ℕ) (h1 : 216 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 226 then pr_216_226 i h1 h else pr_226_236 i (by omega) h2
theorem pr_196_236 (i : ℕ) (h1 : 196 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 216 then pr_196_216 i h1 h else pr_216_236 i (by omega) h2
theorem pr_157_236 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 236) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 196 then pr_157_196 i h1 h else pr_196_236 i (by omega) h2
theorem pr_236_237 (i : ℕ) (h1 : 236 ≤ i) (h2 : i < 237) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 236 := by omega
  exact Skel.check_sound boxes all_cov skp236 _ _ skp236_ok
theorem pr_237_238 (i : ℕ) (h1 : 237 ≤ i) (h2 : i < 238) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 237 := by omega
  exact Skel.check_sound boxes all_cov skp237 _ _ skp237_ok
theorem pr_236_238 (i : ℕ) (h1 : 236 ≤ i) (h2 : i < 238) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 237 then pr_236_237 i h1 h else pr_237_238 i (by omega) h2
theorem pr_238_239 (i : ℕ) (h1 : 238 ≤ i) (h2 : i < 239) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 238 := by omega
  exact Skel.check_sound boxes all_cov skp238 _ _ skp238_ok
theorem pr_239_240 (i : ℕ) (h1 : 239 ≤ i) (h2 : i < 240) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 239 := by omega
  exact Skel.check_sound boxes all_cov skp239 _ _ skp239_ok
theorem pr_238_240 (i : ℕ) (h1 : 238 ≤ i) (h2 : i < 240) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 239 then pr_238_239 i h1 h else pr_239_240 i (by omega) h2
theorem pr_236_240 (i : ℕ) (h1 : 236 ≤ i) (h2 : i < 240) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 238 then pr_236_238 i h1 h else pr_238_240 i (by omega) h2
theorem pr_240_241 (i : ℕ) (h1 : 240 ≤ i) (h2 : i < 241) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 240 := by omega
  exact Skel.check_sound boxes all_cov skp240 _ _ skp240_ok
theorem pr_241_242 (i : ℕ) (h1 : 241 ≤ i) (h2 : i < 242) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 241 := by omega
  exact Skel.check_sound boxes all_cov skp241 _ _ skp241_ok
theorem pr_240_242 (i : ℕ) (h1 : 240 ≤ i) (h2 : i < 242) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 241 then pr_240_241 i h1 h else pr_241_242 i (by omega) h2
theorem pr_242_243 (i : ℕ) (h1 : 242 ≤ i) (h2 : i < 243) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 242 := by omega
  exact Skel.check_sound boxes all_cov skp242 _ _ skp242_ok
theorem pr_243_244 (i : ℕ) (h1 : 243 ≤ i) (h2 : i < 244) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 243 := by omega
  exact Skel.check_sound boxes all_cov skp243 _ _ skp243_ok
theorem pr_244_245 (i : ℕ) (h1 : 244 ≤ i) (h2 : i < 245) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 244 := by omega
  exact Skel.check_sound boxes all_cov skp244 _ _ skp244_ok
theorem pr_243_245 (i : ℕ) (h1 : 243 ≤ i) (h2 : i < 245) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 244 then pr_243_244 i h1 h else pr_244_245 i (by omega) h2
theorem pr_242_245 (i : ℕ) (h1 : 242 ≤ i) (h2 : i < 245) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 243 then pr_242_243 i h1 h else pr_243_245 i (by omega) h2
theorem pr_240_245 (i : ℕ) (h1 : 240 ≤ i) (h2 : i < 245) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 242 then pr_240_242 i h1 h else pr_242_245 i (by omega) h2
theorem pr_236_245 (i : ℕ) (h1 : 236 ≤ i) (h2 : i < 245) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 240 then pr_236_240 i h1 h else pr_240_245 i (by omega) h2
theorem pr_245_246 (i : ℕ) (h1 : 245 ≤ i) (h2 : i < 246) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 245 := by omega
  exact Skel.check_sound boxes all_cov skp245 _ _ skp245_ok
theorem pr_246_247 (i : ℕ) (h1 : 246 ≤ i) (h2 : i < 247) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 246 := by omega
  exact Skel.check_sound boxes all_cov skp246 _ _ skp246_ok
theorem pr_245_247 (i : ℕ) (h1 : 245 ≤ i) (h2 : i < 247) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 246 then pr_245_246 i h1 h else pr_246_247 i (by omega) h2
theorem pr_247_248 (i : ℕ) (h1 : 247 ≤ i) (h2 : i < 248) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 247 := by omega
  exact Skel.check_sound boxes all_cov skp247 _ _ skp247_ok
theorem pr_248_249 (i : ℕ) (h1 : 248 ≤ i) (h2 : i < 249) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 248 := by omega
  exact Skel.check_sound boxes all_cov skp248 _ _ skp248_ok
theorem pr_249_250 (i : ℕ) (h1 : 249 ≤ i) (h2 : i < 250) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 249 := by omega
  exact Skel.check_sound boxes all_cov skp249 _ _ skp249_ok
theorem pr_248_250 (i : ℕ) (h1 : 248 ≤ i) (h2 : i < 250) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 249 then pr_248_249 i h1 h else pr_249_250 i (by omega) h2
theorem pr_247_250 (i : ℕ) (h1 : 247 ≤ i) (h2 : i < 250) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 248 then pr_247_248 i h1 h else pr_248_250 i (by omega) h2
theorem pr_245_250 (i : ℕ) (h1 : 245 ≤ i) (h2 : i < 250) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 247 then pr_245_247 i h1 h else pr_247_250 i (by omega) h2
theorem pr_250_251 (i : ℕ) (h1 : 250 ≤ i) (h2 : i < 251) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 250 := by omega
  exact Skel.check_sound boxes all_cov skp250 _ _ skp250_ok
theorem pr_251_252 (i : ℕ) (h1 : 251 ≤ i) (h2 : i < 252) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 251 := by omega
  exact Skel.check_sound boxes all_cov skp251 _ _ skp251_ok
theorem pr_250_252 (i : ℕ) (h1 : 250 ≤ i) (h2 : i < 252) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 251 then pr_250_251 i h1 h else pr_251_252 i (by omega) h2
theorem pr_252_253 (i : ℕ) (h1 : 252 ≤ i) (h2 : i < 253) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 252 := by omega
  exact Skel.check_sound boxes all_cov skp252 _ _ skp252_ok
theorem pr_253_254 (i : ℕ) (h1 : 253 ≤ i) (h2 : i < 254) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 253 := by omega
  exact Skel.check_sound boxes all_cov skp253 _ _ skp253_ok
theorem pr_254_255 (i : ℕ) (h1 : 254 ≤ i) (h2 : i < 255) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 254 := by omega
  exact Skel.check_sound boxes all_cov skp254 _ _ skp254_ok
theorem pr_253_255 (i : ℕ) (h1 : 253 ≤ i) (h2 : i < 255) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 254 then pr_253_254 i h1 h else pr_254_255 i (by omega) h2
theorem pr_252_255 (i : ℕ) (h1 : 252 ≤ i) (h2 : i < 255) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 253 then pr_252_253 i h1 h else pr_253_255 i (by omega) h2
theorem pr_250_255 (i : ℕ) (h1 : 250 ≤ i) (h2 : i < 255) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 252 then pr_250_252 i h1 h else pr_252_255 i (by omega) h2
theorem pr_245_255 (i : ℕ) (h1 : 245 ≤ i) (h2 : i < 255) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 250 then pr_245_250 i h1 h else pr_250_255 i (by omega) h2
theorem pr_236_255 (i : ℕ) (h1 : 236 ≤ i) (h2 : i < 255) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 245 then pr_236_245 i h1 h else pr_245_255 i (by omega) h2
theorem pr_255_256 (i : ℕ) (h1 : 255 ≤ i) (h2 : i < 256) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 255 := by omega
  exact Skel.check_sound boxes all_cov skp255 _ _ skp255_ok
theorem pr_256_257 (i : ℕ) (h1 : 256 ≤ i) (h2 : i < 257) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 256 := by omega
  exact Skel.check_sound boxes all_cov skp256 _ _ skp256_ok
theorem pr_255_257 (i : ℕ) (h1 : 255 ≤ i) (h2 : i < 257) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 256 then pr_255_256 i h1 h else pr_256_257 i (by omega) h2
theorem pr_257_258 (i : ℕ) (h1 : 257 ≤ i) (h2 : i < 258) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 257 := by omega
  exact Skel.check_sound boxes all_cov skp257 _ _ skp257_ok
theorem pr_258_259 (i : ℕ) (h1 : 258 ≤ i) (h2 : i < 259) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 258 := by omega
  exact Skel.check_sound boxes all_cov skp258 _ _ skp258_ok
theorem pr_259_260 (i : ℕ) (h1 : 259 ≤ i) (h2 : i < 260) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 259 := by omega
  exact Skel.check_sound boxes all_cov skp259 _ _ skp259_ok
theorem pr_258_260 (i : ℕ) (h1 : 258 ≤ i) (h2 : i < 260) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 259 then pr_258_259 i h1 h else pr_259_260 i (by omega) h2
theorem pr_257_260 (i : ℕ) (h1 : 257 ≤ i) (h2 : i < 260) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 258 then pr_257_258 i h1 h else pr_258_260 i (by omega) h2
theorem pr_255_260 (i : ℕ) (h1 : 255 ≤ i) (h2 : i < 260) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 257 then pr_255_257 i h1 h else pr_257_260 i (by omega) h2
theorem pr_260_261 (i : ℕ) (h1 : 260 ≤ i) (h2 : i < 261) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 260 := by omega
  exact Skel.check_sound boxes all_cov skp260 _ _ skp260_ok
theorem pr_261_262 (i : ℕ) (h1 : 261 ≤ i) (h2 : i < 262) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 261 := by omega
  exact Skel.check_sound boxes all_cov skp261 _ _ skp261_ok
theorem pr_260_262 (i : ℕ) (h1 : 260 ≤ i) (h2 : i < 262) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 261 then pr_260_261 i h1 h else pr_261_262 i (by omega) h2
theorem pr_262_263 (i : ℕ) (h1 : 262 ≤ i) (h2 : i < 263) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 262 := by omega
  exact Skel.check_sound boxes all_cov skp262 _ _ skp262_ok
theorem pr_263_264 (i : ℕ) (h1 : 263 ≤ i) (h2 : i < 264) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 263 := by omega
  exact Skel.check_sound boxes all_cov skp263 _ _ skp263_ok
theorem pr_264_265 (i : ℕ) (h1 : 264 ≤ i) (h2 : i < 265) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 264 := by omega
  exact Skel.check_sound boxes all_cov skp264 _ _ skp264_ok
theorem pr_263_265 (i : ℕ) (h1 : 263 ≤ i) (h2 : i < 265) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 264 then pr_263_264 i h1 h else pr_264_265 i (by omega) h2
theorem pr_262_265 (i : ℕ) (h1 : 262 ≤ i) (h2 : i < 265) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 263 then pr_262_263 i h1 h else pr_263_265 i (by omega) h2
theorem pr_260_265 (i : ℕ) (h1 : 260 ≤ i) (h2 : i < 265) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 262 then pr_260_262 i h1 h else pr_262_265 i (by omega) h2
theorem pr_255_265 (i : ℕ) (h1 : 255 ≤ i) (h2 : i < 265) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 260 then pr_255_260 i h1 h else pr_260_265 i (by omega) h2
theorem pr_265_266 (i : ℕ) (h1 : 265 ≤ i) (h2 : i < 266) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 265 := by omega
  exact Skel.check_sound boxes all_cov skp265 _ _ skp265_ok
theorem pr_266_267 (i : ℕ) (h1 : 266 ≤ i) (h2 : i < 267) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 266 := by omega
  exact Skel.check_sound boxes all_cov skp266 _ _ skp266_ok
theorem pr_265_267 (i : ℕ) (h1 : 265 ≤ i) (h2 : i < 267) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 266 then pr_265_266 i h1 h else pr_266_267 i (by omega) h2
theorem pr_267_268 (i : ℕ) (h1 : 267 ≤ i) (h2 : i < 268) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 267 := by omega
  exact Skel.check_sound boxes all_cov skp267 _ _ skp267_ok
theorem pr_268_269 (i : ℕ) (h1 : 268 ≤ i) (h2 : i < 269) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 268 := by omega
  exact Skel.check_sound boxes all_cov skp268 _ _ skp268_ok
theorem pr_269_270 (i : ℕ) (h1 : 269 ≤ i) (h2 : i < 270) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 269 := by omega
  exact Skel.check_sound boxes all_cov skp269 _ _ skp269_ok
theorem pr_268_270 (i : ℕ) (h1 : 268 ≤ i) (h2 : i < 270) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 269 then pr_268_269 i h1 h else pr_269_270 i (by omega) h2
theorem pr_267_270 (i : ℕ) (h1 : 267 ≤ i) (h2 : i < 270) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 268 then pr_267_268 i h1 h else pr_268_270 i (by omega) h2
theorem pr_265_270 (i : ℕ) (h1 : 265 ≤ i) (h2 : i < 270) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 267 then pr_265_267 i h1 h else pr_267_270 i (by omega) h2
theorem pr_270_271 (i : ℕ) (h1 : 270 ≤ i) (h2 : i < 271) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 270 := by omega
  exact Skel.check_sound boxes all_cov skp270 _ _ skp270_ok
theorem pr_271_272 (i : ℕ) (h1 : 271 ≤ i) (h2 : i < 272) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 271 := by omega
  exact Skel.check_sound boxes all_cov skp271 _ _ skp271_ok
theorem pr_270_272 (i : ℕ) (h1 : 270 ≤ i) (h2 : i < 272) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 271 then pr_270_271 i h1 h else pr_271_272 i (by omega) h2
theorem pr_272_273 (i : ℕ) (h1 : 272 ≤ i) (h2 : i < 273) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 272 := by omega
  exact Skel.check_sound boxes all_cov skp272 _ _ skp272_ok
theorem pr_273_274 (i : ℕ) (h1 : 273 ≤ i) (h2 : i < 274) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 273 := by omega
  exact Skel.check_sound boxes all_cov skp273 _ _ skp273_ok
theorem pr_274_275 (i : ℕ) (h1 : 274 ≤ i) (h2 : i < 275) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 274 := by omega
  exact Skel.check_sound boxes all_cov skp274 _ _ skp274_ok
theorem pr_273_275 (i : ℕ) (h1 : 273 ≤ i) (h2 : i < 275) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 274 then pr_273_274 i h1 h else pr_274_275 i (by omega) h2
theorem pr_272_275 (i : ℕ) (h1 : 272 ≤ i) (h2 : i < 275) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 273 then pr_272_273 i h1 h else pr_273_275 i (by omega) h2
theorem pr_270_275 (i : ℕ) (h1 : 270 ≤ i) (h2 : i < 275) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 272 then pr_270_272 i h1 h else pr_272_275 i (by omega) h2
theorem pr_265_275 (i : ℕ) (h1 : 265 ≤ i) (h2 : i < 275) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 270 then pr_265_270 i h1 h else pr_270_275 i (by omega) h2
theorem pr_255_275 (i : ℕ) (h1 : 255 ≤ i) (h2 : i < 275) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 265 then pr_255_265 i h1 h else pr_265_275 i (by omega) h2
theorem pr_236_275 (i : ℕ) (h1 : 236 ≤ i) (h2 : i < 275) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 255 then pr_236_255 i h1 h else pr_255_275 i (by omega) h2
theorem pr_275_276 (i : ℕ) (h1 : 275 ≤ i) (h2 : i < 276) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 275 := by omega
  exact Skel.check_sound boxes all_cov skp275 _ _ skp275_ok
theorem pr_276_277 (i : ℕ) (h1 : 276 ≤ i) (h2 : i < 277) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 276 := by omega
  exact Skel.check_sound boxes all_cov skp276 _ _ skp276_ok
theorem pr_275_277 (i : ℕ) (h1 : 275 ≤ i) (h2 : i < 277) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 276 then pr_275_276 i h1 h else pr_276_277 i (by omega) h2
theorem pr_277_278 (i : ℕ) (h1 : 277 ≤ i) (h2 : i < 278) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 277 := by omega
  exact Skel.check_sound boxes all_cov skp277 _ _ skp277_ok
theorem pr_278_279 (i : ℕ) (h1 : 278 ≤ i) (h2 : i < 279) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 278 := by omega
  exact Skel.check_sound boxes all_cov skp278 _ _ skp278_ok
theorem pr_279_280 (i : ℕ) (h1 : 279 ≤ i) (h2 : i < 280) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 279 := by omega
  exact Skel.check_sound boxes all_cov skp279 _ _ skp279_ok
theorem pr_278_280 (i : ℕ) (h1 : 278 ≤ i) (h2 : i < 280) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 279 then pr_278_279 i h1 h else pr_279_280 i (by omega) h2
theorem pr_277_280 (i : ℕ) (h1 : 277 ≤ i) (h2 : i < 280) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 278 then pr_277_278 i h1 h else pr_278_280 i (by omega) h2
theorem pr_275_280 (i : ℕ) (h1 : 275 ≤ i) (h2 : i < 280) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 277 then pr_275_277 i h1 h else pr_277_280 i (by omega) h2
theorem pr_280_281 (i : ℕ) (h1 : 280 ≤ i) (h2 : i < 281) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 280 := by omega
  exact Skel.check_sound boxes all_cov skp280 _ _ skp280_ok
theorem pr_281_282 (i : ℕ) (h1 : 281 ≤ i) (h2 : i < 282) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 281 := by omega
  exact Skel.check_sound boxes all_cov skp281 _ _ skp281_ok
theorem pr_280_282 (i : ℕ) (h1 : 280 ≤ i) (h2 : i < 282) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 281 then pr_280_281 i h1 h else pr_281_282 i (by omega) h2
theorem pr_282_283 (i : ℕ) (h1 : 282 ≤ i) (h2 : i < 283) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 282 := by omega
  exact Skel.check_sound boxes all_cov skp282 _ _ skp282_ok
theorem pr_283_284 (i : ℕ) (h1 : 283 ≤ i) (h2 : i < 284) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 283 := by omega
  exact Skel.check_sound boxes all_cov skp283 _ _ skp283_ok
theorem pr_284_285 (i : ℕ) (h1 : 284 ≤ i) (h2 : i < 285) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 284 := by omega
  exact Skel.check_sound boxes all_cov skp284 _ _ skp284_ok
theorem pr_283_285 (i : ℕ) (h1 : 283 ≤ i) (h2 : i < 285) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 284 then pr_283_284 i h1 h else pr_284_285 i (by omega) h2
theorem pr_282_285 (i : ℕ) (h1 : 282 ≤ i) (h2 : i < 285) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 283 then pr_282_283 i h1 h else pr_283_285 i (by omega) h2
theorem pr_280_285 (i : ℕ) (h1 : 280 ≤ i) (h2 : i < 285) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 282 then pr_280_282 i h1 h else pr_282_285 i (by omega) h2
theorem pr_275_285 (i : ℕ) (h1 : 275 ≤ i) (h2 : i < 285) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 280 then pr_275_280 i h1 h else pr_280_285 i (by omega) h2
theorem pr_285_286 (i : ℕ) (h1 : 285 ≤ i) (h2 : i < 286) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 285 := by omega
  exact Skel.check_sound boxes all_cov skp285 _ _ skp285_ok
theorem pr_286_287 (i : ℕ) (h1 : 286 ≤ i) (h2 : i < 287) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 286 := by omega
  exact Skel.check_sound boxes all_cov skp286 _ _ skp286_ok
theorem pr_285_287 (i : ℕ) (h1 : 285 ≤ i) (h2 : i < 287) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 286 then pr_285_286 i h1 h else pr_286_287 i (by omega) h2
theorem pr_287_288 (i : ℕ) (h1 : 287 ≤ i) (h2 : i < 288) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 287 := by omega
  exact Skel.check_sound boxes all_cov skp287 _ _ skp287_ok
theorem pr_288_289 (i : ℕ) (h1 : 288 ≤ i) (h2 : i < 289) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 288 := by omega
  exact Skel.check_sound boxes all_cov skp288 _ _ skp288_ok
theorem pr_289_290 (i : ℕ) (h1 : 289 ≤ i) (h2 : i < 290) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 289 := by omega
  exact Skel.check_sound boxes all_cov skp289 _ _ skp289_ok
theorem pr_288_290 (i : ℕ) (h1 : 288 ≤ i) (h2 : i < 290) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 289 then pr_288_289 i h1 h else pr_289_290 i (by omega) h2
theorem pr_287_290 (i : ℕ) (h1 : 287 ≤ i) (h2 : i < 290) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 288 then pr_287_288 i h1 h else pr_288_290 i (by omega) h2
theorem pr_285_290 (i : ℕ) (h1 : 285 ≤ i) (h2 : i < 290) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 287 then pr_285_287 i h1 h else pr_287_290 i (by omega) h2
theorem pr_290_291 (i : ℕ) (h1 : 290 ≤ i) (h2 : i < 291) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 290 := by omega
  exact Skel.check_sound boxes all_cov skp290 _ _ skp290_ok
theorem pr_291_292 (i : ℕ) (h1 : 291 ≤ i) (h2 : i < 292) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 291 := by omega
  exact Skel.check_sound boxes all_cov skp291 _ _ skp291_ok
theorem pr_290_292 (i : ℕ) (h1 : 290 ≤ i) (h2 : i < 292) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 291 then pr_290_291 i h1 h else pr_291_292 i (by omega) h2
theorem pr_292_293 (i : ℕ) (h1 : 292 ≤ i) (h2 : i < 293) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 292 := by omega
  exact Skel.check_sound boxes all_cov skp292 _ _ skp292_ok
theorem pr_293_294 (i : ℕ) (h1 : 293 ≤ i) (h2 : i < 294) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 293 := by omega
  exact Skel.check_sound boxes all_cov skp293 _ _ skp293_ok
theorem pr_294_295 (i : ℕ) (h1 : 294 ≤ i) (h2 : i < 295) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 294 := by omega
  exact Skel.check_sound boxes all_cov skp294 _ _ skp294_ok
theorem pr_293_295 (i : ℕ) (h1 : 293 ≤ i) (h2 : i < 295) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 294 then pr_293_294 i h1 h else pr_294_295 i (by omega) h2
theorem pr_292_295 (i : ℕ) (h1 : 292 ≤ i) (h2 : i < 295) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 293 then pr_292_293 i h1 h else pr_293_295 i (by omega) h2
theorem pr_290_295 (i : ℕ) (h1 : 290 ≤ i) (h2 : i < 295) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 292 then pr_290_292 i h1 h else pr_292_295 i (by omega) h2
theorem pr_285_295 (i : ℕ) (h1 : 285 ≤ i) (h2 : i < 295) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 290 then pr_285_290 i h1 h else pr_290_295 i (by omega) h2
theorem pr_275_295 (i : ℕ) (h1 : 275 ≤ i) (h2 : i < 295) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 285 then pr_275_285 i h1 h else pr_285_295 i (by omega) h2
theorem pr_295_296 (i : ℕ) (h1 : 295 ≤ i) (h2 : i < 296) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 295 := by omega
  exact Skel.check_sound boxes all_cov skp295 _ _ skp295_ok
theorem pr_296_297 (i : ℕ) (h1 : 296 ≤ i) (h2 : i < 297) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 296 := by omega
  exact Skel.check_sound boxes all_cov skp296 _ _ skp296_ok
theorem pr_295_297 (i : ℕ) (h1 : 295 ≤ i) (h2 : i < 297) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 296 then pr_295_296 i h1 h else pr_296_297 i (by omega) h2
theorem pr_297_298 (i : ℕ) (h1 : 297 ≤ i) (h2 : i < 298) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 297 := by omega
  exact Skel.check_sound boxes all_cov skp297 _ _ skp297_ok
theorem pr_298_299 (i : ℕ) (h1 : 298 ≤ i) (h2 : i < 299) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 298 := by omega
  exact Skel.check_sound boxes all_cov skp298 _ _ skp298_ok
theorem pr_299_300 (i : ℕ) (h1 : 299 ≤ i) (h2 : i < 300) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 299 := by omega
  exact Skel.check_sound boxes all_cov skp299 _ _ skp299_ok
theorem pr_298_300 (i : ℕ) (h1 : 298 ≤ i) (h2 : i < 300) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 299 then pr_298_299 i h1 h else pr_299_300 i (by omega) h2
theorem pr_297_300 (i : ℕ) (h1 : 297 ≤ i) (h2 : i < 300) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 298 then pr_297_298 i h1 h else pr_298_300 i (by omega) h2
theorem pr_295_300 (i : ℕ) (h1 : 295 ≤ i) (h2 : i < 300) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 297 then pr_295_297 i h1 h else pr_297_300 i (by omega) h2
theorem pr_300_301 (i : ℕ) (h1 : 300 ≤ i) (h2 : i < 301) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 300 := by omega
  exact Skel.check_sound boxes all_cov skp300 _ _ skp300_ok
theorem pr_301_302 (i : ℕ) (h1 : 301 ≤ i) (h2 : i < 302) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 301 := by omega
  exact Skel.check_sound boxes all_cov skp301 _ _ skp301_ok
theorem pr_300_302 (i : ℕ) (h1 : 300 ≤ i) (h2 : i < 302) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 301 then pr_300_301 i h1 h else pr_301_302 i (by omega) h2
theorem pr_302_303 (i : ℕ) (h1 : 302 ≤ i) (h2 : i < 303) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 302 := by omega
  exact Skel.check_sound boxes all_cov skp302 _ _ skp302_ok
theorem pr_303_304 (i : ℕ) (h1 : 303 ≤ i) (h2 : i < 304) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 303 := by omega
  exact Skel.check_sound boxes all_cov skp303 _ _ skp303_ok
theorem pr_304_305 (i : ℕ) (h1 : 304 ≤ i) (h2 : i < 305) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 304 := by omega
  exact Skel.check_sound boxes all_cov skp304 _ _ skp304_ok
theorem pr_303_305 (i : ℕ) (h1 : 303 ≤ i) (h2 : i < 305) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 304 then pr_303_304 i h1 h else pr_304_305 i (by omega) h2
theorem pr_302_305 (i : ℕ) (h1 : 302 ≤ i) (h2 : i < 305) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 303 then pr_302_303 i h1 h else pr_303_305 i (by omega) h2
theorem pr_300_305 (i : ℕ) (h1 : 300 ≤ i) (h2 : i < 305) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 302 then pr_300_302 i h1 h else pr_302_305 i (by omega) h2
theorem pr_295_305 (i : ℕ) (h1 : 295 ≤ i) (h2 : i < 305) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 300 then pr_295_300 i h1 h else pr_300_305 i (by omega) h2
theorem pr_305_306 (i : ℕ) (h1 : 305 ≤ i) (h2 : i < 306) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 305 := by omega
  exact Skel.check_sound boxes all_cov skp305 _ _ skp305_ok
theorem pr_306_307 (i : ℕ) (h1 : 306 ≤ i) (h2 : i < 307) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 306 := by omega
  exact Skel.check_sound boxes all_cov skp306 _ _ skp306_ok
theorem pr_305_307 (i : ℕ) (h1 : 305 ≤ i) (h2 : i < 307) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 306 then pr_305_306 i h1 h else pr_306_307 i (by omega) h2
theorem pr_307_308 (i : ℕ) (h1 : 307 ≤ i) (h2 : i < 308) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 307 := by omega
  exact Skel.check_sound boxes all_cov skp307 _ _ skp307_ok
theorem pr_308_309 (i : ℕ) (h1 : 308 ≤ i) (h2 : i < 309) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 308 := by omega
  exact Skel.check_sound boxes all_cov skp308 _ _ skp308_ok
theorem pr_309_310 (i : ℕ) (h1 : 309 ≤ i) (h2 : i < 310) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 309 := by omega
  exact Skel.check_sound boxes all_cov skp309 _ _ skp309_ok
theorem pr_308_310 (i : ℕ) (h1 : 308 ≤ i) (h2 : i < 310) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 309 then pr_308_309 i h1 h else pr_309_310 i (by omega) h2
theorem pr_307_310 (i : ℕ) (h1 : 307 ≤ i) (h2 : i < 310) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 308 then pr_307_308 i h1 h else pr_308_310 i (by omega) h2
theorem pr_305_310 (i : ℕ) (h1 : 305 ≤ i) (h2 : i < 310) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 307 then pr_305_307 i h1 h else pr_307_310 i (by omega) h2
theorem pr_310_311 (i : ℕ) (h1 : 310 ≤ i) (h2 : i < 311) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 310 := by omega
  exact Skel.check_sound boxes all_cov skp310 _ _ skp310_ok
theorem pr_311_312 (i : ℕ) (h1 : 311 ≤ i) (h2 : i < 312) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 311 := by omega
  exact Skel.check_sound boxes all_cov skp311 _ _ skp311_ok
theorem pr_310_312 (i : ℕ) (h1 : 310 ≤ i) (h2 : i < 312) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 311 then pr_310_311 i h1 h else pr_311_312 i (by omega) h2
theorem pr_312_313 (i : ℕ) (h1 : 312 ≤ i) (h2 : i < 313) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 312 := by omega
  exact Skel.check_sound boxes all_cov skp312 _ _ skp312_ok
theorem pr_313_314 (i : ℕ) (h1 : 313 ≤ i) (h2 : i < 314) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 313 := by omega
  exact Skel.check_sound boxes all_cov skp313 _ _ skp313_ok
theorem pr_314_315 (i : ℕ) (h1 : 314 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 := by
  obtain rfl : i = 314 := by omega
  exact Skel.check_sound boxes all_cov skp314 _ _ skp314_ok
theorem pr_313_315 (i : ℕ) (h1 : 313 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 314 then pr_313_314 i h1 h else pr_314_315 i (by omega) h2
theorem pr_312_315 (i : ℕ) (h1 : 312 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 313 then pr_312_313 i h1 h else pr_313_315 i (by omega) h2
theorem pr_310_315 (i : ℕ) (h1 : 310 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 312 then pr_310_312 i h1 h else pr_312_315 i (by omega) h2
theorem pr_305_315 (i : ℕ) (h1 : 305 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 310 then pr_305_310 i h1 h else pr_310_315 i (by omega) h2
theorem pr_295_315 (i : ℕ) (h1 : 295 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 305 then pr_295_305 i h1 h else pr_305_315 i (by omega) h2
theorem pr_275_315 (i : ℕ) (h1 : 275 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 295 then pr_275_295 i h1 h else pr_295_315 i (by omega) h2
theorem pr_236_315 (i : ℕ) (h1 : 236 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 275 then pr_236_275 i h1 h else pr_275_315 i (by omega) h2
theorem pr_157_315 (i : ℕ) (h1 : 157 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 236 then pr_157_236 i h1 h else pr_236_315 i (by omega) h2
theorem pr_0_315 (i : ℕ) (h1 : 0 ≤ i) (h2 : i < 315) : Covered (topBoxes i).1 (topBoxes i).2 :=
  if h : i < 157 then pr_0_157 i h1 h else pr_157_315 i (by omega) h2

theorem all_top (i : ℕ) : Covered (topBoxes i).1 (topBoxes i).2 := by
  by_cases hi : i < 315
  · exact pr_0_315 i (Nat.zero_le _) hi
  · have : topBoxes i = (fun _ => 1, fun _ => 0) := by
      unfold topBoxes; rw [List.getD_eq_default]; rw [topBoxList_length]; omega
    rw [this]; exact covered_empty _ _ 0 (by norm_num)

/-- **The global step.** -/
theorem global_step (x : Fin 7 → ℝ) (h : Hyps x) : Goal x :=
  Skel.check_sound topBoxes all_top skelTop rootLo rootHi skelTop_ok x h.box h

end Harris
