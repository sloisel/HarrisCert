module

public import HarrisCert.Kernel
public import HarrisCert.Leaves.L0
public import HarrisCert.Leaves.L1
public import HarrisCert.Leaves.L2
public import HarrisCert.Leaves.L3
public import HarrisCert.Leaves.L4
public import HarrisCert.Leaves.L5
public import HarrisCert.Leaves.L6
public import HarrisCert.Leaves.L7
public import HarrisCert.Leaves.L8
public import HarrisCert.Leaves.L9
public import HarrisCert.Leaves.L10

/-! Leaves 0 … 655 cover their boxes. -/

@[expose] public section

namespace Harris

theorem cr_0_1 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 1) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 0 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf0_ok
theorem cr_1_2 (k : ℕ) (h1 : 1 ≤ k) (h2 : k < 2) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1_ok
theorem cr_0_2 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 2) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1 then cr_0_1 k h1 h else cr_1_2 k (by omega) h2
theorem cr_2_3 (k : ℕ) (h1 : 2 ≤ k) (h2 : k < 3) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2_ok
theorem cr_3_4 (k : ℕ) (h1 : 3 ≤ k) (h2 : k < 4) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 3 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf3_ok
theorem cr_4_5 (k : ℕ) (h1 : 4 ≤ k) (h2 : k < 5) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 4 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf4_ok
theorem cr_3_5 (k : ℕ) (h1 : 3 ≤ k) (h2 : k < 5) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 4 then cr_3_4 k h1 h else cr_4_5 k (by omega) h2
theorem cr_2_5 (k : ℕ) (h1 : 2 ≤ k) (h2 : k < 5) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 3 then cr_2_3 k h1 h else cr_3_5 k (by omega) h2
theorem cr_0_5 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 5) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2 then cr_0_2 k h1 h else cr_2_5 k (by omega) h2
theorem cr_5_6 (k : ℕ) (h1 : 5 ≤ k) (h2 : k < 6) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 5 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf5_ok
theorem cr_6_7 (k : ℕ) (h1 : 6 ≤ k) (h2 : k < 7) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 6 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf6_ok
theorem cr_5_7 (k : ℕ) (h1 : 5 ≤ k) (h2 : k < 7) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 6 then cr_5_6 k h1 h else cr_6_7 k (by omega) h2
theorem cr_7_8 (k : ℕ) (h1 : 7 ≤ k) (h2 : k < 8) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 7 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf7_ok
theorem cr_8_9 (k : ℕ) (h1 : 8 ≤ k) (h2 : k < 9) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 8 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf8_ok
theorem cr_9_10 (k : ℕ) (h1 : 9 ≤ k) (h2 : k < 10) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 9 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf9_ok
theorem cr_8_10 (k : ℕ) (h1 : 8 ≤ k) (h2 : k < 10) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 9 then cr_8_9 k h1 h else cr_9_10 k (by omega) h2
theorem cr_7_10 (k : ℕ) (h1 : 7 ≤ k) (h2 : k < 10) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 8 then cr_7_8 k h1 h else cr_8_10 k (by omega) h2
theorem cr_5_10 (k : ℕ) (h1 : 5 ≤ k) (h2 : k < 10) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 7 then cr_5_7 k h1 h else cr_7_10 k (by omega) h2
theorem cr_0_10 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 10) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 5 then cr_0_5 k h1 h else cr_5_10 k (by omega) h2
theorem cr_10_11 (k : ℕ) (h1 : 10 ≤ k) (h2 : k < 11) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 10 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf10_ok
theorem cr_11_12 (k : ℕ) (h1 : 11 ≤ k) (h2 : k < 12) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 11 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf11_ok
theorem cr_10_12 (k : ℕ) (h1 : 10 ≤ k) (h2 : k < 12) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 11 then cr_10_11 k h1 h else cr_11_12 k (by omega) h2
theorem cr_12_13 (k : ℕ) (h1 : 12 ≤ k) (h2 : k < 13) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 12 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf12_ok
theorem cr_13_14 (k : ℕ) (h1 : 13 ≤ k) (h2 : k < 14) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 13 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf13_ok
theorem cr_14_15 (k : ℕ) (h1 : 14 ≤ k) (h2 : k < 15) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 14 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf14_ok
theorem cr_13_15 (k : ℕ) (h1 : 13 ≤ k) (h2 : k < 15) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 14 then cr_13_14 k h1 h else cr_14_15 k (by omega) h2
theorem cr_12_15 (k : ℕ) (h1 : 12 ≤ k) (h2 : k < 15) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 13 then cr_12_13 k h1 h else cr_13_15 k (by omega) h2
theorem cr_10_15 (k : ℕ) (h1 : 10 ≤ k) (h2 : k < 15) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 12 then cr_10_12 k h1 h else cr_12_15 k (by omega) h2
theorem cr_15_16 (k : ℕ) (h1 : 15 ≤ k) (h2 : k < 16) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 15 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf15_ok
theorem cr_16_17 (k : ℕ) (h1 : 16 ≤ k) (h2 : k < 17) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 16 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf16_ok
theorem cr_15_17 (k : ℕ) (h1 : 15 ≤ k) (h2 : k < 17) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 16 then cr_15_16 k h1 h else cr_16_17 k (by omega) h2
theorem cr_17_18 (k : ℕ) (h1 : 17 ≤ k) (h2 : k < 18) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 17 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf17_ok
theorem cr_18_19 (k : ℕ) (h1 : 18 ≤ k) (h2 : k < 19) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 18 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf18_ok
theorem cr_19_20 (k : ℕ) (h1 : 19 ≤ k) (h2 : k < 20) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 19 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf19_ok
theorem cr_18_20 (k : ℕ) (h1 : 18 ≤ k) (h2 : k < 20) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 19 then cr_18_19 k h1 h else cr_19_20 k (by omega) h2
theorem cr_17_20 (k : ℕ) (h1 : 17 ≤ k) (h2 : k < 20) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 18 then cr_17_18 k h1 h else cr_18_20 k (by omega) h2
theorem cr_15_20 (k : ℕ) (h1 : 15 ≤ k) (h2 : k < 20) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 17 then cr_15_17 k h1 h else cr_17_20 k (by omega) h2
theorem cr_10_20 (k : ℕ) (h1 : 10 ≤ k) (h2 : k < 20) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 15 then cr_10_15 k h1 h else cr_15_20 k (by omega) h2
theorem cr_0_20 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 20) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 10 then cr_0_10 k h1 h else cr_10_20 k (by omega) h2
theorem cr_20_21 (k : ℕ) (h1 : 20 ≤ k) (h2 : k < 21) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 20 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf20_ok
theorem cr_21_22 (k : ℕ) (h1 : 21 ≤ k) (h2 : k < 22) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 21 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf21_ok
theorem cr_20_22 (k : ℕ) (h1 : 20 ≤ k) (h2 : k < 22) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 21 then cr_20_21 k h1 h else cr_21_22 k (by omega) h2
theorem cr_22_23 (k : ℕ) (h1 : 22 ≤ k) (h2 : k < 23) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 22 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf22_ok
theorem cr_23_24 (k : ℕ) (h1 : 23 ≤ k) (h2 : k < 24) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 23 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf23_ok
theorem cr_24_25 (k : ℕ) (h1 : 24 ≤ k) (h2 : k < 25) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 24 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf24_ok
theorem cr_23_25 (k : ℕ) (h1 : 23 ≤ k) (h2 : k < 25) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 24 then cr_23_24 k h1 h else cr_24_25 k (by omega) h2
theorem cr_22_25 (k : ℕ) (h1 : 22 ≤ k) (h2 : k < 25) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 23 then cr_22_23 k h1 h else cr_23_25 k (by omega) h2
theorem cr_20_25 (k : ℕ) (h1 : 20 ≤ k) (h2 : k < 25) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 22 then cr_20_22 k h1 h else cr_22_25 k (by omega) h2
theorem cr_25_26 (k : ℕ) (h1 : 25 ≤ k) (h2 : k < 26) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 25 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf25_ok
theorem cr_26_27 (k : ℕ) (h1 : 26 ≤ k) (h2 : k < 27) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 26 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf26_ok
theorem cr_25_27 (k : ℕ) (h1 : 25 ≤ k) (h2 : k < 27) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 26 then cr_25_26 k h1 h else cr_26_27 k (by omega) h2
theorem cr_27_28 (k : ℕ) (h1 : 27 ≤ k) (h2 : k < 28) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 27 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf27_ok
theorem cr_28_29 (k : ℕ) (h1 : 28 ≤ k) (h2 : k < 29) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 28 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf28_ok
theorem cr_29_30 (k : ℕ) (h1 : 29 ≤ k) (h2 : k < 30) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 29 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf29_ok
theorem cr_28_30 (k : ℕ) (h1 : 28 ≤ k) (h2 : k < 30) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 29 then cr_28_29 k h1 h else cr_29_30 k (by omega) h2
theorem cr_27_30 (k : ℕ) (h1 : 27 ≤ k) (h2 : k < 30) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 28 then cr_27_28 k h1 h else cr_28_30 k (by omega) h2
theorem cr_25_30 (k : ℕ) (h1 : 25 ≤ k) (h2 : k < 30) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 27 then cr_25_27 k h1 h else cr_27_30 k (by omega) h2
theorem cr_20_30 (k : ℕ) (h1 : 20 ≤ k) (h2 : k < 30) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 25 then cr_20_25 k h1 h else cr_25_30 k (by omega) h2
theorem cr_30_31 (k : ℕ) (h1 : 30 ≤ k) (h2 : k < 31) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 30 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf30_ok
theorem cr_31_32 (k : ℕ) (h1 : 31 ≤ k) (h2 : k < 32) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 31 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf31_ok
theorem cr_30_32 (k : ℕ) (h1 : 30 ≤ k) (h2 : k < 32) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 31 then cr_30_31 k h1 h else cr_31_32 k (by omega) h2
theorem cr_32_33 (k : ℕ) (h1 : 32 ≤ k) (h2 : k < 33) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 32 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf32_ok
theorem cr_33_34 (k : ℕ) (h1 : 33 ≤ k) (h2 : k < 34) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 33 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf33_ok
theorem cr_34_35 (k : ℕ) (h1 : 34 ≤ k) (h2 : k < 35) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 34 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf34_ok
theorem cr_33_35 (k : ℕ) (h1 : 33 ≤ k) (h2 : k < 35) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 34 then cr_33_34 k h1 h else cr_34_35 k (by omega) h2
theorem cr_32_35 (k : ℕ) (h1 : 32 ≤ k) (h2 : k < 35) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 33 then cr_32_33 k h1 h else cr_33_35 k (by omega) h2
theorem cr_30_35 (k : ℕ) (h1 : 30 ≤ k) (h2 : k < 35) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 32 then cr_30_32 k h1 h else cr_32_35 k (by omega) h2
theorem cr_35_36 (k : ℕ) (h1 : 35 ≤ k) (h2 : k < 36) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 35 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf35_ok
theorem cr_36_37 (k : ℕ) (h1 : 36 ≤ k) (h2 : k < 37) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 36 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf36_ok
theorem cr_37_38 (k : ℕ) (h1 : 37 ≤ k) (h2 : k < 38) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 37 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf37_ok
theorem cr_36_38 (k : ℕ) (h1 : 36 ≤ k) (h2 : k < 38) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 37 then cr_36_37 k h1 h else cr_37_38 k (by omega) h2
theorem cr_35_38 (k : ℕ) (h1 : 35 ≤ k) (h2 : k < 38) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 36 then cr_35_36 k h1 h else cr_36_38 k (by omega) h2
theorem cr_38_39 (k : ℕ) (h1 : 38 ≤ k) (h2 : k < 39) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 38 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf38_ok
theorem cr_39_40 (k : ℕ) (h1 : 39 ≤ k) (h2 : k < 40) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 39 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf39_ok
theorem cr_40_41 (k : ℕ) (h1 : 40 ≤ k) (h2 : k < 41) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 40 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf40_ok
theorem cr_39_41 (k : ℕ) (h1 : 39 ≤ k) (h2 : k < 41) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 40 then cr_39_40 k h1 h else cr_40_41 k (by omega) h2
theorem cr_38_41 (k : ℕ) (h1 : 38 ≤ k) (h2 : k < 41) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 39 then cr_38_39 k h1 h else cr_39_41 k (by omega) h2
theorem cr_35_41 (k : ℕ) (h1 : 35 ≤ k) (h2 : k < 41) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 38 then cr_35_38 k h1 h else cr_38_41 k (by omega) h2
theorem cr_30_41 (k : ℕ) (h1 : 30 ≤ k) (h2 : k < 41) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 35 then cr_30_35 k h1 h else cr_35_41 k (by omega) h2
theorem cr_20_41 (k : ℕ) (h1 : 20 ≤ k) (h2 : k < 41) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 30 then cr_20_30 k h1 h else cr_30_41 k (by omega) h2
theorem cr_0_41 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 41) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 20 then cr_0_20 k h1 h else cr_20_41 k (by omega) h2
theorem cr_41_42 (k : ℕ) (h1 : 41 ≤ k) (h2 : k < 42) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 41 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf41_ok
theorem cr_42_43 (k : ℕ) (h1 : 42 ≤ k) (h2 : k < 43) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 42 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf42_ok
theorem cr_41_43 (k : ℕ) (h1 : 41 ≤ k) (h2 : k < 43) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 42 then cr_41_42 k h1 h else cr_42_43 k (by omega) h2
theorem cr_43_44 (k : ℕ) (h1 : 43 ≤ k) (h2 : k < 44) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 43 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf43_ok
theorem cr_44_45 (k : ℕ) (h1 : 44 ≤ k) (h2 : k < 45) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 44 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf44_ok
theorem cr_45_46 (k : ℕ) (h1 : 45 ≤ k) (h2 : k < 46) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 45 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf45_ok
theorem cr_44_46 (k : ℕ) (h1 : 44 ≤ k) (h2 : k < 46) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 45 then cr_44_45 k h1 h else cr_45_46 k (by omega) h2
theorem cr_43_46 (k : ℕ) (h1 : 43 ≤ k) (h2 : k < 46) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 44 then cr_43_44 k h1 h else cr_44_46 k (by omega) h2
theorem cr_41_46 (k : ℕ) (h1 : 41 ≤ k) (h2 : k < 46) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 43 then cr_41_43 k h1 h else cr_43_46 k (by omega) h2
theorem cr_46_47 (k : ℕ) (h1 : 46 ≤ k) (h2 : k < 47) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 46 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf46_ok
theorem cr_47_48 (k : ℕ) (h1 : 47 ≤ k) (h2 : k < 48) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 47 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf47_ok
theorem cr_46_48 (k : ℕ) (h1 : 46 ≤ k) (h2 : k < 48) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 47 then cr_46_47 k h1 h else cr_47_48 k (by omega) h2
theorem cr_48_49 (k : ℕ) (h1 : 48 ≤ k) (h2 : k < 49) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 48 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf48_ok
theorem cr_49_50 (k : ℕ) (h1 : 49 ≤ k) (h2 : k < 50) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 49 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf49_ok
theorem cr_50_51 (k : ℕ) (h1 : 50 ≤ k) (h2 : k < 51) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 50 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf50_ok
theorem cr_49_51 (k : ℕ) (h1 : 49 ≤ k) (h2 : k < 51) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 50 then cr_49_50 k h1 h else cr_50_51 k (by omega) h2
theorem cr_48_51 (k : ℕ) (h1 : 48 ≤ k) (h2 : k < 51) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 49 then cr_48_49 k h1 h else cr_49_51 k (by omega) h2
theorem cr_46_51 (k : ℕ) (h1 : 46 ≤ k) (h2 : k < 51) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 48 then cr_46_48 k h1 h else cr_48_51 k (by omega) h2
theorem cr_41_51 (k : ℕ) (h1 : 41 ≤ k) (h2 : k < 51) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 46 then cr_41_46 k h1 h else cr_46_51 k (by omega) h2
theorem cr_51_52 (k : ℕ) (h1 : 51 ≤ k) (h2 : k < 52) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 51 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf51_ok
theorem cr_52_53 (k : ℕ) (h1 : 52 ≤ k) (h2 : k < 53) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 52 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf52_ok
theorem cr_51_53 (k : ℕ) (h1 : 51 ≤ k) (h2 : k < 53) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 52 then cr_51_52 k h1 h else cr_52_53 k (by omega) h2
theorem cr_53_54 (k : ℕ) (h1 : 53 ≤ k) (h2 : k < 54) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 53 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf53_ok
theorem cr_54_55 (k : ℕ) (h1 : 54 ≤ k) (h2 : k < 55) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 54 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf54_ok
theorem cr_55_56 (k : ℕ) (h1 : 55 ≤ k) (h2 : k < 56) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 55 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf55_ok
theorem cr_54_56 (k : ℕ) (h1 : 54 ≤ k) (h2 : k < 56) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 55 then cr_54_55 k h1 h else cr_55_56 k (by omega) h2
theorem cr_53_56 (k : ℕ) (h1 : 53 ≤ k) (h2 : k < 56) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 54 then cr_53_54 k h1 h else cr_54_56 k (by omega) h2
theorem cr_51_56 (k : ℕ) (h1 : 51 ≤ k) (h2 : k < 56) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 53 then cr_51_53 k h1 h else cr_53_56 k (by omega) h2
theorem cr_56_57 (k : ℕ) (h1 : 56 ≤ k) (h2 : k < 57) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 56 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf56_ok
theorem cr_57_58 (k : ℕ) (h1 : 57 ≤ k) (h2 : k < 58) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 57 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf57_ok
theorem cr_56_58 (k : ℕ) (h1 : 56 ≤ k) (h2 : k < 58) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 57 then cr_56_57 k h1 h else cr_57_58 k (by omega) h2
theorem cr_58_59 (k : ℕ) (h1 : 58 ≤ k) (h2 : k < 59) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 58 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf58_ok
theorem cr_59_60 (k : ℕ) (h1 : 59 ≤ k) (h2 : k < 60) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 59 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf59_ok
theorem cr_60_61 (k : ℕ) (h1 : 60 ≤ k) (h2 : k < 61) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 60 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf60_ok
theorem cr_59_61 (k : ℕ) (h1 : 59 ≤ k) (h2 : k < 61) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 60 then cr_59_60 k h1 h else cr_60_61 k (by omega) h2
theorem cr_58_61 (k : ℕ) (h1 : 58 ≤ k) (h2 : k < 61) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 59 then cr_58_59 k h1 h else cr_59_61 k (by omega) h2
theorem cr_56_61 (k : ℕ) (h1 : 56 ≤ k) (h2 : k < 61) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 58 then cr_56_58 k h1 h else cr_58_61 k (by omega) h2
theorem cr_51_61 (k : ℕ) (h1 : 51 ≤ k) (h2 : k < 61) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 56 then cr_51_56 k h1 h else cr_56_61 k (by omega) h2
theorem cr_41_61 (k : ℕ) (h1 : 41 ≤ k) (h2 : k < 61) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 51 then cr_41_51 k h1 h else cr_51_61 k (by omega) h2
theorem cr_61_62 (k : ℕ) (h1 : 61 ≤ k) (h2 : k < 62) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 61 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf61_ok
theorem cr_62_63 (k : ℕ) (h1 : 62 ≤ k) (h2 : k < 63) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 62 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf62_ok
theorem cr_61_63 (k : ℕ) (h1 : 61 ≤ k) (h2 : k < 63) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 62 then cr_61_62 k h1 h else cr_62_63 k (by omega) h2
theorem cr_63_64 (k : ℕ) (h1 : 63 ≤ k) (h2 : k < 64) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 63 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf63_ok
theorem cr_64_65 (k : ℕ) (h1 : 64 ≤ k) (h2 : k < 65) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 64 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf64_ok
theorem cr_65_66 (k : ℕ) (h1 : 65 ≤ k) (h2 : k < 66) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 65 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf65_ok
theorem cr_64_66 (k : ℕ) (h1 : 64 ≤ k) (h2 : k < 66) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 65 then cr_64_65 k h1 h else cr_65_66 k (by omega) h2
theorem cr_63_66 (k : ℕ) (h1 : 63 ≤ k) (h2 : k < 66) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 64 then cr_63_64 k h1 h else cr_64_66 k (by omega) h2
theorem cr_61_66 (k : ℕ) (h1 : 61 ≤ k) (h2 : k < 66) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 63 then cr_61_63 k h1 h else cr_63_66 k (by omega) h2
theorem cr_66_67 (k : ℕ) (h1 : 66 ≤ k) (h2 : k < 67) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 66 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf66_ok
theorem cr_67_68 (k : ℕ) (h1 : 67 ≤ k) (h2 : k < 68) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 67 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf67_ok
theorem cr_66_68 (k : ℕ) (h1 : 66 ≤ k) (h2 : k < 68) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 67 then cr_66_67 k h1 h else cr_67_68 k (by omega) h2
theorem cr_68_69 (k : ℕ) (h1 : 68 ≤ k) (h2 : k < 69) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 68 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf68_ok
theorem cr_69_70 (k : ℕ) (h1 : 69 ≤ k) (h2 : k < 70) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 69 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf69_ok
theorem cr_70_71 (k : ℕ) (h1 : 70 ≤ k) (h2 : k < 71) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 70 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf70_ok
theorem cr_69_71 (k : ℕ) (h1 : 69 ≤ k) (h2 : k < 71) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 70 then cr_69_70 k h1 h else cr_70_71 k (by omega) h2
theorem cr_68_71 (k : ℕ) (h1 : 68 ≤ k) (h2 : k < 71) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 69 then cr_68_69 k h1 h else cr_69_71 k (by omega) h2
theorem cr_66_71 (k : ℕ) (h1 : 66 ≤ k) (h2 : k < 71) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 68 then cr_66_68 k h1 h else cr_68_71 k (by omega) h2
theorem cr_61_71 (k : ℕ) (h1 : 61 ≤ k) (h2 : k < 71) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 66 then cr_61_66 k h1 h else cr_66_71 k (by omega) h2
theorem cr_71_72 (k : ℕ) (h1 : 71 ≤ k) (h2 : k < 72) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 71 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf71_ok
theorem cr_72_73 (k : ℕ) (h1 : 72 ≤ k) (h2 : k < 73) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 72 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf72_ok
theorem cr_71_73 (k : ℕ) (h1 : 71 ≤ k) (h2 : k < 73) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 72 then cr_71_72 k h1 h else cr_72_73 k (by omega) h2
theorem cr_73_74 (k : ℕ) (h1 : 73 ≤ k) (h2 : k < 74) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 73 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf73_ok
theorem cr_74_75 (k : ℕ) (h1 : 74 ≤ k) (h2 : k < 75) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 74 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf74_ok
theorem cr_75_76 (k : ℕ) (h1 : 75 ≤ k) (h2 : k < 76) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 75 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf75_ok
theorem cr_74_76 (k : ℕ) (h1 : 74 ≤ k) (h2 : k < 76) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 75 then cr_74_75 k h1 h else cr_75_76 k (by omega) h2
theorem cr_73_76 (k : ℕ) (h1 : 73 ≤ k) (h2 : k < 76) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 74 then cr_73_74 k h1 h else cr_74_76 k (by omega) h2
theorem cr_71_76 (k : ℕ) (h1 : 71 ≤ k) (h2 : k < 76) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 73 then cr_71_73 k h1 h else cr_73_76 k (by omega) h2
theorem cr_76_77 (k : ℕ) (h1 : 76 ≤ k) (h2 : k < 77) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 76 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf76_ok
theorem cr_77_78 (k : ℕ) (h1 : 77 ≤ k) (h2 : k < 78) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 77 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf77_ok
theorem cr_78_79 (k : ℕ) (h1 : 78 ≤ k) (h2 : k < 79) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 78 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf78_ok
theorem cr_77_79 (k : ℕ) (h1 : 77 ≤ k) (h2 : k < 79) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 78 then cr_77_78 k h1 h else cr_78_79 k (by omega) h2
theorem cr_76_79 (k : ℕ) (h1 : 76 ≤ k) (h2 : k < 79) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 77 then cr_76_77 k h1 h else cr_77_79 k (by omega) h2
theorem cr_79_80 (k : ℕ) (h1 : 79 ≤ k) (h2 : k < 80) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 79 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf79_ok
theorem cr_80_81 (k : ℕ) (h1 : 80 ≤ k) (h2 : k < 81) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 80 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf80_ok
theorem cr_81_82 (k : ℕ) (h1 : 81 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 81 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf81_ok
theorem cr_80_82 (k : ℕ) (h1 : 80 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 81 then cr_80_81 k h1 h else cr_81_82 k (by omega) h2
theorem cr_79_82 (k : ℕ) (h1 : 79 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 80 then cr_79_80 k h1 h else cr_80_82 k (by omega) h2
theorem cr_76_82 (k : ℕ) (h1 : 76 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 79 then cr_76_79 k h1 h else cr_79_82 k (by omega) h2
theorem cr_71_82 (k : ℕ) (h1 : 71 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 76 then cr_71_76 k h1 h else cr_76_82 k (by omega) h2
theorem cr_61_82 (k : ℕ) (h1 : 61 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 71 then cr_61_71 k h1 h else cr_71_82 k (by omega) h2
theorem cr_41_82 (k : ℕ) (h1 : 41 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 61 then cr_41_61 k h1 h else cr_61_82 k (by omega) h2
theorem cr_0_82 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 82) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 41 then cr_0_41 k h1 h else cr_41_82 k (by omega) h2
theorem cr_82_83 (k : ℕ) (h1 : 82 ≤ k) (h2 : k < 83) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 82 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf82_ok
theorem cr_83_84 (k : ℕ) (h1 : 83 ≤ k) (h2 : k < 84) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 83 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf83_ok
theorem cr_82_84 (k : ℕ) (h1 : 82 ≤ k) (h2 : k < 84) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 83 then cr_82_83 k h1 h else cr_83_84 k (by omega) h2
theorem cr_84_85 (k : ℕ) (h1 : 84 ≤ k) (h2 : k < 85) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 84 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf84_ok
theorem cr_85_86 (k : ℕ) (h1 : 85 ≤ k) (h2 : k < 86) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 85 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf85_ok
theorem cr_86_87 (k : ℕ) (h1 : 86 ≤ k) (h2 : k < 87) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 86 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf86_ok
theorem cr_85_87 (k : ℕ) (h1 : 85 ≤ k) (h2 : k < 87) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 86 then cr_85_86 k h1 h else cr_86_87 k (by omega) h2
theorem cr_84_87 (k : ℕ) (h1 : 84 ≤ k) (h2 : k < 87) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 85 then cr_84_85 k h1 h else cr_85_87 k (by omega) h2
theorem cr_82_87 (k : ℕ) (h1 : 82 ≤ k) (h2 : k < 87) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 84 then cr_82_84 k h1 h else cr_84_87 k (by omega) h2
theorem cr_87_88 (k : ℕ) (h1 : 87 ≤ k) (h2 : k < 88) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 87 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf87_ok
theorem cr_88_89 (k : ℕ) (h1 : 88 ≤ k) (h2 : k < 89) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 88 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf88_ok
theorem cr_87_89 (k : ℕ) (h1 : 87 ≤ k) (h2 : k < 89) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 88 then cr_87_88 k h1 h else cr_88_89 k (by omega) h2
theorem cr_89_90 (k : ℕ) (h1 : 89 ≤ k) (h2 : k < 90) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 89 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf89_ok
theorem cr_90_91 (k : ℕ) (h1 : 90 ≤ k) (h2 : k < 91) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 90 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf90_ok
theorem cr_91_92 (k : ℕ) (h1 : 91 ≤ k) (h2 : k < 92) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 91 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf91_ok
theorem cr_90_92 (k : ℕ) (h1 : 90 ≤ k) (h2 : k < 92) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 91 then cr_90_91 k h1 h else cr_91_92 k (by omega) h2
theorem cr_89_92 (k : ℕ) (h1 : 89 ≤ k) (h2 : k < 92) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 90 then cr_89_90 k h1 h else cr_90_92 k (by omega) h2
theorem cr_87_92 (k : ℕ) (h1 : 87 ≤ k) (h2 : k < 92) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 89 then cr_87_89 k h1 h else cr_89_92 k (by omega) h2
theorem cr_82_92 (k : ℕ) (h1 : 82 ≤ k) (h2 : k < 92) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 87 then cr_82_87 k h1 h else cr_87_92 k (by omega) h2
theorem cr_92_93 (k : ℕ) (h1 : 92 ≤ k) (h2 : k < 93) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 92 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf92_ok
theorem cr_93_94 (k : ℕ) (h1 : 93 ≤ k) (h2 : k < 94) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 93 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf93_ok
theorem cr_92_94 (k : ℕ) (h1 : 92 ≤ k) (h2 : k < 94) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 93 then cr_92_93 k h1 h else cr_93_94 k (by omega) h2
theorem cr_94_95 (k : ℕ) (h1 : 94 ≤ k) (h2 : k < 95) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 94 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf94_ok
theorem cr_95_96 (k : ℕ) (h1 : 95 ≤ k) (h2 : k < 96) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 95 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf95_ok
theorem cr_96_97 (k : ℕ) (h1 : 96 ≤ k) (h2 : k < 97) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 96 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf96_ok
theorem cr_95_97 (k : ℕ) (h1 : 95 ≤ k) (h2 : k < 97) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 96 then cr_95_96 k h1 h else cr_96_97 k (by omega) h2
theorem cr_94_97 (k : ℕ) (h1 : 94 ≤ k) (h2 : k < 97) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 95 then cr_94_95 k h1 h else cr_95_97 k (by omega) h2
theorem cr_92_97 (k : ℕ) (h1 : 92 ≤ k) (h2 : k < 97) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 94 then cr_92_94 k h1 h else cr_94_97 k (by omega) h2
theorem cr_97_98 (k : ℕ) (h1 : 97 ≤ k) (h2 : k < 98) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 97 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf97_ok
theorem cr_98_99 (k : ℕ) (h1 : 98 ≤ k) (h2 : k < 99) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 98 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf98_ok
theorem cr_97_99 (k : ℕ) (h1 : 97 ≤ k) (h2 : k < 99) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 98 then cr_97_98 k h1 h else cr_98_99 k (by omega) h2
theorem cr_99_100 (k : ℕ) (h1 : 99 ≤ k) (h2 : k < 100) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 99 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf99_ok
theorem cr_100_101 (k : ℕ) (h1 : 100 ≤ k) (h2 : k < 101) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 100 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf100_ok
theorem cr_101_102 (k : ℕ) (h1 : 101 ≤ k) (h2 : k < 102) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 101 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf101_ok
theorem cr_100_102 (k : ℕ) (h1 : 100 ≤ k) (h2 : k < 102) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 101 then cr_100_101 k h1 h else cr_101_102 k (by omega) h2
theorem cr_99_102 (k : ℕ) (h1 : 99 ≤ k) (h2 : k < 102) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 100 then cr_99_100 k h1 h else cr_100_102 k (by omega) h2
theorem cr_97_102 (k : ℕ) (h1 : 97 ≤ k) (h2 : k < 102) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 99 then cr_97_99 k h1 h else cr_99_102 k (by omega) h2
theorem cr_92_102 (k : ℕ) (h1 : 92 ≤ k) (h2 : k < 102) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 97 then cr_92_97 k h1 h else cr_97_102 k (by omega) h2
theorem cr_82_102 (k : ℕ) (h1 : 82 ≤ k) (h2 : k < 102) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 92 then cr_82_92 k h1 h else cr_92_102 k (by omega) h2
theorem cr_102_103 (k : ℕ) (h1 : 102 ≤ k) (h2 : k < 103) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 102 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf102_ok
theorem cr_103_104 (k : ℕ) (h1 : 103 ≤ k) (h2 : k < 104) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 103 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf103_ok
theorem cr_102_104 (k : ℕ) (h1 : 102 ≤ k) (h2 : k < 104) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 103 then cr_102_103 k h1 h else cr_103_104 k (by omega) h2
theorem cr_104_105 (k : ℕ) (h1 : 104 ≤ k) (h2 : k < 105) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 104 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf104_ok
theorem cr_105_106 (k : ℕ) (h1 : 105 ≤ k) (h2 : k < 106) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 105 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf105_ok
theorem cr_106_107 (k : ℕ) (h1 : 106 ≤ k) (h2 : k < 107) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 106 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf106_ok
theorem cr_105_107 (k : ℕ) (h1 : 105 ≤ k) (h2 : k < 107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 106 then cr_105_106 k h1 h else cr_106_107 k (by omega) h2
theorem cr_104_107 (k : ℕ) (h1 : 104 ≤ k) (h2 : k < 107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 105 then cr_104_105 k h1 h else cr_105_107 k (by omega) h2
theorem cr_102_107 (k : ℕ) (h1 : 102 ≤ k) (h2 : k < 107) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 104 then cr_102_104 k h1 h else cr_104_107 k (by omega) h2
theorem cr_107_108 (k : ℕ) (h1 : 107 ≤ k) (h2 : k < 108) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 107 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf107_ok
theorem cr_108_109 (k : ℕ) (h1 : 108 ≤ k) (h2 : k < 109) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 108 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf108_ok
theorem cr_107_109 (k : ℕ) (h1 : 107 ≤ k) (h2 : k < 109) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 108 then cr_107_108 k h1 h else cr_108_109 k (by omega) h2
theorem cr_109_110 (k : ℕ) (h1 : 109 ≤ k) (h2 : k < 110) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 109 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf109_ok
theorem cr_110_111 (k : ℕ) (h1 : 110 ≤ k) (h2 : k < 111) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 110 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf110_ok
theorem cr_111_112 (k : ℕ) (h1 : 111 ≤ k) (h2 : k < 112) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 111 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf111_ok
theorem cr_110_112 (k : ℕ) (h1 : 110 ≤ k) (h2 : k < 112) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 111 then cr_110_111 k h1 h else cr_111_112 k (by omega) h2
theorem cr_109_112 (k : ℕ) (h1 : 109 ≤ k) (h2 : k < 112) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 110 then cr_109_110 k h1 h else cr_110_112 k (by omega) h2
theorem cr_107_112 (k : ℕ) (h1 : 107 ≤ k) (h2 : k < 112) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 109 then cr_107_109 k h1 h else cr_109_112 k (by omega) h2
theorem cr_102_112 (k : ℕ) (h1 : 102 ≤ k) (h2 : k < 112) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 107 then cr_102_107 k h1 h else cr_107_112 k (by omega) h2
theorem cr_112_113 (k : ℕ) (h1 : 112 ≤ k) (h2 : k < 113) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 112 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf112_ok
theorem cr_113_114 (k : ℕ) (h1 : 113 ≤ k) (h2 : k < 114) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 113 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf113_ok
theorem cr_112_114 (k : ℕ) (h1 : 112 ≤ k) (h2 : k < 114) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 113 then cr_112_113 k h1 h else cr_113_114 k (by omega) h2
theorem cr_114_115 (k : ℕ) (h1 : 114 ≤ k) (h2 : k < 115) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 114 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf114_ok
theorem cr_115_116 (k : ℕ) (h1 : 115 ≤ k) (h2 : k < 116) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 115 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf115_ok
theorem cr_116_117 (k : ℕ) (h1 : 116 ≤ k) (h2 : k < 117) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 116 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf116_ok
theorem cr_115_117 (k : ℕ) (h1 : 115 ≤ k) (h2 : k < 117) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 116 then cr_115_116 k h1 h else cr_116_117 k (by omega) h2
theorem cr_114_117 (k : ℕ) (h1 : 114 ≤ k) (h2 : k < 117) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 115 then cr_114_115 k h1 h else cr_115_117 k (by omega) h2
theorem cr_112_117 (k : ℕ) (h1 : 112 ≤ k) (h2 : k < 117) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 114 then cr_112_114 k h1 h else cr_114_117 k (by omega) h2
theorem cr_117_118 (k : ℕ) (h1 : 117 ≤ k) (h2 : k < 118) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 117 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf117_ok
theorem cr_118_119 (k : ℕ) (h1 : 118 ≤ k) (h2 : k < 119) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 118 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf118_ok
theorem cr_119_120 (k : ℕ) (h1 : 119 ≤ k) (h2 : k < 120) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 119 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf119_ok
theorem cr_118_120 (k : ℕ) (h1 : 118 ≤ k) (h2 : k < 120) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 119 then cr_118_119 k h1 h else cr_119_120 k (by omega) h2
theorem cr_117_120 (k : ℕ) (h1 : 117 ≤ k) (h2 : k < 120) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 118 then cr_117_118 k h1 h else cr_118_120 k (by omega) h2
theorem cr_120_121 (k : ℕ) (h1 : 120 ≤ k) (h2 : k < 121) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 120 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf120_ok
theorem cr_121_122 (k : ℕ) (h1 : 121 ≤ k) (h2 : k < 122) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 121 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf121_ok
theorem cr_122_123 (k : ℕ) (h1 : 122 ≤ k) (h2 : k < 123) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 122 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf122_ok
theorem cr_121_123 (k : ℕ) (h1 : 121 ≤ k) (h2 : k < 123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 122 then cr_121_122 k h1 h else cr_122_123 k (by omega) h2
theorem cr_120_123 (k : ℕ) (h1 : 120 ≤ k) (h2 : k < 123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 121 then cr_120_121 k h1 h else cr_121_123 k (by omega) h2
theorem cr_117_123 (k : ℕ) (h1 : 117 ≤ k) (h2 : k < 123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 120 then cr_117_120 k h1 h else cr_120_123 k (by omega) h2
theorem cr_112_123 (k : ℕ) (h1 : 112 ≤ k) (h2 : k < 123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 117 then cr_112_117 k h1 h else cr_117_123 k (by omega) h2
theorem cr_102_123 (k : ℕ) (h1 : 102 ≤ k) (h2 : k < 123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 112 then cr_102_112 k h1 h else cr_112_123 k (by omega) h2
theorem cr_82_123 (k : ℕ) (h1 : 82 ≤ k) (h2 : k < 123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 102 then cr_82_102 k h1 h else cr_102_123 k (by omega) h2
theorem cr_123_124 (k : ℕ) (h1 : 123 ≤ k) (h2 : k < 124) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 123 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf123_ok
theorem cr_124_125 (k : ℕ) (h1 : 124 ≤ k) (h2 : k < 125) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 124 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf124_ok
theorem cr_123_125 (k : ℕ) (h1 : 123 ≤ k) (h2 : k < 125) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 124 then cr_123_124 k h1 h else cr_124_125 k (by omega) h2
theorem cr_125_126 (k : ℕ) (h1 : 125 ≤ k) (h2 : k < 126) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 125 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf125_ok
theorem cr_126_127 (k : ℕ) (h1 : 126 ≤ k) (h2 : k < 127) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 126 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf126_ok
theorem cr_127_128 (k : ℕ) (h1 : 127 ≤ k) (h2 : k < 128) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 127 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf127_ok
theorem cr_126_128 (k : ℕ) (h1 : 126 ≤ k) (h2 : k < 128) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 127 then cr_126_127 k h1 h else cr_127_128 k (by omega) h2
theorem cr_125_128 (k : ℕ) (h1 : 125 ≤ k) (h2 : k < 128) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 126 then cr_125_126 k h1 h else cr_126_128 k (by omega) h2
theorem cr_123_128 (k : ℕ) (h1 : 123 ≤ k) (h2 : k < 128) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 125 then cr_123_125 k h1 h else cr_125_128 k (by omega) h2
theorem cr_128_129 (k : ℕ) (h1 : 128 ≤ k) (h2 : k < 129) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 128 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf128_ok
theorem cr_129_130 (k : ℕ) (h1 : 129 ≤ k) (h2 : k < 130) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 129 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf129_ok
theorem cr_128_130 (k : ℕ) (h1 : 128 ≤ k) (h2 : k < 130) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 129 then cr_128_129 k h1 h else cr_129_130 k (by omega) h2
theorem cr_130_131 (k : ℕ) (h1 : 130 ≤ k) (h2 : k < 131) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 130 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf130_ok
theorem cr_131_132 (k : ℕ) (h1 : 131 ≤ k) (h2 : k < 132) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 131 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf131_ok
theorem cr_132_133 (k : ℕ) (h1 : 132 ≤ k) (h2 : k < 133) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 132 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf132_ok
theorem cr_131_133 (k : ℕ) (h1 : 131 ≤ k) (h2 : k < 133) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 132 then cr_131_132 k h1 h else cr_132_133 k (by omega) h2
theorem cr_130_133 (k : ℕ) (h1 : 130 ≤ k) (h2 : k < 133) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 131 then cr_130_131 k h1 h else cr_131_133 k (by omega) h2
theorem cr_128_133 (k : ℕ) (h1 : 128 ≤ k) (h2 : k < 133) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 130 then cr_128_130 k h1 h else cr_130_133 k (by omega) h2
theorem cr_123_133 (k : ℕ) (h1 : 123 ≤ k) (h2 : k < 133) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 128 then cr_123_128 k h1 h else cr_128_133 k (by omega) h2
theorem cr_133_134 (k : ℕ) (h1 : 133 ≤ k) (h2 : k < 134) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 133 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf133_ok
theorem cr_134_135 (k : ℕ) (h1 : 134 ≤ k) (h2 : k < 135) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 134 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf134_ok
theorem cr_133_135 (k : ℕ) (h1 : 133 ≤ k) (h2 : k < 135) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 134 then cr_133_134 k h1 h else cr_134_135 k (by omega) h2
theorem cr_135_136 (k : ℕ) (h1 : 135 ≤ k) (h2 : k < 136) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 135 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf135_ok
theorem cr_136_137 (k : ℕ) (h1 : 136 ≤ k) (h2 : k < 137) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 136 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf136_ok
theorem cr_137_138 (k : ℕ) (h1 : 137 ≤ k) (h2 : k < 138) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 137 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf137_ok
theorem cr_136_138 (k : ℕ) (h1 : 136 ≤ k) (h2 : k < 138) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 137 then cr_136_137 k h1 h else cr_137_138 k (by omega) h2
theorem cr_135_138 (k : ℕ) (h1 : 135 ≤ k) (h2 : k < 138) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 136 then cr_135_136 k h1 h else cr_136_138 k (by omega) h2
theorem cr_133_138 (k : ℕ) (h1 : 133 ≤ k) (h2 : k < 138) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 135 then cr_133_135 k h1 h else cr_135_138 k (by omega) h2
theorem cr_138_139 (k : ℕ) (h1 : 138 ≤ k) (h2 : k < 139) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 138 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf138_ok
theorem cr_139_140 (k : ℕ) (h1 : 139 ≤ k) (h2 : k < 140) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 139 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf139_ok
theorem cr_138_140 (k : ℕ) (h1 : 138 ≤ k) (h2 : k < 140) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 139 then cr_138_139 k h1 h else cr_139_140 k (by omega) h2
theorem cr_140_141 (k : ℕ) (h1 : 140 ≤ k) (h2 : k < 141) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 140 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf140_ok
theorem cr_141_142 (k : ℕ) (h1 : 141 ≤ k) (h2 : k < 142) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 141 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf141_ok
theorem cr_142_143 (k : ℕ) (h1 : 142 ≤ k) (h2 : k < 143) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 142 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf142_ok
theorem cr_141_143 (k : ℕ) (h1 : 141 ≤ k) (h2 : k < 143) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 142 then cr_141_142 k h1 h else cr_142_143 k (by omega) h2
theorem cr_140_143 (k : ℕ) (h1 : 140 ≤ k) (h2 : k < 143) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 141 then cr_140_141 k h1 h else cr_141_143 k (by omega) h2
theorem cr_138_143 (k : ℕ) (h1 : 138 ≤ k) (h2 : k < 143) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 140 then cr_138_140 k h1 h else cr_140_143 k (by omega) h2
theorem cr_133_143 (k : ℕ) (h1 : 133 ≤ k) (h2 : k < 143) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 138 then cr_133_138 k h1 h else cr_138_143 k (by omega) h2
theorem cr_123_143 (k : ℕ) (h1 : 123 ≤ k) (h2 : k < 143) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 133 then cr_123_133 k h1 h else cr_133_143 k (by omega) h2
theorem cr_143_144 (k : ℕ) (h1 : 143 ≤ k) (h2 : k < 144) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 143 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf143_ok
theorem cr_144_145 (k : ℕ) (h1 : 144 ≤ k) (h2 : k < 145) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 144 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf144_ok
theorem cr_143_145 (k : ℕ) (h1 : 143 ≤ k) (h2 : k < 145) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 144 then cr_143_144 k h1 h else cr_144_145 k (by omega) h2
theorem cr_145_146 (k : ℕ) (h1 : 145 ≤ k) (h2 : k < 146) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 145 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf145_ok
theorem cr_146_147 (k : ℕ) (h1 : 146 ≤ k) (h2 : k < 147) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 146 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf146_ok
theorem cr_147_148 (k : ℕ) (h1 : 147 ≤ k) (h2 : k < 148) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 147 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf147_ok
theorem cr_146_148 (k : ℕ) (h1 : 146 ≤ k) (h2 : k < 148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 147 then cr_146_147 k h1 h else cr_147_148 k (by omega) h2
theorem cr_145_148 (k : ℕ) (h1 : 145 ≤ k) (h2 : k < 148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 146 then cr_145_146 k h1 h else cr_146_148 k (by omega) h2
theorem cr_143_148 (k : ℕ) (h1 : 143 ≤ k) (h2 : k < 148) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 145 then cr_143_145 k h1 h else cr_145_148 k (by omega) h2
theorem cr_148_149 (k : ℕ) (h1 : 148 ≤ k) (h2 : k < 149) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 148 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf148_ok
theorem cr_149_150 (k : ℕ) (h1 : 149 ≤ k) (h2 : k < 150) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 149 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf149_ok
theorem cr_148_150 (k : ℕ) (h1 : 148 ≤ k) (h2 : k < 150) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 149 then cr_148_149 k h1 h else cr_149_150 k (by omega) h2
theorem cr_150_151 (k : ℕ) (h1 : 150 ≤ k) (h2 : k < 151) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 150 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf150_ok
theorem cr_151_152 (k : ℕ) (h1 : 151 ≤ k) (h2 : k < 152) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 151 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf151_ok
theorem cr_152_153 (k : ℕ) (h1 : 152 ≤ k) (h2 : k < 153) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 152 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf152_ok
theorem cr_151_153 (k : ℕ) (h1 : 151 ≤ k) (h2 : k < 153) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 152 then cr_151_152 k h1 h else cr_152_153 k (by omega) h2
theorem cr_150_153 (k : ℕ) (h1 : 150 ≤ k) (h2 : k < 153) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 151 then cr_150_151 k h1 h else cr_151_153 k (by omega) h2
theorem cr_148_153 (k : ℕ) (h1 : 148 ≤ k) (h2 : k < 153) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 150 then cr_148_150 k h1 h else cr_150_153 k (by omega) h2
theorem cr_143_153 (k : ℕ) (h1 : 143 ≤ k) (h2 : k < 153) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 148 then cr_143_148 k h1 h else cr_148_153 k (by omega) h2
theorem cr_153_154 (k : ℕ) (h1 : 153 ≤ k) (h2 : k < 154) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 153 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf153_ok
theorem cr_154_155 (k : ℕ) (h1 : 154 ≤ k) (h2 : k < 155) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 154 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf154_ok
theorem cr_153_155 (k : ℕ) (h1 : 153 ≤ k) (h2 : k < 155) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 154 then cr_153_154 k h1 h else cr_154_155 k (by omega) h2
theorem cr_155_156 (k : ℕ) (h1 : 155 ≤ k) (h2 : k < 156) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 155 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf155_ok
theorem cr_156_157 (k : ℕ) (h1 : 156 ≤ k) (h2 : k < 157) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 156 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf156_ok
theorem cr_157_158 (k : ℕ) (h1 : 157 ≤ k) (h2 : k < 158) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 157 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf157_ok
theorem cr_156_158 (k : ℕ) (h1 : 156 ≤ k) (h2 : k < 158) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 157 then cr_156_157 k h1 h else cr_157_158 k (by omega) h2
theorem cr_155_158 (k : ℕ) (h1 : 155 ≤ k) (h2 : k < 158) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 156 then cr_155_156 k h1 h else cr_156_158 k (by omega) h2
theorem cr_153_158 (k : ℕ) (h1 : 153 ≤ k) (h2 : k < 158) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 155 then cr_153_155 k h1 h else cr_155_158 k (by omega) h2
theorem cr_158_159 (k : ℕ) (h1 : 158 ≤ k) (h2 : k < 159) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 158 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf158_ok
theorem cr_159_160 (k : ℕ) (h1 : 159 ≤ k) (h2 : k < 160) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 159 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf159_ok
theorem cr_160_161 (k : ℕ) (h1 : 160 ≤ k) (h2 : k < 161) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 160 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf160_ok
theorem cr_159_161 (k : ℕ) (h1 : 159 ≤ k) (h2 : k < 161) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 160 then cr_159_160 k h1 h else cr_160_161 k (by omega) h2
theorem cr_158_161 (k : ℕ) (h1 : 158 ≤ k) (h2 : k < 161) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 159 then cr_158_159 k h1 h else cr_159_161 k (by omega) h2
theorem cr_161_162 (k : ℕ) (h1 : 161 ≤ k) (h2 : k < 162) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 161 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf161_ok
theorem cr_162_163 (k : ℕ) (h1 : 162 ≤ k) (h2 : k < 163) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 162 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf162_ok
theorem cr_163_164 (k : ℕ) (h1 : 163 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 163 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf163_ok
theorem cr_162_164 (k : ℕ) (h1 : 162 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 163 then cr_162_163 k h1 h else cr_163_164 k (by omega) h2
theorem cr_161_164 (k : ℕ) (h1 : 161 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 162 then cr_161_162 k h1 h else cr_162_164 k (by omega) h2
theorem cr_158_164 (k : ℕ) (h1 : 158 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 161 then cr_158_161 k h1 h else cr_161_164 k (by omega) h2
theorem cr_153_164 (k : ℕ) (h1 : 153 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 158 then cr_153_158 k h1 h else cr_158_164 k (by omega) h2
theorem cr_143_164 (k : ℕ) (h1 : 143 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 153 then cr_143_153 k h1 h else cr_153_164 k (by omega) h2
theorem cr_123_164 (k : ℕ) (h1 : 123 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 143 then cr_123_143 k h1 h else cr_143_164 k (by omega) h2
theorem cr_82_164 (k : ℕ) (h1 : 82 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 123 then cr_82_123 k h1 h else cr_123_164 k (by omega) h2
theorem cr_0_164 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 82 then cr_0_82 k h1 h else cr_82_164 k (by omega) h2
theorem cr_164_165 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 165) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 164 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf164_ok
theorem cr_165_166 (k : ℕ) (h1 : 165 ≤ k) (h2 : k < 166) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 165 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf165_ok
theorem cr_164_166 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 166) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 165 then cr_164_165 k h1 h else cr_165_166 k (by omega) h2
theorem cr_166_167 (k : ℕ) (h1 : 166 ≤ k) (h2 : k < 167) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 166 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf166_ok
theorem cr_167_168 (k : ℕ) (h1 : 167 ≤ k) (h2 : k < 168) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 167 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf167_ok
theorem cr_168_169 (k : ℕ) (h1 : 168 ≤ k) (h2 : k < 169) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 168 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf168_ok
theorem cr_167_169 (k : ℕ) (h1 : 167 ≤ k) (h2 : k < 169) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 168 then cr_167_168 k h1 h else cr_168_169 k (by omega) h2
theorem cr_166_169 (k : ℕ) (h1 : 166 ≤ k) (h2 : k < 169) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 167 then cr_166_167 k h1 h else cr_167_169 k (by omega) h2
theorem cr_164_169 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 169) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 166 then cr_164_166 k h1 h else cr_166_169 k (by omega) h2
theorem cr_169_170 (k : ℕ) (h1 : 169 ≤ k) (h2 : k < 170) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 169 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf169_ok
theorem cr_170_171 (k : ℕ) (h1 : 170 ≤ k) (h2 : k < 171) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 170 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf170_ok
theorem cr_169_171 (k : ℕ) (h1 : 169 ≤ k) (h2 : k < 171) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 170 then cr_169_170 k h1 h else cr_170_171 k (by omega) h2
theorem cr_171_172 (k : ℕ) (h1 : 171 ≤ k) (h2 : k < 172) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 171 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf171_ok
theorem cr_172_173 (k : ℕ) (h1 : 172 ≤ k) (h2 : k < 173) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 172 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf172_ok
theorem cr_173_174 (k : ℕ) (h1 : 173 ≤ k) (h2 : k < 174) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 173 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf173_ok
theorem cr_172_174 (k : ℕ) (h1 : 172 ≤ k) (h2 : k < 174) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 173 then cr_172_173 k h1 h else cr_173_174 k (by omega) h2
theorem cr_171_174 (k : ℕ) (h1 : 171 ≤ k) (h2 : k < 174) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 172 then cr_171_172 k h1 h else cr_172_174 k (by omega) h2
theorem cr_169_174 (k : ℕ) (h1 : 169 ≤ k) (h2 : k < 174) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 171 then cr_169_171 k h1 h else cr_171_174 k (by omega) h2
theorem cr_164_174 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 174) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 169 then cr_164_169 k h1 h else cr_169_174 k (by omega) h2
theorem cr_174_175 (k : ℕ) (h1 : 174 ≤ k) (h2 : k < 175) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 174 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf174_ok
theorem cr_175_176 (k : ℕ) (h1 : 175 ≤ k) (h2 : k < 176) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 175 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf175_ok
theorem cr_174_176 (k : ℕ) (h1 : 174 ≤ k) (h2 : k < 176) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 175 then cr_174_175 k h1 h else cr_175_176 k (by omega) h2
theorem cr_176_177 (k : ℕ) (h1 : 176 ≤ k) (h2 : k < 177) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 176 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf176_ok
theorem cr_177_178 (k : ℕ) (h1 : 177 ≤ k) (h2 : k < 178) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 177 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf177_ok
theorem cr_178_179 (k : ℕ) (h1 : 178 ≤ k) (h2 : k < 179) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 178 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf178_ok
theorem cr_177_179 (k : ℕ) (h1 : 177 ≤ k) (h2 : k < 179) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 178 then cr_177_178 k h1 h else cr_178_179 k (by omega) h2
theorem cr_176_179 (k : ℕ) (h1 : 176 ≤ k) (h2 : k < 179) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 177 then cr_176_177 k h1 h else cr_177_179 k (by omega) h2
theorem cr_174_179 (k : ℕ) (h1 : 174 ≤ k) (h2 : k < 179) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 176 then cr_174_176 k h1 h else cr_176_179 k (by omega) h2
theorem cr_179_180 (k : ℕ) (h1 : 179 ≤ k) (h2 : k < 180) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 179 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf179_ok
theorem cr_180_181 (k : ℕ) (h1 : 180 ≤ k) (h2 : k < 181) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 180 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf180_ok
theorem cr_179_181 (k : ℕ) (h1 : 179 ≤ k) (h2 : k < 181) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 180 then cr_179_180 k h1 h else cr_180_181 k (by omega) h2
theorem cr_181_182 (k : ℕ) (h1 : 181 ≤ k) (h2 : k < 182) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 181 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf181_ok
theorem cr_182_183 (k : ℕ) (h1 : 182 ≤ k) (h2 : k < 183) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 182 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf182_ok
theorem cr_183_184 (k : ℕ) (h1 : 183 ≤ k) (h2 : k < 184) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 183 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf183_ok
theorem cr_182_184 (k : ℕ) (h1 : 182 ≤ k) (h2 : k < 184) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 183 then cr_182_183 k h1 h else cr_183_184 k (by omega) h2
theorem cr_181_184 (k : ℕ) (h1 : 181 ≤ k) (h2 : k < 184) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 182 then cr_181_182 k h1 h else cr_182_184 k (by omega) h2
theorem cr_179_184 (k : ℕ) (h1 : 179 ≤ k) (h2 : k < 184) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 181 then cr_179_181 k h1 h else cr_181_184 k (by omega) h2
theorem cr_174_184 (k : ℕ) (h1 : 174 ≤ k) (h2 : k < 184) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 179 then cr_174_179 k h1 h else cr_179_184 k (by omega) h2
theorem cr_164_184 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 184) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 174 then cr_164_174 k h1 h else cr_174_184 k (by omega) h2
theorem cr_184_185 (k : ℕ) (h1 : 184 ≤ k) (h2 : k < 185) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 184 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf184_ok
theorem cr_185_186 (k : ℕ) (h1 : 185 ≤ k) (h2 : k < 186) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 185 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf185_ok
theorem cr_184_186 (k : ℕ) (h1 : 184 ≤ k) (h2 : k < 186) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 185 then cr_184_185 k h1 h else cr_185_186 k (by omega) h2
theorem cr_186_187 (k : ℕ) (h1 : 186 ≤ k) (h2 : k < 187) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 186 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf186_ok
theorem cr_187_188 (k : ℕ) (h1 : 187 ≤ k) (h2 : k < 188) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 187 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf187_ok
theorem cr_188_189 (k : ℕ) (h1 : 188 ≤ k) (h2 : k < 189) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 188 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf188_ok
theorem cr_187_189 (k : ℕ) (h1 : 187 ≤ k) (h2 : k < 189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 188 then cr_187_188 k h1 h else cr_188_189 k (by omega) h2
theorem cr_186_189 (k : ℕ) (h1 : 186 ≤ k) (h2 : k < 189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 187 then cr_186_187 k h1 h else cr_187_189 k (by omega) h2
theorem cr_184_189 (k : ℕ) (h1 : 184 ≤ k) (h2 : k < 189) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 186 then cr_184_186 k h1 h else cr_186_189 k (by omega) h2
theorem cr_189_190 (k : ℕ) (h1 : 189 ≤ k) (h2 : k < 190) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 189 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf189_ok
theorem cr_190_191 (k : ℕ) (h1 : 190 ≤ k) (h2 : k < 191) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 190 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf190_ok
theorem cr_189_191 (k : ℕ) (h1 : 189 ≤ k) (h2 : k < 191) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 190 then cr_189_190 k h1 h else cr_190_191 k (by omega) h2
theorem cr_191_192 (k : ℕ) (h1 : 191 ≤ k) (h2 : k < 192) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 191 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf191_ok
theorem cr_192_193 (k : ℕ) (h1 : 192 ≤ k) (h2 : k < 193) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 192 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf192_ok
theorem cr_193_194 (k : ℕ) (h1 : 193 ≤ k) (h2 : k < 194) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 193 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf193_ok
theorem cr_192_194 (k : ℕ) (h1 : 192 ≤ k) (h2 : k < 194) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 193 then cr_192_193 k h1 h else cr_193_194 k (by omega) h2
theorem cr_191_194 (k : ℕ) (h1 : 191 ≤ k) (h2 : k < 194) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 192 then cr_191_192 k h1 h else cr_192_194 k (by omega) h2
theorem cr_189_194 (k : ℕ) (h1 : 189 ≤ k) (h2 : k < 194) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 191 then cr_189_191 k h1 h else cr_191_194 k (by omega) h2
theorem cr_184_194 (k : ℕ) (h1 : 184 ≤ k) (h2 : k < 194) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 189 then cr_184_189 k h1 h else cr_189_194 k (by omega) h2
theorem cr_194_195 (k : ℕ) (h1 : 194 ≤ k) (h2 : k < 195) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 194 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf194_ok
theorem cr_195_196 (k : ℕ) (h1 : 195 ≤ k) (h2 : k < 196) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 195 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf195_ok
theorem cr_194_196 (k : ℕ) (h1 : 194 ≤ k) (h2 : k < 196) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 195 then cr_194_195 k h1 h else cr_195_196 k (by omega) h2
theorem cr_196_197 (k : ℕ) (h1 : 196 ≤ k) (h2 : k < 197) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 196 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf196_ok
theorem cr_197_198 (k : ℕ) (h1 : 197 ≤ k) (h2 : k < 198) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 197 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf197_ok
theorem cr_198_199 (k : ℕ) (h1 : 198 ≤ k) (h2 : k < 199) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 198 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf198_ok
theorem cr_197_199 (k : ℕ) (h1 : 197 ≤ k) (h2 : k < 199) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 198 then cr_197_198 k h1 h else cr_198_199 k (by omega) h2
theorem cr_196_199 (k : ℕ) (h1 : 196 ≤ k) (h2 : k < 199) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 197 then cr_196_197 k h1 h else cr_197_199 k (by omega) h2
theorem cr_194_199 (k : ℕ) (h1 : 194 ≤ k) (h2 : k < 199) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 196 then cr_194_196 k h1 h else cr_196_199 k (by omega) h2
theorem cr_199_200 (k : ℕ) (h1 : 199 ≤ k) (h2 : k < 200) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 199 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf199_ok
theorem cr_200_201 (k : ℕ) (h1 : 200 ≤ k) (h2 : k < 201) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 200 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf200_ok
theorem cr_201_202 (k : ℕ) (h1 : 201 ≤ k) (h2 : k < 202) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 201 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf201_ok
theorem cr_200_202 (k : ℕ) (h1 : 200 ≤ k) (h2 : k < 202) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 201 then cr_200_201 k h1 h else cr_201_202 k (by omega) h2
theorem cr_199_202 (k : ℕ) (h1 : 199 ≤ k) (h2 : k < 202) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 200 then cr_199_200 k h1 h else cr_200_202 k (by omega) h2
theorem cr_202_203 (k : ℕ) (h1 : 202 ≤ k) (h2 : k < 203) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 202 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf202_ok
theorem cr_203_204 (k : ℕ) (h1 : 203 ≤ k) (h2 : k < 204) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 203 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf203_ok
theorem cr_204_205 (k : ℕ) (h1 : 204 ≤ k) (h2 : k < 205) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 204 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf204_ok
theorem cr_203_205 (k : ℕ) (h1 : 203 ≤ k) (h2 : k < 205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 204 then cr_203_204 k h1 h else cr_204_205 k (by omega) h2
theorem cr_202_205 (k : ℕ) (h1 : 202 ≤ k) (h2 : k < 205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 203 then cr_202_203 k h1 h else cr_203_205 k (by omega) h2
theorem cr_199_205 (k : ℕ) (h1 : 199 ≤ k) (h2 : k < 205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 202 then cr_199_202 k h1 h else cr_202_205 k (by omega) h2
theorem cr_194_205 (k : ℕ) (h1 : 194 ≤ k) (h2 : k < 205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 199 then cr_194_199 k h1 h else cr_199_205 k (by omega) h2
theorem cr_184_205 (k : ℕ) (h1 : 184 ≤ k) (h2 : k < 205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 194 then cr_184_194 k h1 h else cr_194_205 k (by omega) h2
theorem cr_164_205 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 184 then cr_164_184 k h1 h else cr_184_205 k (by omega) h2
theorem cr_205_206 (k : ℕ) (h1 : 205 ≤ k) (h2 : k < 206) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 205 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf205_ok
theorem cr_206_207 (k : ℕ) (h1 : 206 ≤ k) (h2 : k < 207) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 206 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf206_ok
theorem cr_205_207 (k : ℕ) (h1 : 205 ≤ k) (h2 : k < 207) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 206 then cr_205_206 k h1 h else cr_206_207 k (by omega) h2
theorem cr_207_208 (k : ℕ) (h1 : 207 ≤ k) (h2 : k < 208) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 207 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf207_ok
theorem cr_208_209 (k : ℕ) (h1 : 208 ≤ k) (h2 : k < 209) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 208 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf208_ok
theorem cr_209_210 (k : ℕ) (h1 : 209 ≤ k) (h2 : k < 210) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 209 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf209_ok
theorem cr_208_210 (k : ℕ) (h1 : 208 ≤ k) (h2 : k < 210) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 209 then cr_208_209 k h1 h else cr_209_210 k (by omega) h2
theorem cr_207_210 (k : ℕ) (h1 : 207 ≤ k) (h2 : k < 210) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 208 then cr_207_208 k h1 h else cr_208_210 k (by omega) h2
theorem cr_205_210 (k : ℕ) (h1 : 205 ≤ k) (h2 : k < 210) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 207 then cr_205_207 k h1 h else cr_207_210 k (by omega) h2
theorem cr_210_211 (k : ℕ) (h1 : 210 ≤ k) (h2 : k < 211) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 210 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf210_ok
theorem cr_211_212 (k : ℕ) (h1 : 211 ≤ k) (h2 : k < 212) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 211 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf211_ok
theorem cr_210_212 (k : ℕ) (h1 : 210 ≤ k) (h2 : k < 212) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 211 then cr_210_211 k h1 h else cr_211_212 k (by omega) h2
theorem cr_212_213 (k : ℕ) (h1 : 212 ≤ k) (h2 : k < 213) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 212 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf212_ok
theorem cr_213_214 (k : ℕ) (h1 : 213 ≤ k) (h2 : k < 214) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 213 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf213_ok
theorem cr_214_215 (k : ℕ) (h1 : 214 ≤ k) (h2 : k < 215) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 214 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf214_ok
theorem cr_213_215 (k : ℕ) (h1 : 213 ≤ k) (h2 : k < 215) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 214 then cr_213_214 k h1 h else cr_214_215 k (by omega) h2
theorem cr_212_215 (k : ℕ) (h1 : 212 ≤ k) (h2 : k < 215) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 213 then cr_212_213 k h1 h else cr_213_215 k (by omega) h2
theorem cr_210_215 (k : ℕ) (h1 : 210 ≤ k) (h2 : k < 215) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 212 then cr_210_212 k h1 h else cr_212_215 k (by omega) h2
theorem cr_205_215 (k : ℕ) (h1 : 205 ≤ k) (h2 : k < 215) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 210 then cr_205_210 k h1 h else cr_210_215 k (by omega) h2
theorem cr_215_216 (k : ℕ) (h1 : 215 ≤ k) (h2 : k < 216) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 215 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf215_ok
theorem cr_216_217 (k : ℕ) (h1 : 216 ≤ k) (h2 : k < 217) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 216 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf216_ok
theorem cr_215_217 (k : ℕ) (h1 : 215 ≤ k) (h2 : k < 217) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 216 then cr_215_216 k h1 h else cr_216_217 k (by omega) h2
theorem cr_217_218 (k : ℕ) (h1 : 217 ≤ k) (h2 : k < 218) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 217 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf217_ok
theorem cr_218_219 (k : ℕ) (h1 : 218 ≤ k) (h2 : k < 219) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 218 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf218_ok
theorem cr_219_220 (k : ℕ) (h1 : 219 ≤ k) (h2 : k < 220) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 219 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf219_ok
theorem cr_218_220 (k : ℕ) (h1 : 218 ≤ k) (h2 : k < 220) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 219 then cr_218_219 k h1 h else cr_219_220 k (by omega) h2
theorem cr_217_220 (k : ℕ) (h1 : 217 ≤ k) (h2 : k < 220) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 218 then cr_217_218 k h1 h else cr_218_220 k (by omega) h2
theorem cr_215_220 (k : ℕ) (h1 : 215 ≤ k) (h2 : k < 220) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 217 then cr_215_217 k h1 h else cr_217_220 k (by omega) h2
theorem cr_220_221 (k : ℕ) (h1 : 220 ≤ k) (h2 : k < 221) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 220 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf220_ok
theorem cr_221_222 (k : ℕ) (h1 : 221 ≤ k) (h2 : k < 222) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 221 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf221_ok
theorem cr_220_222 (k : ℕ) (h1 : 220 ≤ k) (h2 : k < 222) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 221 then cr_220_221 k h1 h else cr_221_222 k (by omega) h2
theorem cr_222_223 (k : ℕ) (h1 : 222 ≤ k) (h2 : k < 223) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 222 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf222_ok
theorem cr_223_224 (k : ℕ) (h1 : 223 ≤ k) (h2 : k < 224) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 223 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf223_ok
theorem cr_224_225 (k : ℕ) (h1 : 224 ≤ k) (h2 : k < 225) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 224 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf224_ok
theorem cr_223_225 (k : ℕ) (h1 : 223 ≤ k) (h2 : k < 225) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 224 then cr_223_224 k h1 h else cr_224_225 k (by omega) h2
theorem cr_222_225 (k : ℕ) (h1 : 222 ≤ k) (h2 : k < 225) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 223 then cr_222_223 k h1 h else cr_223_225 k (by omega) h2
theorem cr_220_225 (k : ℕ) (h1 : 220 ≤ k) (h2 : k < 225) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 222 then cr_220_222 k h1 h else cr_222_225 k (by omega) h2
theorem cr_215_225 (k : ℕ) (h1 : 215 ≤ k) (h2 : k < 225) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 220 then cr_215_220 k h1 h else cr_220_225 k (by omega) h2
theorem cr_205_225 (k : ℕ) (h1 : 205 ≤ k) (h2 : k < 225) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 215 then cr_205_215 k h1 h else cr_215_225 k (by omega) h2
theorem cr_225_226 (k : ℕ) (h1 : 225 ≤ k) (h2 : k < 226) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 225 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf225_ok
theorem cr_226_227 (k : ℕ) (h1 : 226 ≤ k) (h2 : k < 227) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 226 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf226_ok
theorem cr_225_227 (k : ℕ) (h1 : 225 ≤ k) (h2 : k < 227) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 226 then cr_225_226 k h1 h else cr_226_227 k (by omega) h2
theorem cr_227_228 (k : ℕ) (h1 : 227 ≤ k) (h2 : k < 228) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 227 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf227_ok
theorem cr_228_229 (k : ℕ) (h1 : 228 ≤ k) (h2 : k < 229) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 228 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf228_ok
theorem cr_229_230 (k : ℕ) (h1 : 229 ≤ k) (h2 : k < 230) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 229 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf229_ok
theorem cr_228_230 (k : ℕ) (h1 : 228 ≤ k) (h2 : k < 230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 229 then cr_228_229 k h1 h else cr_229_230 k (by omega) h2
theorem cr_227_230 (k : ℕ) (h1 : 227 ≤ k) (h2 : k < 230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 228 then cr_227_228 k h1 h else cr_228_230 k (by omega) h2
theorem cr_225_230 (k : ℕ) (h1 : 225 ≤ k) (h2 : k < 230) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 227 then cr_225_227 k h1 h else cr_227_230 k (by omega) h2
theorem cr_230_231 (k : ℕ) (h1 : 230 ≤ k) (h2 : k < 231) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 230 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf230_ok
theorem cr_231_232 (k : ℕ) (h1 : 231 ≤ k) (h2 : k < 232) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 231 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf231_ok
theorem cr_230_232 (k : ℕ) (h1 : 230 ≤ k) (h2 : k < 232) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 231 then cr_230_231 k h1 h else cr_231_232 k (by omega) h2
theorem cr_232_233 (k : ℕ) (h1 : 232 ≤ k) (h2 : k < 233) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 232 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf232_ok
theorem cr_233_234 (k : ℕ) (h1 : 233 ≤ k) (h2 : k < 234) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 233 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf233_ok
theorem cr_234_235 (k : ℕ) (h1 : 234 ≤ k) (h2 : k < 235) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 234 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf234_ok
theorem cr_233_235 (k : ℕ) (h1 : 233 ≤ k) (h2 : k < 235) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 234 then cr_233_234 k h1 h else cr_234_235 k (by omega) h2
theorem cr_232_235 (k : ℕ) (h1 : 232 ≤ k) (h2 : k < 235) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 233 then cr_232_233 k h1 h else cr_233_235 k (by omega) h2
theorem cr_230_235 (k : ℕ) (h1 : 230 ≤ k) (h2 : k < 235) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 232 then cr_230_232 k h1 h else cr_232_235 k (by omega) h2
theorem cr_225_235 (k : ℕ) (h1 : 225 ≤ k) (h2 : k < 235) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 230 then cr_225_230 k h1 h else cr_230_235 k (by omega) h2
theorem cr_235_236 (k : ℕ) (h1 : 235 ≤ k) (h2 : k < 236) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 235 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf235_ok
theorem cr_236_237 (k : ℕ) (h1 : 236 ≤ k) (h2 : k < 237) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 236 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf236_ok
theorem cr_235_237 (k : ℕ) (h1 : 235 ≤ k) (h2 : k < 237) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 236 then cr_235_236 k h1 h else cr_236_237 k (by omega) h2
theorem cr_237_238 (k : ℕ) (h1 : 237 ≤ k) (h2 : k < 238) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 237 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf237_ok
theorem cr_238_239 (k : ℕ) (h1 : 238 ≤ k) (h2 : k < 239) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 238 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf238_ok
theorem cr_239_240 (k : ℕ) (h1 : 239 ≤ k) (h2 : k < 240) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 239 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf239_ok
theorem cr_238_240 (k : ℕ) (h1 : 238 ≤ k) (h2 : k < 240) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 239 then cr_238_239 k h1 h else cr_239_240 k (by omega) h2
theorem cr_237_240 (k : ℕ) (h1 : 237 ≤ k) (h2 : k < 240) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 238 then cr_237_238 k h1 h else cr_238_240 k (by omega) h2
theorem cr_235_240 (k : ℕ) (h1 : 235 ≤ k) (h2 : k < 240) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 237 then cr_235_237 k h1 h else cr_237_240 k (by omega) h2
theorem cr_240_241 (k : ℕ) (h1 : 240 ≤ k) (h2 : k < 241) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 240 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf240_ok
theorem cr_241_242 (k : ℕ) (h1 : 241 ≤ k) (h2 : k < 242) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 241 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf241_ok
theorem cr_242_243 (k : ℕ) (h1 : 242 ≤ k) (h2 : k < 243) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 242 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf242_ok
theorem cr_241_243 (k : ℕ) (h1 : 241 ≤ k) (h2 : k < 243) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 242 then cr_241_242 k h1 h else cr_242_243 k (by omega) h2
theorem cr_240_243 (k : ℕ) (h1 : 240 ≤ k) (h2 : k < 243) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 241 then cr_240_241 k h1 h else cr_241_243 k (by omega) h2
theorem cr_243_244 (k : ℕ) (h1 : 243 ≤ k) (h2 : k < 244) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 243 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf243_ok
theorem cr_244_245 (k : ℕ) (h1 : 244 ≤ k) (h2 : k < 245) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 244 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf244_ok
theorem cr_245_246 (k : ℕ) (h1 : 245 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 245 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf245_ok
theorem cr_244_246 (k : ℕ) (h1 : 244 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 245 then cr_244_245 k h1 h else cr_245_246 k (by omega) h2
theorem cr_243_246 (k : ℕ) (h1 : 243 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 244 then cr_243_244 k h1 h else cr_244_246 k (by omega) h2
theorem cr_240_246 (k : ℕ) (h1 : 240 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 243 then cr_240_243 k h1 h else cr_243_246 k (by omega) h2
theorem cr_235_246 (k : ℕ) (h1 : 235 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 240 then cr_235_240 k h1 h else cr_240_246 k (by omega) h2
theorem cr_225_246 (k : ℕ) (h1 : 225 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 235 then cr_225_235 k h1 h else cr_235_246 k (by omega) h2
theorem cr_205_246 (k : ℕ) (h1 : 205 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 225 then cr_205_225 k h1 h else cr_225_246 k (by omega) h2
theorem cr_164_246 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 205 then cr_164_205 k h1 h else cr_205_246 k (by omega) h2
theorem cr_246_247 (k : ℕ) (h1 : 246 ≤ k) (h2 : k < 247) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 246 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf246_ok
theorem cr_247_248 (k : ℕ) (h1 : 247 ≤ k) (h2 : k < 248) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 247 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf247_ok
theorem cr_246_248 (k : ℕ) (h1 : 246 ≤ k) (h2 : k < 248) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 247 then cr_246_247 k h1 h else cr_247_248 k (by omega) h2
theorem cr_248_249 (k : ℕ) (h1 : 248 ≤ k) (h2 : k < 249) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 248 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf248_ok
theorem cr_249_250 (k : ℕ) (h1 : 249 ≤ k) (h2 : k < 250) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 249 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf249_ok
theorem cr_250_251 (k : ℕ) (h1 : 250 ≤ k) (h2 : k < 251) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 250 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf250_ok
theorem cr_249_251 (k : ℕ) (h1 : 249 ≤ k) (h2 : k < 251) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 250 then cr_249_250 k h1 h else cr_250_251 k (by omega) h2
theorem cr_248_251 (k : ℕ) (h1 : 248 ≤ k) (h2 : k < 251) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 249 then cr_248_249 k h1 h else cr_249_251 k (by omega) h2
theorem cr_246_251 (k : ℕ) (h1 : 246 ≤ k) (h2 : k < 251) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 248 then cr_246_248 k h1 h else cr_248_251 k (by omega) h2
theorem cr_251_252 (k : ℕ) (h1 : 251 ≤ k) (h2 : k < 252) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 251 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf251_ok
theorem cr_252_253 (k : ℕ) (h1 : 252 ≤ k) (h2 : k < 253) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 252 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf252_ok
theorem cr_251_253 (k : ℕ) (h1 : 251 ≤ k) (h2 : k < 253) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 252 then cr_251_252 k h1 h else cr_252_253 k (by omega) h2
theorem cr_253_254 (k : ℕ) (h1 : 253 ≤ k) (h2 : k < 254) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 253 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf253_ok
theorem cr_254_255 (k : ℕ) (h1 : 254 ≤ k) (h2 : k < 255) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 254 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf254_ok
theorem cr_255_256 (k : ℕ) (h1 : 255 ≤ k) (h2 : k < 256) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 255 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf255_ok
theorem cr_254_256 (k : ℕ) (h1 : 254 ≤ k) (h2 : k < 256) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 255 then cr_254_255 k h1 h else cr_255_256 k (by omega) h2
theorem cr_253_256 (k : ℕ) (h1 : 253 ≤ k) (h2 : k < 256) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 254 then cr_253_254 k h1 h else cr_254_256 k (by omega) h2
theorem cr_251_256 (k : ℕ) (h1 : 251 ≤ k) (h2 : k < 256) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 253 then cr_251_253 k h1 h else cr_253_256 k (by omega) h2
theorem cr_246_256 (k : ℕ) (h1 : 246 ≤ k) (h2 : k < 256) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 251 then cr_246_251 k h1 h else cr_251_256 k (by omega) h2
theorem cr_256_257 (k : ℕ) (h1 : 256 ≤ k) (h2 : k < 257) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 256 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf256_ok
theorem cr_257_258 (k : ℕ) (h1 : 257 ≤ k) (h2 : k < 258) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 257 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf257_ok
theorem cr_256_258 (k : ℕ) (h1 : 256 ≤ k) (h2 : k < 258) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 257 then cr_256_257 k h1 h else cr_257_258 k (by omega) h2
theorem cr_258_259 (k : ℕ) (h1 : 258 ≤ k) (h2 : k < 259) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 258 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf258_ok
theorem cr_259_260 (k : ℕ) (h1 : 259 ≤ k) (h2 : k < 260) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 259 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf259_ok
theorem cr_260_261 (k : ℕ) (h1 : 260 ≤ k) (h2 : k < 261) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 260 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf260_ok
theorem cr_259_261 (k : ℕ) (h1 : 259 ≤ k) (h2 : k < 261) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 260 then cr_259_260 k h1 h else cr_260_261 k (by omega) h2
theorem cr_258_261 (k : ℕ) (h1 : 258 ≤ k) (h2 : k < 261) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 259 then cr_258_259 k h1 h else cr_259_261 k (by omega) h2
theorem cr_256_261 (k : ℕ) (h1 : 256 ≤ k) (h2 : k < 261) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 258 then cr_256_258 k h1 h else cr_258_261 k (by omega) h2
theorem cr_261_262 (k : ℕ) (h1 : 261 ≤ k) (h2 : k < 262) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 261 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf261_ok
theorem cr_262_263 (k : ℕ) (h1 : 262 ≤ k) (h2 : k < 263) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 262 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf262_ok
theorem cr_261_263 (k : ℕ) (h1 : 261 ≤ k) (h2 : k < 263) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 262 then cr_261_262 k h1 h else cr_262_263 k (by omega) h2
theorem cr_263_264 (k : ℕ) (h1 : 263 ≤ k) (h2 : k < 264) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 263 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf263_ok
theorem cr_264_265 (k : ℕ) (h1 : 264 ≤ k) (h2 : k < 265) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 264 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf264_ok
theorem cr_265_266 (k : ℕ) (h1 : 265 ≤ k) (h2 : k < 266) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 265 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf265_ok
theorem cr_264_266 (k : ℕ) (h1 : 264 ≤ k) (h2 : k < 266) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 265 then cr_264_265 k h1 h else cr_265_266 k (by omega) h2
theorem cr_263_266 (k : ℕ) (h1 : 263 ≤ k) (h2 : k < 266) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 264 then cr_263_264 k h1 h else cr_264_266 k (by omega) h2
theorem cr_261_266 (k : ℕ) (h1 : 261 ≤ k) (h2 : k < 266) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 263 then cr_261_263 k h1 h else cr_263_266 k (by omega) h2
theorem cr_256_266 (k : ℕ) (h1 : 256 ≤ k) (h2 : k < 266) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 261 then cr_256_261 k h1 h else cr_261_266 k (by omega) h2
theorem cr_246_266 (k : ℕ) (h1 : 246 ≤ k) (h2 : k < 266) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 256 then cr_246_256 k h1 h else cr_256_266 k (by omega) h2
theorem cr_266_267 (k : ℕ) (h1 : 266 ≤ k) (h2 : k < 267) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 266 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf266_ok
theorem cr_267_268 (k : ℕ) (h1 : 267 ≤ k) (h2 : k < 268) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 267 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf267_ok
theorem cr_266_268 (k : ℕ) (h1 : 266 ≤ k) (h2 : k < 268) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 267 then cr_266_267 k h1 h else cr_267_268 k (by omega) h2
theorem cr_268_269 (k : ℕ) (h1 : 268 ≤ k) (h2 : k < 269) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 268 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf268_ok
theorem cr_269_270 (k : ℕ) (h1 : 269 ≤ k) (h2 : k < 270) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 269 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf269_ok
theorem cr_270_271 (k : ℕ) (h1 : 270 ≤ k) (h2 : k < 271) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 270 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf270_ok
theorem cr_269_271 (k : ℕ) (h1 : 269 ≤ k) (h2 : k < 271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 270 then cr_269_270 k h1 h else cr_270_271 k (by omega) h2
theorem cr_268_271 (k : ℕ) (h1 : 268 ≤ k) (h2 : k < 271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 269 then cr_268_269 k h1 h else cr_269_271 k (by omega) h2
theorem cr_266_271 (k : ℕ) (h1 : 266 ≤ k) (h2 : k < 271) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 268 then cr_266_268 k h1 h else cr_268_271 k (by omega) h2
theorem cr_271_272 (k : ℕ) (h1 : 271 ≤ k) (h2 : k < 272) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 271 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf271_ok
theorem cr_272_273 (k : ℕ) (h1 : 272 ≤ k) (h2 : k < 273) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 272 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf272_ok
theorem cr_271_273 (k : ℕ) (h1 : 271 ≤ k) (h2 : k < 273) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 272 then cr_271_272 k h1 h else cr_272_273 k (by omega) h2
theorem cr_273_274 (k : ℕ) (h1 : 273 ≤ k) (h2 : k < 274) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 273 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf273_ok
theorem cr_274_275 (k : ℕ) (h1 : 274 ≤ k) (h2 : k < 275) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 274 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf274_ok
theorem cr_275_276 (k : ℕ) (h1 : 275 ≤ k) (h2 : k < 276) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 275 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf275_ok
theorem cr_274_276 (k : ℕ) (h1 : 274 ≤ k) (h2 : k < 276) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 275 then cr_274_275 k h1 h else cr_275_276 k (by omega) h2
theorem cr_273_276 (k : ℕ) (h1 : 273 ≤ k) (h2 : k < 276) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 274 then cr_273_274 k h1 h else cr_274_276 k (by omega) h2
theorem cr_271_276 (k : ℕ) (h1 : 271 ≤ k) (h2 : k < 276) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 273 then cr_271_273 k h1 h else cr_273_276 k (by omega) h2
theorem cr_266_276 (k : ℕ) (h1 : 266 ≤ k) (h2 : k < 276) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 271 then cr_266_271 k h1 h else cr_271_276 k (by omega) h2
theorem cr_276_277 (k : ℕ) (h1 : 276 ≤ k) (h2 : k < 277) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 276 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf276_ok
theorem cr_277_278 (k : ℕ) (h1 : 277 ≤ k) (h2 : k < 278) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 277 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf277_ok
theorem cr_276_278 (k : ℕ) (h1 : 276 ≤ k) (h2 : k < 278) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 277 then cr_276_277 k h1 h else cr_277_278 k (by omega) h2
theorem cr_278_279 (k : ℕ) (h1 : 278 ≤ k) (h2 : k < 279) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 278 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf278_ok
theorem cr_279_280 (k : ℕ) (h1 : 279 ≤ k) (h2 : k < 280) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 279 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf279_ok
theorem cr_280_281 (k : ℕ) (h1 : 280 ≤ k) (h2 : k < 281) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 280 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf280_ok
theorem cr_279_281 (k : ℕ) (h1 : 279 ≤ k) (h2 : k < 281) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 280 then cr_279_280 k h1 h else cr_280_281 k (by omega) h2
theorem cr_278_281 (k : ℕ) (h1 : 278 ≤ k) (h2 : k < 281) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 279 then cr_278_279 k h1 h else cr_279_281 k (by omega) h2
theorem cr_276_281 (k : ℕ) (h1 : 276 ≤ k) (h2 : k < 281) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 278 then cr_276_278 k h1 h else cr_278_281 k (by omega) h2
theorem cr_281_282 (k : ℕ) (h1 : 281 ≤ k) (h2 : k < 282) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 281 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf281_ok
theorem cr_282_283 (k : ℕ) (h1 : 282 ≤ k) (h2 : k < 283) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 282 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf282_ok
theorem cr_283_284 (k : ℕ) (h1 : 283 ≤ k) (h2 : k < 284) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 283 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf283_ok
theorem cr_282_284 (k : ℕ) (h1 : 282 ≤ k) (h2 : k < 284) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 283 then cr_282_283 k h1 h else cr_283_284 k (by omega) h2
theorem cr_281_284 (k : ℕ) (h1 : 281 ≤ k) (h2 : k < 284) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 282 then cr_281_282 k h1 h else cr_282_284 k (by omega) h2
theorem cr_284_285 (k : ℕ) (h1 : 284 ≤ k) (h2 : k < 285) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 284 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf284_ok
theorem cr_285_286 (k : ℕ) (h1 : 285 ≤ k) (h2 : k < 286) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 285 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf285_ok
theorem cr_286_287 (k : ℕ) (h1 : 286 ≤ k) (h2 : k < 287) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 286 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf286_ok
theorem cr_285_287 (k : ℕ) (h1 : 285 ≤ k) (h2 : k < 287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 286 then cr_285_286 k h1 h else cr_286_287 k (by omega) h2
theorem cr_284_287 (k : ℕ) (h1 : 284 ≤ k) (h2 : k < 287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 285 then cr_284_285 k h1 h else cr_285_287 k (by omega) h2
theorem cr_281_287 (k : ℕ) (h1 : 281 ≤ k) (h2 : k < 287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 284 then cr_281_284 k h1 h else cr_284_287 k (by omega) h2
theorem cr_276_287 (k : ℕ) (h1 : 276 ≤ k) (h2 : k < 287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 281 then cr_276_281 k h1 h else cr_281_287 k (by omega) h2
theorem cr_266_287 (k : ℕ) (h1 : 266 ≤ k) (h2 : k < 287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 276 then cr_266_276 k h1 h else cr_276_287 k (by omega) h2
theorem cr_246_287 (k : ℕ) (h1 : 246 ≤ k) (h2 : k < 287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 266 then cr_246_266 k h1 h else cr_266_287 k (by omega) h2
theorem cr_287_288 (k : ℕ) (h1 : 287 ≤ k) (h2 : k < 288) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 287 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf287_ok
theorem cr_288_289 (k : ℕ) (h1 : 288 ≤ k) (h2 : k < 289) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 288 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf288_ok
theorem cr_287_289 (k : ℕ) (h1 : 287 ≤ k) (h2 : k < 289) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 288 then cr_287_288 k h1 h else cr_288_289 k (by omega) h2
theorem cr_289_290 (k : ℕ) (h1 : 289 ≤ k) (h2 : k < 290) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 289 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf289_ok
theorem cr_290_291 (k : ℕ) (h1 : 290 ≤ k) (h2 : k < 291) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 290 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf290_ok
theorem cr_291_292 (k : ℕ) (h1 : 291 ≤ k) (h2 : k < 292) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 291 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf291_ok
theorem cr_290_292 (k : ℕ) (h1 : 290 ≤ k) (h2 : k < 292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 291 then cr_290_291 k h1 h else cr_291_292 k (by omega) h2
theorem cr_289_292 (k : ℕ) (h1 : 289 ≤ k) (h2 : k < 292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 290 then cr_289_290 k h1 h else cr_290_292 k (by omega) h2
theorem cr_287_292 (k : ℕ) (h1 : 287 ≤ k) (h2 : k < 292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 289 then cr_287_289 k h1 h else cr_289_292 k (by omega) h2
theorem cr_292_293 (k : ℕ) (h1 : 292 ≤ k) (h2 : k < 293) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 292 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf292_ok
theorem cr_293_294 (k : ℕ) (h1 : 293 ≤ k) (h2 : k < 294) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 293 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf293_ok
theorem cr_292_294 (k : ℕ) (h1 : 292 ≤ k) (h2 : k < 294) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 293 then cr_292_293 k h1 h else cr_293_294 k (by omega) h2
theorem cr_294_295 (k : ℕ) (h1 : 294 ≤ k) (h2 : k < 295) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 294 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf294_ok
theorem cr_295_296 (k : ℕ) (h1 : 295 ≤ k) (h2 : k < 296) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 295 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf295_ok
theorem cr_296_297 (k : ℕ) (h1 : 296 ≤ k) (h2 : k < 297) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 296 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf296_ok
theorem cr_295_297 (k : ℕ) (h1 : 295 ≤ k) (h2 : k < 297) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 296 then cr_295_296 k h1 h else cr_296_297 k (by omega) h2
theorem cr_294_297 (k : ℕ) (h1 : 294 ≤ k) (h2 : k < 297) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 295 then cr_294_295 k h1 h else cr_295_297 k (by omega) h2
theorem cr_292_297 (k : ℕ) (h1 : 292 ≤ k) (h2 : k < 297) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 294 then cr_292_294 k h1 h else cr_294_297 k (by omega) h2
theorem cr_287_297 (k : ℕ) (h1 : 287 ≤ k) (h2 : k < 297) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 292 then cr_287_292 k h1 h else cr_292_297 k (by omega) h2
theorem cr_297_298 (k : ℕ) (h1 : 297 ≤ k) (h2 : k < 298) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 297 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf297_ok
theorem cr_298_299 (k : ℕ) (h1 : 298 ≤ k) (h2 : k < 299) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 298 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf298_ok
theorem cr_297_299 (k : ℕ) (h1 : 297 ≤ k) (h2 : k < 299) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 298 then cr_297_298 k h1 h else cr_298_299 k (by omega) h2
theorem cr_299_300 (k : ℕ) (h1 : 299 ≤ k) (h2 : k < 300) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 299 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf299_ok
theorem cr_300_301 (k : ℕ) (h1 : 300 ≤ k) (h2 : k < 301) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 300 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf300_ok
theorem cr_301_302 (k : ℕ) (h1 : 301 ≤ k) (h2 : k < 302) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 301 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf301_ok
theorem cr_300_302 (k : ℕ) (h1 : 300 ≤ k) (h2 : k < 302) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 301 then cr_300_301 k h1 h else cr_301_302 k (by omega) h2
theorem cr_299_302 (k : ℕ) (h1 : 299 ≤ k) (h2 : k < 302) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 300 then cr_299_300 k h1 h else cr_300_302 k (by omega) h2
theorem cr_297_302 (k : ℕ) (h1 : 297 ≤ k) (h2 : k < 302) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 299 then cr_297_299 k h1 h else cr_299_302 k (by omega) h2
theorem cr_302_303 (k : ℕ) (h1 : 302 ≤ k) (h2 : k < 303) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 302 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf302_ok
theorem cr_303_304 (k : ℕ) (h1 : 303 ≤ k) (h2 : k < 304) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 303 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf303_ok
theorem cr_302_304 (k : ℕ) (h1 : 302 ≤ k) (h2 : k < 304) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 303 then cr_302_303 k h1 h else cr_303_304 k (by omega) h2
theorem cr_304_305 (k : ℕ) (h1 : 304 ≤ k) (h2 : k < 305) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 304 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf304_ok
theorem cr_305_306 (k : ℕ) (h1 : 305 ≤ k) (h2 : k < 306) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 305 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf305_ok
theorem cr_306_307 (k : ℕ) (h1 : 306 ≤ k) (h2 : k < 307) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 306 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf306_ok
theorem cr_305_307 (k : ℕ) (h1 : 305 ≤ k) (h2 : k < 307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 306 then cr_305_306 k h1 h else cr_306_307 k (by omega) h2
theorem cr_304_307 (k : ℕ) (h1 : 304 ≤ k) (h2 : k < 307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 305 then cr_304_305 k h1 h else cr_305_307 k (by omega) h2
theorem cr_302_307 (k : ℕ) (h1 : 302 ≤ k) (h2 : k < 307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 304 then cr_302_304 k h1 h else cr_304_307 k (by omega) h2
theorem cr_297_307 (k : ℕ) (h1 : 297 ≤ k) (h2 : k < 307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 302 then cr_297_302 k h1 h else cr_302_307 k (by omega) h2
theorem cr_287_307 (k : ℕ) (h1 : 287 ≤ k) (h2 : k < 307) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 297 then cr_287_297 k h1 h else cr_297_307 k (by omega) h2
theorem cr_307_308 (k : ℕ) (h1 : 307 ≤ k) (h2 : k < 308) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 307 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf307_ok
theorem cr_308_309 (k : ℕ) (h1 : 308 ≤ k) (h2 : k < 309) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 308 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf308_ok
theorem cr_307_309 (k : ℕ) (h1 : 307 ≤ k) (h2 : k < 309) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 308 then cr_307_308 k h1 h else cr_308_309 k (by omega) h2
theorem cr_309_310 (k : ℕ) (h1 : 309 ≤ k) (h2 : k < 310) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 309 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf309_ok
theorem cr_310_311 (k : ℕ) (h1 : 310 ≤ k) (h2 : k < 311) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 310 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf310_ok
theorem cr_311_312 (k : ℕ) (h1 : 311 ≤ k) (h2 : k < 312) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 311 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf311_ok
theorem cr_310_312 (k : ℕ) (h1 : 310 ≤ k) (h2 : k < 312) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 311 then cr_310_311 k h1 h else cr_311_312 k (by omega) h2
theorem cr_309_312 (k : ℕ) (h1 : 309 ≤ k) (h2 : k < 312) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 310 then cr_309_310 k h1 h else cr_310_312 k (by omega) h2
theorem cr_307_312 (k : ℕ) (h1 : 307 ≤ k) (h2 : k < 312) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 309 then cr_307_309 k h1 h else cr_309_312 k (by omega) h2
theorem cr_312_313 (k : ℕ) (h1 : 312 ≤ k) (h2 : k < 313) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 312 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf312_ok
theorem cr_313_314 (k : ℕ) (h1 : 313 ≤ k) (h2 : k < 314) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 313 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf313_ok
theorem cr_312_314 (k : ℕ) (h1 : 312 ≤ k) (h2 : k < 314) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 313 then cr_312_313 k h1 h else cr_313_314 k (by omega) h2
theorem cr_314_315 (k : ℕ) (h1 : 314 ≤ k) (h2 : k < 315) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 314 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf314_ok
theorem cr_315_316 (k : ℕ) (h1 : 315 ≤ k) (h2 : k < 316) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 315 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf315_ok
theorem cr_316_317 (k : ℕ) (h1 : 316 ≤ k) (h2 : k < 317) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 316 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf316_ok
theorem cr_315_317 (k : ℕ) (h1 : 315 ≤ k) (h2 : k < 317) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 316 then cr_315_316 k h1 h else cr_316_317 k (by omega) h2
theorem cr_314_317 (k : ℕ) (h1 : 314 ≤ k) (h2 : k < 317) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 315 then cr_314_315 k h1 h else cr_315_317 k (by omega) h2
theorem cr_312_317 (k : ℕ) (h1 : 312 ≤ k) (h2 : k < 317) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 314 then cr_312_314 k h1 h else cr_314_317 k (by omega) h2
theorem cr_307_317 (k : ℕ) (h1 : 307 ≤ k) (h2 : k < 317) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 312 then cr_307_312 k h1 h else cr_312_317 k (by omega) h2
theorem cr_317_318 (k : ℕ) (h1 : 317 ≤ k) (h2 : k < 318) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 317 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf317_ok
theorem cr_318_319 (k : ℕ) (h1 : 318 ≤ k) (h2 : k < 319) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 318 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf318_ok
theorem cr_317_319 (k : ℕ) (h1 : 317 ≤ k) (h2 : k < 319) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 318 then cr_317_318 k h1 h else cr_318_319 k (by omega) h2
theorem cr_319_320 (k : ℕ) (h1 : 319 ≤ k) (h2 : k < 320) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 319 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf319_ok
theorem cr_320_321 (k : ℕ) (h1 : 320 ≤ k) (h2 : k < 321) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 320 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf320_ok
theorem cr_321_322 (k : ℕ) (h1 : 321 ≤ k) (h2 : k < 322) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 321 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf321_ok
theorem cr_320_322 (k : ℕ) (h1 : 320 ≤ k) (h2 : k < 322) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 321 then cr_320_321 k h1 h else cr_321_322 k (by omega) h2
theorem cr_319_322 (k : ℕ) (h1 : 319 ≤ k) (h2 : k < 322) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 320 then cr_319_320 k h1 h else cr_320_322 k (by omega) h2
theorem cr_317_322 (k : ℕ) (h1 : 317 ≤ k) (h2 : k < 322) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 319 then cr_317_319 k h1 h else cr_319_322 k (by omega) h2
theorem cr_322_323 (k : ℕ) (h1 : 322 ≤ k) (h2 : k < 323) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 322 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf322_ok
theorem cr_323_324 (k : ℕ) (h1 : 323 ≤ k) (h2 : k < 324) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 323 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf323_ok
theorem cr_324_325 (k : ℕ) (h1 : 324 ≤ k) (h2 : k < 325) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 324 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf324_ok
theorem cr_323_325 (k : ℕ) (h1 : 323 ≤ k) (h2 : k < 325) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 324 then cr_323_324 k h1 h else cr_324_325 k (by omega) h2
theorem cr_322_325 (k : ℕ) (h1 : 322 ≤ k) (h2 : k < 325) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 323 then cr_322_323 k h1 h else cr_323_325 k (by omega) h2
theorem cr_325_326 (k : ℕ) (h1 : 325 ≤ k) (h2 : k < 326) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 325 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf325_ok
theorem cr_326_327 (k : ℕ) (h1 : 326 ≤ k) (h2 : k < 327) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 326 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf326_ok
theorem cr_327_328 (k : ℕ) (h1 : 327 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 327 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf327_ok
theorem cr_326_328 (k : ℕ) (h1 : 326 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 327 then cr_326_327 k h1 h else cr_327_328 k (by omega) h2
theorem cr_325_328 (k : ℕ) (h1 : 325 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 326 then cr_325_326 k h1 h else cr_326_328 k (by omega) h2
theorem cr_322_328 (k : ℕ) (h1 : 322 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 325 then cr_322_325 k h1 h else cr_325_328 k (by omega) h2
theorem cr_317_328 (k : ℕ) (h1 : 317 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 322 then cr_317_322 k h1 h else cr_322_328 k (by omega) h2
theorem cr_307_328 (k : ℕ) (h1 : 307 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 317 then cr_307_317 k h1 h else cr_317_328 k (by omega) h2
theorem cr_287_328 (k : ℕ) (h1 : 287 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 307 then cr_287_307 k h1 h else cr_307_328 k (by omega) h2
theorem cr_246_328 (k : ℕ) (h1 : 246 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 287 then cr_246_287 k h1 h else cr_287_328 k (by omega) h2
theorem cr_164_328 (k : ℕ) (h1 : 164 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 246 then cr_164_246 k h1 h else cr_246_328 k (by omega) h2
theorem cr_0_328 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 164 then cr_0_164 k h1 h else cr_164_328 k (by omega) h2
theorem cr_328_329 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 329) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 328 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf328_ok
theorem cr_329_330 (k : ℕ) (h1 : 329 ≤ k) (h2 : k < 330) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 329 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf329_ok
theorem cr_328_330 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 330) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 329 then cr_328_329 k h1 h else cr_329_330 k (by omega) h2
theorem cr_330_331 (k : ℕ) (h1 : 330 ≤ k) (h2 : k < 331) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 330 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf330_ok
theorem cr_331_332 (k : ℕ) (h1 : 331 ≤ k) (h2 : k < 332) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 331 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf331_ok
theorem cr_332_333 (k : ℕ) (h1 : 332 ≤ k) (h2 : k < 333) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 332 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf332_ok
theorem cr_331_333 (k : ℕ) (h1 : 331 ≤ k) (h2 : k < 333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 332 then cr_331_332 k h1 h else cr_332_333 k (by omega) h2
theorem cr_330_333 (k : ℕ) (h1 : 330 ≤ k) (h2 : k < 333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 331 then cr_330_331 k h1 h else cr_331_333 k (by omega) h2
theorem cr_328_333 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 330 then cr_328_330 k h1 h else cr_330_333 k (by omega) h2
theorem cr_333_334 (k : ℕ) (h1 : 333 ≤ k) (h2 : k < 334) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 333 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf333_ok
theorem cr_334_335 (k : ℕ) (h1 : 334 ≤ k) (h2 : k < 335) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 334 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf334_ok
theorem cr_333_335 (k : ℕ) (h1 : 333 ≤ k) (h2 : k < 335) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 334 then cr_333_334 k h1 h else cr_334_335 k (by omega) h2
theorem cr_335_336 (k : ℕ) (h1 : 335 ≤ k) (h2 : k < 336) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 335 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf335_ok
theorem cr_336_337 (k : ℕ) (h1 : 336 ≤ k) (h2 : k < 337) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 336 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf336_ok
theorem cr_337_338 (k : ℕ) (h1 : 337 ≤ k) (h2 : k < 338) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 337 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf337_ok
theorem cr_336_338 (k : ℕ) (h1 : 336 ≤ k) (h2 : k < 338) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 337 then cr_336_337 k h1 h else cr_337_338 k (by omega) h2
theorem cr_335_338 (k : ℕ) (h1 : 335 ≤ k) (h2 : k < 338) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 336 then cr_335_336 k h1 h else cr_336_338 k (by omega) h2
theorem cr_333_338 (k : ℕ) (h1 : 333 ≤ k) (h2 : k < 338) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 335 then cr_333_335 k h1 h else cr_335_338 k (by omega) h2
theorem cr_328_338 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 338) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 333 then cr_328_333 k h1 h else cr_333_338 k (by omega) h2
theorem cr_338_339 (k : ℕ) (h1 : 338 ≤ k) (h2 : k < 339) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 338 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf338_ok
theorem cr_339_340 (k : ℕ) (h1 : 339 ≤ k) (h2 : k < 340) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 339 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf339_ok
theorem cr_338_340 (k : ℕ) (h1 : 338 ≤ k) (h2 : k < 340) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 339 then cr_338_339 k h1 h else cr_339_340 k (by omega) h2
theorem cr_340_341 (k : ℕ) (h1 : 340 ≤ k) (h2 : k < 341) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 340 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf340_ok
theorem cr_341_342 (k : ℕ) (h1 : 341 ≤ k) (h2 : k < 342) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 341 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf341_ok
theorem cr_342_343 (k : ℕ) (h1 : 342 ≤ k) (h2 : k < 343) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 342 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf342_ok
theorem cr_341_343 (k : ℕ) (h1 : 341 ≤ k) (h2 : k < 343) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 342 then cr_341_342 k h1 h else cr_342_343 k (by omega) h2
theorem cr_340_343 (k : ℕ) (h1 : 340 ≤ k) (h2 : k < 343) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 341 then cr_340_341 k h1 h else cr_341_343 k (by omega) h2
theorem cr_338_343 (k : ℕ) (h1 : 338 ≤ k) (h2 : k < 343) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 340 then cr_338_340 k h1 h else cr_340_343 k (by omega) h2
theorem cr_343_344 (k : ℕ) (h1 : 343 ≤ k) (h2 : k < 344) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 343 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf343_ok
theorem cr_344_345 (k : ℕ) (h1 : 344 ≤ k) (h2 : k < 345) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 344 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf344_ok
theorem cr_343_345 (k : ℕ) (h1 : 343 ≤ k) (h2 : k < 345) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 344 then cr_343_344 k h1 h else cr_344_345 k (by omega) h2
theorem cr_345_346 (k : ℕ) (h1 : 345 ≤ k) (h2 : k < 346) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 345 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf345_ok
theorem cr_346_347 (k : ℕ) (h1 : 346 ≤ k) (h2 : k < 347) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 346 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf346_ok
theorem cr_347_348 (k : ℕ) (h1 : 347 ≤ k) (h2 : k < 348) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 347 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf347_ok
theorem cr_346_348 (k : ℕ) (h1 : 346 ≤ k) (h2 : k < 348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 347 then cr_346_347 k h1 h else cr_347_348 k (by omega) h2
theorem cr_345_348 (k : ℕ) (h1 : 345 ≤ k) (h2 : k < 348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 346 then cr_345_346 k h1 h else cr_346_348 k (by omega) h2
theorem cr_343_348 (k : ℕ) (h1 : 343 ≤ k) (h2 : k < 348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 345 then cr_343_345 k h1 h else cr_345_348 k (by omega) h2
theorem cr_338_348 (k : ℕ) (h1 : 338 ≤ k) (h2 : k < 348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 343 then cr_338_343 k h1 h else cr_343_348 k (by omega) h2
theorem cr_328_348 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 338 then cr_328_338 k h1 h else cr_338_348 k (by omega) h2
theorem cr_348_349 (k : ℕ) (h1 : 348 ≤ k) (h2 : k < 349) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 348 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf348_ok
theorem cr_349_350 (k : ℕ) (h1 : 349 ≤ k) (h2 : k < 350) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 349 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf349_ok
theorem cr_348_350 (k : ℕ) (h1 : 348 ≤ k) (h2 : k < 350) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 349 then cr_348_349 k h1 h else cr_349_350 k (by omega) h2
theorem cr_350_351 (k : ℕ) (h1 : 350 ≤ k) (h2 : k < 351) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 350 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf350_ok
theorem cr_351_352 (k : ℕ) (h1 : 351 ≤ k) (h2 : k < 352) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 351 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf351_ok
theorem cr_352_353 (k : ℕ) (h1 : 352 ≤ k) (h2 : k < 353) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 352 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf352_ok
theorem cr_351_353 (k : ℕ) (h1 : 351 ≤ k) (h2 : k < 353) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 352 then cr_351_352 k h1 h else cr_352_353 k (by omega) h2
theorem cr_350_353 (k : ℕ) (h1 : 350 ≤ k) (h2 : k < 353) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 351 then cr_350_351 k h1 h else cr_351_353 k (by omega) h2
theorem cr_348_353 (k : ℕ) (h1 : 348 ≤ k) (h2 : k < 353) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 350 then cr_348_350 k h1 h else cr_350_353 k (by omega) h2
theorem cr_353_354 (k : ℕ) (h1 : 353 ≤ k) (h2 : k < 354) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 353 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf353_ok
theorem cr_354_355 (k : ℕ) (h1 : 354 ≤ k) (h2 : k < 355) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 354 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf354_ok
theorem cr_353_355 (k : ℕ) (h1 : 353 ≤ k) (h2 : k < 355) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 354 then cr_353_354 k h1 h else cr_354_355 k (by omega) h2
theorem cr_355_356 (k : ℕ) (h1 : 355 ≤ k) (h2 : k < 356) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 355 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf355_ok
theorem cr_356_357 (k : ℕ) (h1 : 356 ≤ k) (h2 : k < 357) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 356 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf356_ok
theorem cr_357_358 (k : ℕ) (h1 : 357 ≤ k) (h2 : k < 358) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 357 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf357_ok
theorem cr_356_358 (k : ℕ) (h1 : 356 ≤ k) (h2 : k < 358) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 357 then cr_356_357 k h1 h else cr_357_358 k (by omega) h2
theorem cr_355_358 (k : ℕ) (h1 : 355 ≤ k) (h2 : k < 358) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 356 then cr_355_356 k h1 h else cr_356_358 k (by omega) h2
theorem cr_353_358 (k : ℕ) (h1 : 353 ≤ k) (h2 : k < 358) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 355 then cr_353_355 k h1 h else cr_355_358 k (by omega) h2
theorem cr_348_358 (k : ℕ) (h1 : 348 ≤ k) (h2 : k < 358) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 353 then cr_348_353 k h1 h else cr_353_358 k (by omega) h2
theorem cr_358_359 (k : ℕ) (h1 : 358 ≤ k) (h2 : k < 359) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 358 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf358_ok
theorem cr_359_360 (k : ℕ) (h1 : 359 ≤ k) (h2 : k < 360) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 359 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf359_ok
theorem cr_358_360 (k : ℕ) (h1 : 358 ≤ k) (h2 : k < 360) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 359 then cr_358_359 k h1 h else cr_359_360 k (by omega) h2
theorem cr_360_361 (k : ℕ) (h1 : 360 ≤ k) (h2 : k < 361) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 360 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf360_ok
theorem cr_361_362 (k : ℕ) (h1 : 361 ≤ k) (h2 : k < 362) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 361 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf361_ok
theorem cr_362_363 (k : ℕ) (h1 : 362 ≤ k) (h2 : k < 363) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 362 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf362_ok
theorem cr_361_363 (k : ℕ) (h1 : 361 ≤ k) (h2 : k < 363) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 362 then cr_361_362 k h1 h else cr_362_363 k (by omega) h2
theorem cr_360_363 (k : ℕ) (h1 : 360 ≤ k) (h2 : k < 363) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 361 then cr_360_361 k h1 h else cr_361_363 k (by omega) h2
theorem cr_358_363 (k : ℕ) (h1 : 358 ≤ k) (h2 : k < 363) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 360 then cr_358_360 k h1 h else cr_360_363 k (by omega) h2
theorem cr_363_364 (k : ℕ) (h1 : 363 ≤ k) (h2 : k < 364) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 363 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf363_ok
theorem cr_364_365 (k : ℕ) (h1 : 364 ≤ k) (h2 : k < 365) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 364 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf364_ok
theorem cr_365_366 (k : ℕ) (h1 : 365 ≤ k) (h2 : k < 366) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 365 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf365_ok
theorem cr_364_366 (k : ℕ) (h1 : 364 ≤ k) (h2 : k < 366) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 365 then cr_364_365 k h1 h else cr_365_366 k (by omega) h2
theorem cr_363_366 (k : ℕ) (h1 : 363 ≤ k) (h2 : k < 366) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 364 then cr_363_364 k h1 h else cr_364_366 k (by omega) h2
theorem cr_366_367 (k : ℕ) (h1 : 366 ≤ k) (h2 : k < 367) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 366 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf366_ok
theorem cr_367_368 (k : ℕ) (h1 : 367 ≤ k) (h2 : k < 368) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 367 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf367_ok
theorem cr_368_369 (k : ℕ) (h1 : 368 ≤ k) (h2 : k < 369) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 368 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf368_ok
theorem cr_367_369 (k : ℕ) (h1 : 367 ≤ k) (h2 : k < 369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 368 then cr_367_368 k h1 h else cr_368_369 k (by omega) h2
theorem cr_366_369 (k : ℕ) (h1 : 366 ≤ k) (h2 : k < 369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 367 then cr_366_367 k h1 h else cr_367_369 k (by omega) h2
theorem cr_363_369 (k : ℕ) (h1 : 363 ≤ k) (h2 : k < 369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 366 then cr_363_366 k h1 h else cr_366_369 k (by omega) h2
theorem cr_358_369 (k : ℕ) (h1 : 358 ≤ k) (h2 : k < 369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 363 then cr_358_363 k h1 h else cr_363_369 k (by omega) h2
theorem cr_348_369 (k : ℕ) (h1 : 348 ≤ k) (h2 : k < 369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 358 then cr_348_358 k h1 h else cr_358_369 k (by omega) h2
theorem cr_328_369 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 348 then cr_328_348 k h1 h else cr_348_369 k (by omega) h2
theorem cr_369_370 (k : ℕ) (h1 : 369 ≤ k) (h2 : k < 370) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 369 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf369_ok
theorem cr_370_371 (k : ℕ) (h1 : 370 ≤ k) (h2 : k < 371) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 370 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf370_ok
theorem cr_369_371 (k : ℕ) (h1 : 369 ≤ k) (h2 : k < 371) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 370 then cr_369_370 k h1 h else cr_370_371 k (by omega) h2
theorem cr_371_372 (k : ℕ) (h1 : 371 ≤ k) (h2 : k < 372) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 371 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf371_ok
theorem cr_372_373 (k : ℕ) (h1 : 372 ≤ k) (h2 : k < 373) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 372 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf372_ok
theorem cr_373_374 (k : ℕ) (h1 : 373 ≤ k) (h2 : k < 374) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 373 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf373_ok
theorem cr_372_374 (k : ℕ) (h1 : 372 ≤ k) (h2 : k < 374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 373 then cr_372_373 k h1 h else cr_373_374 k (by omega) h2
theorem cr_371_374 (k : ℕ) (h1 : 371 ≤ k) (h2 : k < 374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 372 then cr_371_372 k h1 h else cr_372_374 k (by omega) h2
theorem cr_369_374 (k : ℕ) (h1 : 369 ≤ k) (h2 : k < 374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 371 then cr_369_371 k h1 h else cr_371_374 k (by omega) h2
theorem cr_374_375 (k : ℕ) (h1 : 374 ≤ k) (h2 : k < 375) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 374 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf374_ok
theorem cr_375_376 (k : ℕ) (h1 : 375 ≤ k) (h2 : k < 376) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 375 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf375_ok
theorem cr_374_376 (k : ℕ) (h1 : 374 ≤ k) (h2 : k < 376) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 375 then cr_374_375 k h1 h else cr_375_376 k (by omega) h2
theorem cr_376_377 (k : ℕ) (h1 : 376 ≤ k) (h2 : k < 377) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 376 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf376_ok
theorem cr_377_378 (k : ℕ) (h1 : 377 ≤ k) (h2 : k < 378) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 377 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf377_ok
theorem cr_378_379 (k : ℕ) (h1 : 378 ≤ k) (h2 : k < 379) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 378 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf378_ok
theorem cr_377_379 (k : ℕ) (h1 : 377 ≤ k) (h2 : k < 379) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 378 then cr_377_378 k h1 h else cr_378_379 k (by omega) h2
theorem cr_376_379 (k : ℕ) (h1 : 376 ≤ k) (h2 : k < 379) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 377 then cr_376_377 k h1 h else cr_377_379 k (by omega) h2
theorem cr_374_379 (k : ℕ) (h1 : 374 ≤ k) (h2 : k < 379) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 376 then cr_374_376 k h1 h else cr_376_379 k (by omega) h2
theorem cr_369_379 (k : ℕ) (h1 : 369 ≤ k) (h2 : k < 379) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 374 then cr_369_374 k h1 h else cr_374_379 k (by omega) h2
theorem cr_379_380 (k : ℕ) (h1 : 379 ≤ k) (h2 : k < 380) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 379 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf379_ok
theorem cr_380_381 (k : ℕ) (h1 : 380 ≤ k) (h2 : k < 381) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 380 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf380_ok
theorem cr_379_381 (k : ℕ) (h1 : 379 ≤ k) (h2 : k < 381) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 380 then cr_379_380 k h1 h else cr_380_381 k (by omega) h2
theorem cr_381_382 (k : ℕ) (h1 : 381 ≤ k) (h2 : k < 382) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 381 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf381_ok
theorem cr_382_383 (k : ℕ) (h1 : 382 ≤ k) (h2 : k < 383) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 382 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf382_ok
theorem cr_383_384 (k : ℕ) (h1 : 383 ≤ k) (h2 : k < 384) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 383 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf383_ok
theorem cr_382_384 (k : ℕ) (h1 : 382 ≤ k) (h2 : k < 384) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 383 then cr_382_383 k h1 h else cr_383_384 k (by omega) h2
theorem cr_381_384 (k : ℕ) (h1 : 381 ≤ k) (h2 : k < 384) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 382 then cr_381_382 k h1 h else cr_382_384 k (by omega) h2
theorem cr_379_384 (k : ℕ) (h1 : 379 ≤ k) (h2 : k < 384) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 381 then cr_379_381 k h1 h else cr_381_384 k (by omega) h2
theorem cr_384_385 (k : ℕ) (h1 : 384 ≤ k) (h2 : k < 385) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 384 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf384_ok
theorem cr_385_386 (k : ℕ) (h1 : 385 ≤ k) (h2 : k < 386) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 385 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf385_ok
theorem cr_384_386 (k : ℕ) (h1 : 384 ≤ k) (h2 : k < 386) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 385 then cr_384_385 k h1 h else cr_385_386 k (by omega) h2
theorem cr_386_387 (k : ℕ) (h1 : 386 ≤ k) (h2 : k < 387) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 386 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf386_ok
theorem cr_387_388 (k : ℕ) (h1 : 387 ≤ k) (h2 : k < 388) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 387 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf387_ok
theorem cr_388_389 (k : ℕ) (h1 : 388 ≤ k) (h2 : k < 389) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 388 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf388_ok
theorem cr_387_389 (k : ℕ) (h1 : 387 ≤ k) (h2 : k < 389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 388 then cr_387_388 k h1 h else cr_388_389 k (by omega) h2
theorem cr_386_389 (k : ℕ) (h1 : 386 ≤ k) (h2 : k < 389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 387 then cr_386_387 k h1 h else cr_387_389 k (by omega) h2
theorem cr_384_389 (k : ℕ) (h1 : 384 ≤ k) (h2 : k < 389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 386 then cr_384_386 k h1 h else cr_386_389 k (by omega) h2
theorem cr_379_389 (k : ℕ) (h1 : 379 ≤ k) (h2 : k < 389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 384 then cr_379_384 k h1 h else cr_384_389 k (by omega) h2
theorem cr_369_389 (k : ℕ) (h1 : 369 ≤ k) (h2 : k < 389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 379 then cr_369_379 k h1 h else cr_379_389 k (by omega) h2
theorem cr_389_390 (k : ℕ) (h1 : 389 ≤ k) (h2 : k < 390) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 389 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf389_ok
theorem cr_390_391 (k : ℕ) (h1 : 390 ≤ k) (h2 : k < 391) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 390 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf390_ok
theorem cr_389_391 (k : ℕ) (h1 : 389 ≤ k) (h2 : k < 391) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 390 then cr_389_390 k h1 h else cr_390_391 k (by omega) h2
theorem cr_391_392 (k : ℕ) (h1 : 391 ≤ k) (h2 : k < 392) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 391 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf391_ok
theorem cr_392_393 (k : ℕ) (h1 : 392 ≤ k) (h2 : k < 393) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 392 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf392_ok
theorem cr_393_394 (k : ℕ) (h1 : 393 ≤ k) (h2 : k < 394) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 393 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf393_ok
theorem cr_392_394 (k : ℕ) (h1 : 392 ≤ k) (h2 : k < 394) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 393 then cr_392_393 k h1 h else cr_393_394 k (by omega) h2
theorem cr_391_394 (k : ℕ) (h1 : 391 ≤ k) (h2 : k < 394) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 392 then cr_391_392 k h1 h else cr_392_394 k (by omega) h2
theorem cr_389_394 (k : ℕ) (h1 : 389 ≤ k) (h2 : k < 394) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 391 then cr_389_391 k h1 h else cr_391_394 k (by omega) h2
theorem cr_394_395 (k : ℕ) (h1 : 394 ≤ k) (h2 : k < 395) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 394 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf394_ok
theorem cr_395_396 (k : ℕ) (h1 : 395 ≤ k) (h2 : k < 396) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 395 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf395_ok
theorem cr_394_396 (k : ℕ) (h1 : 394 ≤ k) (h2 : k < 396) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 395 then cr_394_395 k h1 h else cr_395_396 k (by omega) h2
theorem cr_396_397 (k : ℕ) (h1 : 396 ≤ k) (h2 : k < 397) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 396 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf396_ok
theorem cr_397_398 (k : ℕ) (h1 : 397 ≤ k) (h2 : k < 398) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 397 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf397_ok
theorem cr_398_399 (k : ℕ) (h1 : 398 ≤ k) (h2 : k < 399) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 398 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf398_ok
theorem cr_397_399 (k : ℕ) (h1 : 397 ≤ k) (h2 : k < 399) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 398 then cr_397_398 k h1 h else cr_398_399 k (by omega) h2
theorem cr_396_399 (k : ℕ) (h1 : 396 ≤ k) (h2 : k < 399) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 397 then cr_396_397 k h1 h else cr_397_399 k (by omega) h2
theorem cr_394_399 (k : ℕ) (h1 : 394 ≤ k) (h2 : k < 399) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 396 then cr_394_396 k h1 h else cr_396_399 k (by omega) h2
theorem cr_389_399 (k : ℕ) (h1 : 389 ≤ k) (h2 : k < 399) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 394 then cr_389_394 k h1 h else cr_394_399 k (by omega) h2
theorem cr_399_400 (k : ℕ) (h1 : 399 ≤ k) (h2 : k < 400) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 399 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf399_ok
theorem cr_400_401 (k : ℕ) (h1 : 400 ≤ k) (h2 : k < 401) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 400 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf400_ok
theorem cr_399_401 (k : ℕ) (h1 : 399 ≤ k) (h2 : k < 401) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 400 then cr_399_400 k h1 h else cr_400_401 k (by omega) h2
theorem cr_401_402 (k : ℕ) (h1 : 401 ≤ k) (h2 : k < 402) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 401 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf401_ok
theorem cr_402_403 (k : ℕ) (h1 : 402 ≤ k) (h2 : k < 403) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 402 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf402_ok
theorem cr_403_404 (k : ℕ) (h1 : 403 ≤ k) (h2 : k < 404) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 403 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf403_ok
theorem cr_402_404 (k : ℕ) (h1 : 402 ≤ k) (h2 : k < 404) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 403 then cr_402_403 k h1 h else cr_403_404 k (by omega) h2
theorem cr_401_404 (k : ℕ) (h1 : 401 ≤ k) (h2 : k < 404) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 402 then cr_401_402 k h1 h else cr_402_404 k (by omega) h2
theorem cr_399_404 (k : ℕ) (h1 : 399 ≤ k) (h2 : k < 404) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 401 then cr_399_401 k h1 h else cr_401_404 k (by omega) h2
theorem cr_404_405 (k : ℕ) (h1 : 404 ≤ k) (h2 : k < 405) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 404 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf404_ok
theorem cr_405_406 (k : ℕ) (h1 : 405 ≤ k) (h2 : k < 406) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 405 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf405_ok
theorem cr_406_407 (k : ℕ) (h1 : 406 ≤ k) (h2 : k < 407) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 406 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf406_ok
theorem cr_405_407 (k : ℕ) (h1 : 405 ≤ k) (h2 : k < 407) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 406 then cr_405_406 k h1 h else cr_406_407 k (by omega) h2
theorem cr_404_407 (k : ℕ) (h1 : 404 ≤ k) (h2 : k < 407) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 405 then cr_404_405 k h1 h else cr_405_407 k (by omega) h2
theorem cr_407_408 (k : ℕ) (h1 : 407 ≤ k) (h2 : k < 408) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 407 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf407_ok
theorem cr_408_409 (k : ℕ) (h1 : 408 ≤ k) (h2 : k < 409) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 408 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf408_ok
theorem cr_409_410 (k : ℕ) (h1 : 409 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 409 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf409_ok
theorem cr_408_410 (k : ℕ) (h1 : 408 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 409 then cr_408_409 k h1 h else cr_409_410 k (by omega) h2
theorem cr_407_410 (k : ℕ) (h1 : 407 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 408 then cr_407_408 k h1 h else cr_408_410 k (by omega) h2
theorem cr_404_410 (k : ℕ) (h1 : 404 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 407 then cr_404_407 k h1 h else cr_407_410 k (by omega) h2
theorem cr_399_410 (k : ℕ) (h1 : 399 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 404 then cr_399_404 k h1 h else cr_404_410 k (by omega) h2
theorem cr_389_410 (k : ℕ) (h1 : 389 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 399 then cr_389_399 k h1 h else cr_399_410 k (by omega) h2
theorem cr_369_410 (k : ℕ) (h1 : 369 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 389 then cr_369_389 k h1 h else cr_389_410 k (by omega) h2
theorem cr_328_410 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 369 then cr_328_369 k h1 h else cr_369_410 k (by omega) h2
theorem cr_410_411 (k : ℕ) (h1 : 410 ≤ k) (h2 : k < 411) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 410 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf410_ok
theorem cr_411_412 (k : ℕ) (h1 : 411 ≤ k) (h2 : k < 412) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 411 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf411_ok
theorem cr_410_412 (k : ℕ) (h1 : 410 ≤ k) (h2 : k < 412) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 411 then cr_410_411 k h1 h else cr_411_412 k (by omega) h2
theorem cr_412_413 (k : ℕ) (h1 : 412 ≤ k) (h2 : k < 413) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 412 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf412_ok
theorem cr_413_414 (k : ℕ) (h1 : 413 ≤ k) (h2 : k < 414) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 413 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf413_ok
theorem cr_414_415 (k : ℕ) (h1 : 414 ≤ k) (h2 : k < 415) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 414 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf414_ok
theorem cr_413_415 (k : ℕ) (h1 : 413 ≤ k) (h2 : k < 415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 414 then cr_413_414 k h1 h else cr_414_415 k (by omega) h2
theorem cr_412_415 (k : ℕ) (h1 : 412 ≤ k) (h2 : k < 415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 413 then cr_412_413 k h1 h else cr_413_415 k (by omega) h2
theorem cr_410_415 (k : ℕ) (h1 : 410 ≤ k) (h2 : k < 415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 412 then cr_410_412 k h1 h else cr_412_415 k (by omega) h2
theorem cr_415_416 (k : ℕ) (h1 : 415 ≤ k) (h2 : k < 416) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 415 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf415_ok
theorem cr_416_417 (k : ℕ) (h1 : 416 ≤ k) (h2 : k < 417) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 416 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf416_ok
theorem cr_415_417 (k : ℕ) (h1 : 415 ≤ k) (h2 : k < 417) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 416 then cr_415_416 k h1 h else cr_416_417 k (by omega) h2
theorem cr_417_418 (k : ℕ) (h1 : 417 ≤ k) (h2 : k < 418) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 417 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf417_ok
theorem cr_418_419 (k : ℕ) (h1 : 418 ≤ k) (h2 : k < 419) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 418 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf418_ok
theorem cr_419_420 (k : ℕ) (h1 : 419 ≤ k) (h2 : k < 420) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 419 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf419_ok
theorem cr_418_420 (k : ℕ) (h1 : 418 ≤ k) (h2 : k < 420) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 419 then cr_418_419 k h1 h else cr_419_420 k (by omega) h2
theorem cr_417_420 (k : ℕ) (h1 : 417 ≤ k) (h2 : k < 420) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 418 then cr_417_418 k h1 h else cr_418_420 k (by omega) h2
theorem cr_415_420 (k : ℕ) (h1 : 415 ≤ k) (h2 : k < 420) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 417 then cr_415_417 k h1 h else cr_417_420 k (by omega) h2
theorem cr_410_420 (k : ℕ) (h1 : 410 ≤ k) (h2 : k < 420) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 415 then cr_410_415 k h1 h else cr_415_420 k (by omega) h2
theorem cr_420_421 (k : ℕ) (h1 : 420 ≤ k) (h2 : k < 421) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 420 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf420_ok
theorem cr_421_422 (k : ℕ) (h1 : 421 ≤ k) (h2 : k < 422) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 421 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf421_ok
theorem cr_420_422 (k : ℕ) (h1 : 420 ≤ k) (h2 : k < 422) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 421 then cr_420_421 k h1 h else cr_421_422 k (by omega) h2
theorem cr_422_423 (k : ℕ) (h1 : 422 ≤ k) (h2 : k < 423) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 422 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf422_ok
theorem cr_423_424 (k : ℕ) (h1 : 423 ≤ k) (h2 : k < 424) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 423 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf423_ok
theorem cr_424_425 (k : ℕ) (h1 : 424 ≤ k) (h2 : k < 425) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 424 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf424_ok
theorem cr_423_425 (k : ℕ) (h1 : 423 ≤ k) (h2 : k < 425) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 424 then cr_423_424 k h1 h else cr_424_425 k (by omega) h2
theorem cr_422_425 (k : ℕ) (h1 : 422 ≤ k) (h2 : k < 425) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 423 then cr_422_423 k h1 h else cr_423_425 k (by omega) h2
theorem cr_420_425 (k : ℕ) (h1 : 420 ≤ k) (h2 : k < 425) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 422 then cr_420_422 k h1 h else cr_422_425 k (by omega) h2
theorem cr_425_426 (k : ℕ) (h1 : 425 ≤ k) (h2 : k < 426) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 425 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf425_ok
theorem cr_426_427 (k : ℕ) (h1 : 426 ≤ k) (h2 : k < 427) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 426 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf426_ok
theorem cr_425_427 (k : ℕ) (h1 : 425 ≤ k) (h2 : k < 427) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 426 then cr_425_426 k h1 h else cr_426_427 k (by omega) h2
theorem cr_427_428 (k : ℕ) (h1 : 427 ≤ k) (h2 : k < 428) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 427 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf427_ok
theorem cr_428_429 (k : ℕ) (h1 : 428 ≤ k) (h2 : k < 429) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 428 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf428_ok
theorem cr_429_430 (k : ℕ) (h1 : 429 ≤ k) (h2 : k < 430) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 429 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf429_ok
theorem cr_428_430 (k : ℕ) (h1 : 428 ≤ k) (h2 : k < 430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 429 then cr_428_429 k h1 h else cr_429_430 k (by omega) h2
theorem cr_427_430 (k : ℕ) (h1 : 427 ≤ k) (h2 : k < 430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 428 then cr_427_428 k h1 h else cr_428_430 k (by omega) h2
theorem cr_425_430 (k : ℕ) (h1 : 425 ≤ k) (h2 : k < 430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 427 then cr_425_427 k h1 h else cr_427_430 k (by omega) h2
theorem cr_420_430 (k : ℕ) (h1 : 420 ≤ k) (h2 : k < 430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 425 then cr_420_425 k h1 h else cr_425_430 k (by omega) h2
theorem cr_410_430 (k : ℕ) (h1 : 410 ≤ k) (h2 : k < 430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 420 then cr_410_420 k h1 h else cr_420_430 k (by omega) h2
theorem cr_430_431 (k : ℕ) (h1 : 430 ≤ k) (h2 : k < 431) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 430 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf430_ok
theorem cr_431_432 (k : ℕ) (h1 : 431 ≤ k) (h2 : k < 432) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 431 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf431_ok
theorem cr_430_432 (k : ℕ) (h1 : 430 ≤ k) (h2 : k < 432) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 431 then cr_430_431 k h1 h else cr_431_432 k (by omega) h2
theorem cr_432_433 (k : ℕ) (h1 : 432 ≤ k) (h2 : k < 433) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 432 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf432_ok
theorem cr_433_434 (k : ℕ) (h1 : 433 ≤ k) (h2 : k < 434) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 433 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf433_ok
theorem cr_434_435 (k : ℕ) (h1 : 434 ≤ k) (h2 : k < 435) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 434 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf434_ok
theorem cr_433_435 (k : ℕ) (h1 : 433 ≤ k) (h2 : k < 435) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 434 then cr_433_434 k h1 h else cr_434_435 k (by omega) h2
theorem cr_432_435 (k : ℕ) (h1 : 432 ≤ k) (h2 : k < 435) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 433 then cr_432_433 k h1 h else cr_433_435 k (by omega) h2
theorem cr_430_435 (k : ℕ) (h1 : 430 ≤ k) (h2 : k < 435) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 432 then cr_430_432 k h1 h else cr_432_435 k (by omega) h2
theorem cr_435_436 (k : ℕ) (h1 : 435 ≤ k) (h2 : k < 436) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 435 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf435_ok
theorem cr_436_437 (k : ℕ) (h1 : 436 ≤ k) (h2 : k < 437) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 436 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf436_ok
theorem cr_435_437 (k : ℕ) (h1 : 435 ≤ k) (h2 : k < 437) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 436 then cr_435_436 k h1 h else cr_436_437 k (by omega) h2
theorem cr_437_438 (k : ℕ) (h1 : 437 ≤ k) (h2 : k < 438) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 437 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf437_ok
theorem cr_438_439 (k : ℕ) (h1 : 438 ≤ k) (h2 : k < 439) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 438 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf438_ok
theorem cr_439_440 (k : ℕ) (h1 : 439 ≤ k) (h2 : k < 440) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 439 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf439_ok
theorem cr_438_440 (k : ℕ) (h1 : 438 ≤ k) (h2 : k < 440) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 439 then cr_438_439 k h1 h else cr_439_440 k (by omega) h2
theorem cr_437_440 (k : ℕ) (h1 : 437 ≤ k) (h2 : k < 440) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 438 then cr_437_438 k h1 h else cr_438_440 k (by omega) h2
theorem cr_435_440 (k : ℕ) (h1 : 435 ≤ k) (h2 : k < 440) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 437 then cr_435_437 k h1 h else cr_437_440 k (by omega) h2
theorem cr_430_440 (k : ℕ) (h1 : 430 ≤ k) (h2 : k < 440) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 435 then cr_430_435 k h1 h else cr_435_440 k (by omega) h2
theorem cr_440_441 (k : ℕ) (h1 : 440 ≤ k) (h2 : k < 441) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 440 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf440_ok
theorem cr_441_442 (k : ℕ) (h1 : 441 ≤ k) (h2 : k < 442) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 441 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf441_ok
theorem cr_440_442 (k : ℕ) (h1 : 440 ≤ k) (h2 : k < 442) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 441 then cr_440_441 k h1 h else cr_441_442 k (by omega) h2
theorem cr_442_443 (k : ℕ) (h1 : 442 ≤ k) (h2 : k < 443) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 442 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf442_ok
theorem cr_443_444 (k : ℕ) (h1 : 443 ≤ k) (h2 : k < 444) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 443 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf443_ok
theorem cr_444_445 (k : ℕ) (h1 : 444 ≤ k) (h2 : k < 445) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 444 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf444_ok
theorem cr_443_445 (k : ℕ) (h1 : 443 ≤ k) (h2 : k < 445) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 444 then cr_443_444 k h1 h else cr_444_445 k (by omega) h2
theorem cr_442_445 (k : ℕ) (h1 : 442 ≤ k) (h2 : k < 445) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 443 then cr_442_443 k h1 h else cr_443_445 k (by omega) h2
theorem cr_440_445 (k : ℕ) (h1 : 440 ≤ k) (h2 : k < 445) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 442 then cr_440_442 k h1 h else cr_442_445 k (by omega) h2
theorem cr_445_446 (k : ℕ) (h1 : 445 ≤ k) (h2 : k < 446) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 445 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf445_ok
theorem cr_446_447 (k : ℕ) (h1 : 446 ≤ k) (h2 : k < 447) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 446 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf446_ok
theorem cr_447_448 (k : ℕ) (h1 : 447 ≤ k) (h2 : k < 448) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 447 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf447_ok
theorem cr_446_448 (k : ℕ) (h1 : 446 ≤ k) (h2 : k < 448) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 447 then cr_446_447 k h1 h else cr_447_448 k (by omega) h2
theorem cr_445_448 (k : ℕ) (h1 : 445 ≤ k) (h2 : k < 448) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 446 then cr_445_446 k h1 h else cr_446_448 k (by omega) h2
theorem cr_448_449 (k : ℕ) (h1 : 448 ≤ k) (h2 : k < 449) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 448 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf448_ok
theorem cr_449_450 (k : ℕ) (h1 : 449 ≤ k) (h2 : k < 450) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 449 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf449_ok
theorem cr_450_451 (k : ℕ) (h1 : 450 ≤ k) (h2 : k < 451) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 450 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf450_ok
theorem cr_449_451 (k : ℕ) (h1 : 449 ≤ k) (h2 : k < 451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 450 then cr_449_450 k h1 h else cr_450_451 k (by omega) h2
theorem cr_448_451 (k : ℕ) (h1 : 448 ≤ k) (h2 : k < 451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 449 then cr_448_449 k h1 h else cr_449_451 k (by omega) h2
theorem cr_445_451 (k : ℕ) (h1 : 445 ≤ k) (h2 : k < 451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 448 then cr_445_448 k h1 h else cr_448_451 k (by omega) h2
theorem cr_440_451 (k : ℕ) (h1 : 440 ≤ k) (h2 : k < 451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 445 then cr_440_445 k h1 h else cr_445_451 k (by omega) h2
theorem cr_430_451 (k : ℕ) (h1 : 430 ≤ k) (h2 : k < 451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 440 then cr_430_440 k h1 h else cr_440_451 k (by omega) h2
theorem cr_410_451 (k : ℕ) (h1 : 410 ≤ k) (h2 : k < 451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 430 then cr_410_430 k h1 h else cr_430_451 k (by omega) h2
theorem cr_451_452 (k : ℕ) (h1 : 451 ≤ k) (h2 : k < 452) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 451 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf451_ok
theorem cr_452_453 (k : ℕ) (h1 : 452 ≤ k) (h2 : k < 453) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 452 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf452_ok
theorem cr_451_453 (k : ℕ) (h1 : 451 ≤ k) (h2 : k < 453) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 452 then cr_451_452 k h1 h else cr_452_453 k (by omega) h2
theorem cr_453_454 (k : ℕ) (h1 : 453 ≤ k) (h2 : k < 454) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 453 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf453_ok
theorem cr_454_455 (k : ℕ) (h1 : 454 ≤ k) (h2 : k < 455) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 454 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf454_ok
theorem cr_455_456 (k : ℕ) (h1 : 455 ≤ k) (h2 : k < 456) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 455 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf455_ok
theorem cr_454_456 (k : ℕ) (h1 : 454 ≤ k) (h2 : k < 456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 455 then cr_454_455 k h1 h else cr_455_456 k (by omega) h2
theorem cr_453_456 (k : ℕ) (h1 : 453 ≤ k) (h2 : k < 456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 454 then cr_453_454 k h1 h else cr_454_456 k (by omega) h2
theorem cr_451_456 (k : ℕ) (h1 : 451 ≤ k) (h2 : k < 456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 453 then cr_451_453 k h1 h else cr_453_456 k (by omega) h2
theorem cr_456_457 (k : ℕ) (h1 : 456 ≤ k) (h2 : k < 457) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 456 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf456_ok
theorem cr_457_458 (k : ℕ) (h1 : 457 ≤ k) (h2 : k < 458) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 457 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf457_ok
theorem cr_456_458 (k : ℕ) (h1 : 456 ≤ k) (h2 : k < 458) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 457 then cr_456_457 k h1 h else cr_457_458 k (by omega) h2
theorem cr_458_459 (k : ℕ) (h1 : 458 ≤ k) (h2 : k < 459) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 458 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf458_ok
theorem cr_459_460 (k : ℕ) (h1 : 459 ≤ k) (h2 : k < 460) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 459 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf459_ok
theorem cr_460_461 (k : ℕ) (h1 : 460 ≤ k) (h2 : k < 461) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 460 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf460_ok
theorem cr_459_461 (k : ℕ) (h1 : 459 ≤ k) (h2 : k < 461) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 460 then cr_459_460 k h1 h else cr_460_461 k (by omega) h2
theorem cr_458_461 (k : ℕ) (h1 : 458 ≤ k) (h2 : k < 461) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 459 then cr_458_459 k h1 h else cr_459_461 k (by omega) h2
theorem cr_456_461 (k : ℕ) (h1 : 456 ≤ k) (h2 : k < 461) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 458 then cr_456_458 k h1 h else cr_458_461 k (by omega) h2
theorem cr_451_461 (k : ℕ) (h1 : 451 ≤ k) (h2 : k < 461) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 456 then cr_451_456 k h1 h else cr_456_461 k (by omega) h2
theorem cr_461_462 (k : ℕ) (h1 : 461 ≤ k) (h2 : k < 462) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 461 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf461_ok
theorem cr_462_463 (k : ℕ) (h1 : 462 ≤ k) (h2 : k < 463) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 462 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf462_ok
theorem cr_461_463 (k : ℕ) (h1 : 461 ≤ k) (h2 : k < 463) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 462 then cr_461_462 k h1 h else cr_462_463 k (by omega) h2
theorem cr_463_464 (k : ℕ) (h1 : 463 ≤ k) (h2 : k < 464) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 463 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf463_ok
theorem cr_464_465 (k : ℕ) (h1 : 464 ≤ k) (h2 : k < 465) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 464 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf464_ok
theorem cr_465_466 (k : ℕ) (h1 : 465 ≤ k) (h2 : k < 466) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 465 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf465_ok
theorem cr_464_466 (k : ℕ) (h1 : 464 ≤ k) (h2 : k < 466) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 465 then cr_464_465 k h1 h else cr_465_466 k (by omega) h2
theorem cr_463_466 (k : ℕ) (h1 : 463 ≤ k) (h2 : k < 466) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 464 then cr_463_464 k h1 h else cr_464_466 k (by omega) h2
theorem cr_461_466 (k : ℕ) (h1 : 461 ≤ k) (h2 : k < 466) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 463 then cr_461_463 k h1 h else cr_463_466 k (by omega) h2
theorem cr_466_467 (k : ℕ) (h1 : 466 ≤ k) (h2 : k < 467) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 466 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf466_ok
theorem cr_467_468 (k : ℕ) (h1 : 467 ≤ k) (h2 : k < 468) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 467 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf467_ok
theorem cr_466_468 (k : ℕ) (h1 : 466 ≤ k) (h2 : k < 468) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 467 then cr_466_467 k h1 h else cr_467_468 k (by omega) h2
theorem cr_468_469 (k : ℕ) (h1 : 468 ≤ k) (h2 : k < 469) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 468 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf468_ok
theorem cr_469_470 (k : ℕ) (h1 : 469 ≤ k) (h2 : k < 470) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 469 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf469_ok
theorem cr_470_471 (k : ℕ) (h1 : 470 ≤ k) (h2 : k < 471) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 470 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf470_ok
theorem cr_469_471 (k : ℕ) (h1 : 469 ≤ k) (h2 : k < 471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 470 then cr_469_470 k h1 h else cr_470_471 k (by omega) h2
theorem cr_468_471 (k : ℕ) (h1 : 468 ≤ k) (h2 : k < 471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 469 then cr_468_469 k h1 h else cr_469_471 k (by omega) h2
theorem cr_466_471 (k : ℕ) (h1 : 466 ≤ k) (h2 : k < 471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 468 then cr_466_468 k h1 h else cr_468_471 k (by omega) h2
theorem cr_461_471 (k : ℕ) (h1 : 461 ≤ k) (h2 : k < 471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 466 then cr_461_466 k h1 h else cr_466_471 k (by omega) h2
theorem cr_451_471 (k : ℕ) (h1 : 451 ≤ k) (h2 : k < 471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 461 then cr_451_461 k h1 h else cr_461_471 k (by omega) h2
theorem cr_471_472 (k : ℕ) (h1 : 471 ≤ k) (h2 : k < 472) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 471 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf471_ok
theorem cr_472_473 (k : ℕ) (h1 : 472 ≤ k) (h2 : k < 473) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 472 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf472_ok
theorem cr_471_473 (k : ℕ) (h1 : 471 ≤ k) (h2 : k < 473) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 472 then cr_471_472 k h1 h else cr_472_473 k (by omega) h2
theorem cr_473_474 (k : ℕ) (h1 : 473 ≤ k) (h2 : k < 474) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 473 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf473_ok
theorem cr_474_475 (k : ℕ) (h1 : 474 ≤ k) (h2 : k < 475) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 474 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf474_ok
theorem cr_475_476 (k : ℕ) (h1 : 475 ≤ k) (h2 : k < 476) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 475 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf475_ok
theorem cr_474_476 (k : ℕ) (h1 : 474 ≤ k) (h2 : k < 476) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 475 then cr_474_475 k h1 h else cr_475_476 k (by omega) h2
theorem cr_473_476 (k : ℕ) (h1 : 473 ≤ k) (h2 : k < 476) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 474 then cr_473_474 k h1 h else cr_474_476 k (by omega) h2
theorem cr_471_476 (k : ℕ) (h1 : 471 ≤ k) (h2 : k < 476) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 473 then cr_471_473 k h1 h else cr_473_476 k (by omega) h2
theorem cr_476_477 (k : ℕ) (h1 : 476 ≤ k) (h2 : k < 477) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 476 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf476_ok
theorem cr_477_478 (k : ℕ) (h1 : 477 ≤ k) (h2 : k < 478) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 477 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf477_ok
theorem cr_476_478 (k : ℕ) (h1 : 476 ≤ k) (h2 : k < 478) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 477 then cr_476_477 k h1 h else cr_477_478 k (by omega) h2
theorem cr_478_479 (k : ℕ) (h1 : 478 ≤ k) (h2 : k < 479) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 478 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf478_ok
theorem cr_479_480 (k : ℕ) (h1 : 479 ≤ k) (h2 : k < 480) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 479 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf479_ok
theorem cr_480_481 (k : ℕ) (h1 : 480 ≤ k) (h2 : k < 481) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 480 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf480_ok
theorem cr_479_481 (k : ℕ) (h1 : 479 ≤ k) (h2 : k < 481) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 480 then cr_479_480 k h1 h else cr_480_481 k (by omega) h2
theorem cr_478_481 (k : ℕ) (h1 : 478 ≤ k) (h2 : k < 481) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 479 then cr_478_479 k h1 h else cr_479_481 k (by omega) h2
theorem cr_476_481 (k : ℕ) (h1 : 476 ≤ k) (h2 : k < 481) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 478 then cr_476_478 k h1 h else cr_478_481 k (by omega) h2
theorem cr_471_481 (k : ℕ) (h1 : 471 ≤ k) (h2 : k < 481) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 476 then cr_471_476 k h1 h else cr_476_481 k (by omega) h2
theorem cr_481_482 (k : ℕ) (h1 : 481 ≤ k) (h2 : k < 482) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 481 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf481_ok
theorem cr_482_483 (k : ℕ) (h1 : 482 ≤ k) (h2 : k < 483) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 482 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf482_ok
theorem cr_481_483 (k : ℕ) (h1 : 481 ≤ k) (h2 : k < 483) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 482 then cr_481_482 k h1 h else cr_482_483 k (by omega) h2
theorem cr_483_484 (k : ℕ) (h1 : 483 ≤ k) (h2 : k < 484) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 483 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf483_ok
theorem cr_484_485 (k : ℕ) (h1 : 484 ≤ k) (h2 : k < 485) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 484 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf484_ok
theorem cr_485_486 (k : ℕ) (h1 : 485 ≤ k) (h2 : k < 486) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 485 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf485_ok
theorem cr_484_486 (k : ℕ) (h1 : 484 ≤ k) (h2 : k < 486) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 485 then cr_484_485 k h1 h else cr_485_486 k (by omega) h2
theorem cr_483_486 (k : ℕ) (h1 : 483 ≤ k) (h2 : k < 486) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 484 then cr_483_484 k h1 h else cr_484_486 k (by omega) h2
theorem cr_481_486 (k : ℕ) (h1 : 481 ≤ k) (h2 : k < 486) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 483 then cr_481_483 k h1 h else cr_483_486 k (by omega) h2
theorem cr_486_487 (k : ℕ) (h1 : 486 ≤ k) (h2 : k < 487) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 486 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf486_ok
theorem cr_487_488 (k : ℕ) (h1 : 487 ≤ k) (h2 : k < 488) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 487 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf487_ok
theorem cr_488_489 (k : ℕ) (h1 : 488 ≤ k) (h2 : k < 489) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 488 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf488_ok
theorem cr_487_489 (k : ℕ) (h1 : 487 ≤ k) (h2 : k < 489) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 488 then cr_487_488 k h1 h else cr_488_489 k (by omega) h2
theorem cr_486_489 (k : ℕ) (h1 : 486 ≤ k) (h2 : k < 489) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 487 then cr_486_487 k h1 h else cr_487_489 k (by omega) h2
theorem cr_489_490 (k : ℕ) (h1 : 489 ≤ k) (h2 : k < 490) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 489 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf489_ok
theorem cr_490_491 (k : ℕ) (h1 : 490 ≤ k) (h2 : k < 491) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 490 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf490_ok
theorem cr_491_492 (k : ℕ) (h1 : 491 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 491 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf491_ok
theorem cr_490_492 (k : ℕ) (h1 : 490 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 491 then cr_490_491 k h1 h else cr_491_492 k (by omega) h2
theorem cr_489_492 (k : ℕ) (h1 : 489 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 490 then cr_489_490 k h1 h else cr_490_492 k (by omega) h2
theorem cr_486_492 (k : ℕ) (h1 : 486 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 489 then cr_486_489 k h1 h else cr_489_492 k (by omega) h2
theorem cr_481_492 (k : ℕ) (h1 : 481 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 486 then cr_481_486 k h1 h else cr_486_492 k (by omega) h2
theorem cr_471_492 (k : ℕ) (h1 : 471 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 481 then cr_471_481 k h1 h else cr_481_492 k (by omega) h2
theorem cr_451_492 (k : ℕ) (h1 : 451 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 471 then cr_451_471 k h1 h else cr_471_492 k (by omega) h2
theorem cr_410_492 (k : ℕ) (h1 : 410 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 451 then cr_410_451 k h1 h else cr_451_492 k (by omega) h2
theorem cr_328_492 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 410 then cr_328_410 k h1 h else cr_410_492 k (by omega) h2
theorem cr_492_493 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 493) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 492 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf492_ok
theorem cr_493_494 (k : ℕ) (h1 : 493 ≤ k) (h2 : k < 494) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 493 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf493_ok
theorem cr_492_494 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 494) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 493 then cr_492_493 k h1 h else cr_493_494 k (by omega) h2
theorem cr_494_495 (k : ℕ) (h1 : 494 ≤ k) (h2 : k < 495) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 494 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf494_ok
theorem cr_495_496 (k : ℕ) (h1 : 495 ≤ k) (h2 : k < 496) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 495 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf495_ok
theorem cr_496_497 (k : ℕ) (h1 : 496 ≤ k) (h2 : k < 497) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 496 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf496_ok
theorem cr_495_497 (k : ℕ) (h1 : 495 ≤ k) (h2 : k < 497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 496 then cr_495_496 k h1 h else cr_496_497 k (by omega) h2
theorem cr_494_497 (k : ℕ) (h1 : 494 ≤ k) (h2 : k < 497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 495 then cr_494_495 k h1 h else cr_495_497 k (by omega) h2
theorem cr_492_497 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 494 then cr_492_494 k h1 h else cr_494_497 k (by omega) h2
theorem cr_497_498 (k : ℕ) (h1 : 497 ≤ k) (h2 : k < 498) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 497 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf497_ok
theorem cr_498_499 (k : ℕ) (h1 : 498 ≤ k) (h2 : k < 499) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 498 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf498_ok
theorem cr_497_499 (k : ℕ) (h1 : 497 ≤ k) (h2 : k < 499) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 498 then cr_497_498 k h1 h else cr_498_499 k (by omega) h2
theorem cr_499_500 (k : ℕ) (h1 : 499 ≤ k) (h2 : k < 500) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 499 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf499_ok
theorem cr_500_501 (k : ℕ) (h1 : 500 ≤ k) (h2 : k < 501) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 500 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf500_ok
theorem cr_501_502 (k : ℕ) (h1 : 501 ≤ k) (h2 : k < 502) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 501 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf501_ok
theorem cr_500_502 (k : ℕ) (h1 : 500 ≤ k) (h2 : k < 502) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 501 then cr_500_501 k h1 h else cr_501_502 k (by omega) h2
theorem cr_499_502 (k : ℕ) (h1 : 499 ≤ k) (h2 : k < 502) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 500 then cr_499_500 k h1 h else cr_500_502 k (by omega) h2
theorem cr_497_502 (k : ℕ) (h1 : 497 ≤ k) (h2 : k < 502) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 499 then cr_497_499 k h1 h else cr_499_502 k (by omega) h2
theorem cr_492_502 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 502) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 497 then cr_492_497 k h1 h else cr_497_502 k (by omega) h2
theorem cr_502_503 (k : ℕ) (h1 : 502 ≤ k) (h2 : k < 503) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 502 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf502_ok
theorem cr_503_504 (k : ℕ) (h1 : 503 ≤ k) (h2 : k < 504) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 503 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf503_ok
theorem cr_502_504 (k : ℕ) (h1 : 502 ≤ k) (h2 : k < 504) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 503 then cr_502_503 k h1 h else cr_503_504 k (by omega) h2
theorem cr_504_505 (k : ℕ) (h1 : 504 ≤ k) (h2 : k < 505) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 504 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf504_ok
theorem cr_505_506 (k : ℕ) (h1 : 505 ≤ k) (h2 : k < 506) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 505 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf505_ok
theorem cr_506_507 (k : ℕ) (h1 : 506 ≤ k) (h2 : k < 507) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 506 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf506_ok
theorem cr_505_507 (k : ℕ) (h1 : 505 ≤ k) (h2 : k < 507) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 506 then cr_505_506 k h1 h else cr_506_507 k (by omega) h2
theorem cr_504_507 (k : ℕ) (h1 : 504 ≤ k) (h2 : k < 507) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 505 then cr_504_505 k h1 h else cr_505_507 k (by omega) h2
theorem cr_502_507 (k : ℕ) (h1 : 502 ≤ k) (h2 : k < 507) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 504 then cr_502_504 k h1 h else cr_504_507 k (by omega) h2
theorem cr_507_508 (k : ℕ) (h1 : 507 ≤ k) (h2 : k < 508) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 507 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf507_ok
theorem cr_508_509 (k : ℕ) (h1 : 508 ≤ k) (h2 : k < 509) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 508 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf508_ok
theorem cr_507_509 (k : ℕ) (h1 : 507 ≤ k) (h2 : k < 509) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 508 then cr_507_508 k h1 h else cr_508_509 k (by omega) h2
theorem cr_509_510 (k : ℕ) (h1 : 509 ≤ k) (h2 : k < 510) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 509 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf509_ok
theorem cr_510_511 (k : ℕ) (h1 : 510 ≤ k) (h2 : k < 511) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 510 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf510_ok
theorem cr_511_512 (k : ℕ) (h1 : 511 ≤ k) (h2 : k < 512) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 511 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf511_ok
theorem cr_510_512 (k : ℕ) (h1 : 510 ≤ k) (h2 : k < 512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 511 then cr_510_511 k h1 h else cr_511_512 k (by omega) h2
theorem cr_509_512 (k : ℕ) (h1 : 509 ≤ k) (h2 : k < 512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 510 then cr_509_510 k h1 h else cr_510_512 k (by omega) h2
theorem cr_507_512 (k : ℕ) (h1 : 507 ≤ k) (h2 : k < 512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 509 then cr_507_509 k h1 h else cr_509_512 k (by omega) h2
theorem cr_502_512 (k : ℕ) (h1 : 502 ≤ k) (h2 : k < 512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 507 then cr_502_507 k h1 h else cr_507_512 k (by omega) h2
theorem cr_492_512 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 502 then cr_492_502 k h1 h else cr_502_512 k (by omega) h2
theorem cr_512_513 (k : ℕ) (h1 : 512 ≤ k) (h2 : k < 513) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 512 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf512_ok
theorem cr_513_514 (k : ℕ) (h1 : 513 ≤ k) (h2 : k < 514) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 513 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf513_ok
theorem cr_512_514 (k : ℕ) (h1 : 512 ≤ k) (h2 : k < 514) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 513 then cr_512_513 k h1 h else cr_513_514 k (by omega) h2
theorem cr_514_515 (k : ℕ) (h1 : 514 ≤ k) (h2 : k < 515) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 514 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf514_ok
theorem cr_515_516 (k : ℕ) (h1 : 515 ≤ k) (h2 : k < 516) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 515 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf515_ok
theorem cr_516_517 (k : ℕ) (h1 : 516 ≤ k) (h2 : k < 517) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 516 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf516_ok
theorem cr_515_517 (k : ℕ) (h1 : 515 ≤ k) (h2 : k < 517) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 516 then cr_515_516 k h1 h else cr_516_517 k (by omega) h2
theorem cr_514_517 (k : ℕ) (h1 : 514 ≤ k) (h2 : k < 517) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 515 then cr_514_515 k h1 h else cr_515_517 k (by omega) h2
theorem cr_512_517 (k : ℕ) (h1 : 512 ≤ k) (h2 : k < 517) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 514 then cr_512_514 k h1 h else cr_514_517 k (by omega) h2
theorem cr_517_518 (k : ℕ) (h1 : 517 ≤ k) (h2 : k < 518) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 517 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf517_ok
theorem cr_518_519 (k : ℕ) (h1 : 518 ≤ k) (h2 : k < 519) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 518 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf518_ok
theorem cr_517_519 (k : ℕ) (h1 : 517 ≤ k) (h2 : k < 519) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 518 then cr_517_518 k h1 h else cr_518_519 k (by omega) h2
theorem cr_519_520 (k : ℕ) (h1 : 519 ≤ k) (h2 : k < 520) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 519 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf519_ok
theorem cr_520_521 (k : ℕ) (h1 : 520 ≤ k) (h2 : k < 521) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 520 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf520_ok
theorem cr_521_522 (k : ℕ) (h1 : 521 ≤ k) (h2 : k < 522) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 521 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf521_ok
theorem cr_520_522 (k : ℕ) (h1 : 520 ≤ k) (h2 : k < 522) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 521 then cr_520_521 k h1 h else cr_521_522 k (by omega) h2
theorem cr_519_522 (k : ℕ) (h1 : 519 ≤ k) (h2 : k < 522) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 520 then cr_519_520 k h1 h else cr_520_522 k (by omega) h2
theorem cr_517_522 (k : ℕ) (h1 : 517 ≤ k) (h2 : k < 522) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 519 then cr_517_519 k h1 h else cr_519_522 k (by omega) h2
theorem cr_512_522 (k : ℕ) (h1 : 512 ≤ k) (h2 : k < 522) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 517 then cr_512_517 k h1 h else cr_517_522 k (by omega) h2
theorem cr_522_523 (k : ℕ) (h1 : 522 ≤ k) (h2 : k < 523) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 522 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf522_ok
theorem cr_523_524 (k : ℕ) (h1 : 523 ≤ k) (h2 : k < 524) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 523 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf523_ok
theorem cr_522_524 (k : ℕ) (h1 : 522 ≤ k) (h2 : k < 524) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 523 then cr_522_523 k h1 h else cr_523_524 k (by omega) h2
theorem cr_524_525 (k : ℕ) (h1 : 524 ≤ k) (h2 : k < 525) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 524 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf524_ok
theorem cr_525_526 (k : ℕ) (h1 : 525 ≤ k) (h2 : k < 526) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 525 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf525_ok
theorem cr_526_527 (k : ℕ) (h1 : 526 ≤ k) (h2 : k < 527) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 526 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf526_ok
theorem cr_525_527 (k : ℕ) (h1 : 525 ≤ k) (h2 : k < 527) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 526 then cr_525_526 k h1 h else cr_526_527 k (by omega) h2
theorem cr_524_527 (k : ℕ) (h1 : 524 ≤ k) (h2 : k < 527) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 525 then cr_524_525 k h1 h else cr_525_527 k (by omega) h2
theorem cr_522_527 (k : ℕ) (h1 : 522 ≤ k) (h2 : k < 527) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 524 then cr_522_524 k h1 h else cr_524_527 k (by omega) h2
theorem cr_527_528 (k : ℕ) (h1 : 527 ≤ k) (h2 : k < 528) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 527 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf527_ok
theorem cr_528_529 (k : ℕ) (h1 : 528 ≤ k) (h2 : k < 529) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 528 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf528_ok
theorem cr_529_530 (k : ℕ) (h1 : 529 ≤ k) (h2 : k < 530) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 529 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf529_ok
theorem cr_528_530 (k : ℕ) (h1 : 528 ≤ k) (h2 : k < 530) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 529 then cr_528_529 k h1 h else cr_529_530 k (by omega) h2
theorem cr_527_530 (k : ℕ) (h1 : 527 ≤ k) (h2 : k < 530) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 528 then cr_527_528 k h1 h else cr_528_530 k (by omega) h2
theorem cr_530_531 (k : ℕ) (h1 : 530 ≤ k) (h2 : k < 531) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 530 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf530_ok
theorem cr_531_532 (k : ℕ) (h1 : 531 ≤ k) (h2 : k < 532) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 531 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf531_ok
theorem cr_532_533 (k : ℕ) (h1 : 532 ≤ k) (h2 : k < 533) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 532 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf532_ok
theorem cr_531_533 (k : ℕ) (h1 : 531 ≤ k) (h2 : k < 533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 532 then cr_531_532 k h1 h else cr_532_533 k (by omega) h2
theorem cr_530_533 (k : ℕ) (h1 : 530 ≤ k) (h2 : k < 533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 531 then cr_530_531 k h1 h else cr_531_533 k (by omega) h2
theorem cr_527_533 (k : ℕ) (h1 : 527 ≤ k) (h2 : k < 533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 530 then cr_527_530 k h1 h else cr_530_533 k (by omega) h2
theorem cr_522_533 (k : ℕ) (h1 : 522 ≤ k) (h2 : k < 533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 527 then cr_522_527 k h1 h else cr_527_533 k (by omega) h2
theorem cr_512_533 (k : ℕ) (h1 : 512 ≤ k) (h2 : k < 533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 522 then cr_512_522 k h1 h else cr_522_533 k (by omega) h2
theorem cr_492_533 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 512 then cr_492_512 k h1 h else cr_512_533 k (by omega) h2
theorem cr_533_534 (k : ℕ) (h1 : 533 ≤ k) (h2 : k < 534) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 533 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf533_ok
theorem cr_534_535 (k : ℕ) (h1 : 534 ≤ k) (h2 : k < 535) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 534 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf534_ok
theorem cr_533_535 (k : ℕ) (h1 : 533 ≤ k) (h2 : k < 535) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 534 then cr_533_534 k h1 h else cr_534_535 k (by omega) h2
theorem cr_535_536 (k : ℕ) (h1 : 535 ≤ k) (h2 : k < 536) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 535 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf535_ok
theorem cr_536_537 (k : ℕ) (h1 : 536 ≤ k) (h2 : k < 537) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 536 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf536_ok
theorem cr_537_538 (k : ℕ) (h1 : 537 ≤ k) (h2 : k < 538) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 537 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf537_ok
theorem cr_536_538 (k : ℕ) (h1 : 536 ≤ k) (h2 : k < 538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 537 then cr_536_537 k h1 h else cr_537_538 k (by omega) h2
theorem cr_535_538 (k : ℕ) (h1 : 535 ≤ k) (h2 : k < 538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 536 then cr_535_536 k h1 h else cr_536_538 k (by omega) h2
theorem cr_533_538 (k : ℕ) (h1 : 533 ≤ k) (h2 : k < 538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 535 then cr_533_535 k h1 h else cr_535_538 k (by omega) h2
theorem cr_538_539 (k : ℕ) (h1 : 538 ≤ k) (h2 : k < 539) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 538 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf538_ok
theorem cr_539_540 (k : ℕ) (h1 : 539 ≤ k) (h2 : k < 540) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 539 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf539_ok
theorem cr_538_540 (k : ℕ) (h1 : 538 ≤ k) (h2 : k < 540) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 539 then cr_538_539 k h1 h else cr_539_540 k (by omega) h2
theorem cr_540_541 (k : ℕ) (h1 : 540 ≤ k) (h2 : k < 541) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 540 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf540_ok
theorem cr_541_542 (k : ℕ) (h1 : 541 ≤ k) (h2 : k < 542) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 541 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf541_ok
theorem cr_542_543 (k : ℕ) (h1 : 542 ≤ k) (h2 : k < 543) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 542 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf542_ok
theorem cr_541_543 (k : ℕ) (h1 : 541 ≤ k) (h2 : k < 543) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 542 then cr_541_542 k h1 h else cr_542_543 k (by omega) h2
theorem cr_540_543 (k : ℕ) (h1 : 540 ≤ k) (h2 : k < 543) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 541 then cr_540_541 k h1 h else cr_541_543 k (by omega) h2
theorem cr_538_543 (k : ℕ) (h1 : 538 ≤ k) (h2 : k < 543) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 540 then cr_538_540 k h1 h else cr_540_543 k (by omega) h2
theorem cr_533_543 (k : ℕ) (h1 : 533 ≤ k) (h2 : k < 543) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 538 then cr_533_538 k h1 h else cr_538_543 k (by omega) h2
theorem cr_543_544 (k : ℕ) (h1 : 543 ≤ k) (h2 : k < 544) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 543 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf543_ok
theorem cr_544_545 (k : ℕ) (h1 : 544 ≤ k) (h2 : k < 545) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 544 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf544_ok
theorem cr_543_545 (k : ℕ) (h1 : 543 ≤ k) (h2 : k < 545) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 544 then cr_543_544 k h1 h else cr_544_545 k (by omega) h2
theorem cr_545_546 (k : ℕ) (h1 : 545 ≤ k) (h2 : k < 546) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 545 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf545_ok
theorem cr_546_547 (k : ℕ) (h1 : 546 ≤ k) (h2 : k < 547) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 546 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf546_ok
theorem cr_547_548 (k : ℕ) (h1 : 547 ≤ k) (h2 : k < 548) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 547 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf547_ok
theorem cr_546_548 (k : ℕ) (h1 : 546 ≤ k) (h2 : k < 548) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 547 then cr_546_547 k h1 h else cr_547_548 k (by omega) h2
theorem cr_545_548 (k : ℕ) (h1 : 545 ≤ k) (h2 : k < 548) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 546 then cr_545_546 k h1 h else cr_546_548 k (by omega) h2
theorem cr_543_548 (k : ℕ) (h1 : 543 ≤ k) (h2 : k < 548) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 545 then cr_543_545 k h1 h else cr_545_548 k (by omega) h2
theorem cr_548_549 (k : ℕ) (h1 : 548 ≤ k) (h2 : k < 549) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 548 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf548_ok
theorem cr_549_550 (k : ℕ) (h1 : 549 ≤ k) (h2 : k < 550) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 549 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf549_ok
theorem cr_548_550 (k : ℕ) (h1 : 548 ≤ k) (h2 : k < 550) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 549 then cr_548_549 k h1 h else cr_549_550 k (by omega) h2
theorem cr_550_551 (k : ℕ) (h1 : 550 ≤ k) (h2 : k < 551) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 550 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf550_ok
theorem cr_551_552 (k : ℕ) (h1 : 551 ≤ k) (h2 : k < 552) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 551 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf551_ok
theorem cr_552_553 (k : ℕ) (h1 : 552 ≤ k) (h2 : k < 553) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 552 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf552_ok
theorem cr_551_553 (k : ℕ) (h1 : 551 ≤ k) (h2 : k < 553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 552 then cr_551_552 k h1 h else cr_552_553 k (by omega) h2
theorem cr_550_553 (k : ℕ) (h1 : 550 ≤ k) (h2 : k < 553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 551 then cr_550_551 k h1 h else cr_551_553 k (by omega) h2
theorem cr_548_553 (k : ℕ) (h1 : 548 ≤ k) (h2 : k < 553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 550 then cr_548_550 k h1 h else cr_550_553 k (by omega) h2
theorem cr_543_553 (k : ℕ) (h1 : 543 ≤ k) (h2 : k < 553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 548 then cr_543_548 k h1 h else cr_548_553 k (by omega) h2
theorem cr_533_553 (k : ℕ) (h1 : 533 ≤ k) (h2 : k < 553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 543 then cr_533_543 k h1 h else cr_543_553 k (by omega) h2
theorem cr_553_554 (k : ℕ) (h1 : 553 ≤ k) (h2 : k < 554) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 553 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf553_ok
theorem cr_554_555 (k : ℕ) (h1 : 554 ≤ k) (h2 : k < 555) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 554 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf554_ok
theorem cr_553_555 (k : ℕ) (h1 : 553 ≤ k) (h2 : k < 555) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 554 then cr_553_554 k h1 h else cr_554_555 k (by omega) h2
theorem cr_555_556 (k : ℕ) (h1 : 555 ≤ k) (h2 : k < 556) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 555 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf555_ok
theorem cr_556_557 (k : ℕ) (h1 : 556 ≤ k) (h2 : k < 557) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 556 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf556_ok
theorem cr_557_558 (k : ℕ) (h1 : 557 ≤ k) (h2 : k < 558) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 557 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf557_ok
theorem cr_556_558 (k : ℕ) (h1 : 556 ≤ k) (h2 : k < 558) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 557 then cr_556_557 k h1 h else cr_557_558 k (by omega) h2
theorem cr_555_558 (k : ℕ) (h1 : 555 ≤ k) (h2 : k < 558) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 556 then cr_555_556 k h1 h else cr_556_558 k (by omega) h2
theorem cr_553_558 (k : ℕ) (h1 : 553 ≤ k) (h2 : k < 558) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 555 then cr_553_555 k h1 h else cr_555_558 k (by omega) h2
theorem cr_558_559 (k : ℕ) (h1 : 558 ≤ k) (h2 : k < 559) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 558 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf558_ok
theorem cr_559_560 (k : ℕ) (h1 : 559 ≤ k) (h2 : k < 560) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 559 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf559_ok
theorem cr_558_560 (k : ℕ) (h1 : 558 ≤ k) (h2 : k < 560) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 559 then cr_558_559 k h1 h else cr_559_560 k (by omega) h2
theorem cr_560_561 (k : ℕ) (h1 : 560 ≤ k) (h2 : k < 561) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 560 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf560_ok
theorem cr_561_562 (k : ℕ) (h1 : 561 ≤ k) (h2 : k < 562) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 561 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf561_ok
theorem cr_562_563 (k : ℕ) (h1 : 562 ≤ k) (h2 : k < 563) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 562 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf562_ok
theorem cr_561_563 (k : ℕ) (h1 : 561 ≤ k) (h2 : k < 563) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 562 then cr_561_562 k h1 h else cr_562_563 k (by omega) h2
theorem cr_560_563 (k : ℕ) (h1 : 560 ≤ k) (h2 : k < 563) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 561 then cr_560_561 k h1 h else cr_561_563 k (by omega) h2
theorem cr_558_563 (k : ℕ) (h1 : 558 ≤ k) (h2 : k < 563) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 560 then cr_558_560 k h1 h else cr_560_563 k (by omega) h2
theorem cr_553_563 (k : ℕ) (h1 : 553 ≤ k) (h2 : k < 563) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 558 then cr_553_558 k h1 h else cr_558_563 k (by omega) h2
theorem cr_563_564 (k : ℕ) (h1 : 563 ≤ k) (h2 : k < 564) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 563 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf563_ok
theorem cr_564_565 (k : ℕ) (h1 : 564 ≤ k) (h2 : k < 565) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 564 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf564_ok
theorem cr_563_565 (k : ℕ) (h1 : 563 ≤ k) (h2 : k < 565) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 564 then cr_563_564 k h1 h else cr_564_565 k (by omega) h2
theorem cr_565_566 (k : ℕ) (h1 : 565 ≤ k) (h2 : k < 566) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 565 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf565_ok
theorem cr_566_567 (k : ℕ) (h1 : 566 ≤ k) (h2 : k < 567) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 566 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf566_ok
theorem cr_567_568 (k : ℕ) (h1 : 567 ≤ k) (h2 : k < 568) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 567 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf567_ok
theorem cr_566_568 (k : ℕ) (h1 : 566 ≤ k) (h2 : k < 568) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 567 then cr_566_567 k h1 h else cr_567_568 k (by omega) h2
theorem cr_565_568 (k : ℕ) (h1 : 565 ≤ k) (h2 : k < 568) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 566 then cr_565_566 k h1 h else cr_566_568 k (by omega) h2
theorem cr_563_568 (k : ℕ) (h1 : 563 ≤ k) (h2 : k < 568) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 565 then cr_563_565 k h1 h else cr_565_568 k (by omega) h2
theorem cr_568_569 (k : ℕ) (h1 : 568 ≤ k) (h2 : k < 569) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 568 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf568_ok
theorem cr_569_570 (k : ℕ) (h1 : 569 ≤ k) (h2 : k < 570) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 569 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf569_ok
theorem cr_570_571 (k : ℕ) (h1 : 570 ≤ k) (h2 : k < 571) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 570 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf570_ok
theorem cr_569_571 (k : ℕ) (h1 : 569 ≤ k) (h2 : k < 571) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 570 then cr_569_570 k h1 h else cr_570_571 k (by omega) h2
theorem cr_568_571 (k : ℕ) (h1 : 568 ≤ k) (h2 : k < 571) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 569 then cr_568_569 k h1 h else cr_569_571 k (by omega) h2
theorem cr_571_572 (k : ℕ) (h1 : 571 ≤ k) (h2 : k < 572) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 571 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf571_ok
theorem cr_572_573 (k : ℕ) (h1 : 572 ≤ k) (h2 : k < 573) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 572 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf572_ok
theorem cr_573_574 (k : ℕ) (h1 : 573 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 573 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf573_ok
theorem cr_572_574 (k : ℕ) (h1 : 572 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 573 then cr_572_573 k h1 h else cr_573_574 k (by omega) h2
theorem cr_571_574 (k : ℕ) (h1 : 571 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 572 then cr_571_572 k h1 h else cr_572_574 k (by omega) h2
theorem cr_568_574 (k : ℕ) (h1 : 568 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 571 then cr_568_571 k h1 h else cr_571_574 k (by omega) h2
theorem cr_563_574 (k : ℕ) (h1 : 563 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 568 then cr_563_568 k h1 h else cr_568_574 k (by omega) h2
theorem cr_553_574 (k : ℕ) (h1 : 553 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 563 then cr_553_563 k h1 h else cr_563_574 k (by omega) h2
theorem cr_533_574 (k : ℕ) (h1 : 533 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 553 then cr_533_553 k h1 h else cr_553_574 k (by omega) h2
theorem cr_492_574 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 533 then cr_492_533 k h1 h else cr_533_574 k (by omega) h2
theorem cr_574_575 (k : ℕ) (h1 : 574 ≤ k) (h2 : k < 575) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 574 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf574_ok
theorem cr_575_576 (k : ℕ) (h1 : 575 ≤ k) (h2 : k < 576) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 575 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf575_ok
theorem cr_574_576 (k : ℕ) (h1 : 574 ≤ k) (h2 : k < 576) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 575 then cr_574_575 k h1 h else cr_575_576 k (by omega) h2
theorem cr_576_577 (k : ℕ) (h1 : 576 ≤ k) (h2 : k < 577) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 576 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf576_ok
theorem cr_577_578 (k : ℕ) (h1 : 577 ≤ k) (h2 : k < 578) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 577 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf577_ok
theorem cr_578_579 (k : ℕ) (h1 : 578 ≤ k) (h2 : k < 579) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 578 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf578_ok
theorem cr_577_579 (k : ℕ) (h1 : 577 ≤ k) (h2 : k < 579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 578 then cr_577_578 k h1 h else cr_578_579 k (by omega) h2
theorem cr_576_579 (k : ℕ) (h1 : 576 ≤ k) (h2 : k < 579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 577 then cr_576_577 k h1 h else cr_577_579 k (by omega) h2
theorem cr_574_579 (k : ℕ) (h1 : 574 ≤ k) (h2 : k < 579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 576 then cr_574_576 k h1 h else cr_576_579 k (by omega) h2
theorem cr_579_580 (k : ℕ) (h1 : 579 ≤ k) (h2 : k < 580) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 579 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf579_ok
theorem cr_580_581 (k : ℕ) (h1 : 580 ≤ k) (h2 : k < 581) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 580 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf580_ok
theorem cr_579_581 (k : ℕ) (h1 : 579 ≤ k) (h2 : k < 581) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 580 then cr_579_580 k h1 h else cr_580_581 k (by omega) h2
theorem cr_581_582 (k : ℕ) (h1 : 581 ≤ k) (h2 : k < 582) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 581 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf581_ok
theorem cr_582_583 (k : ℕ) (h1 : 582 ≤ k) (h2 : k < 583) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 582 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf582_ok
theorem cr_583_584 (k : ℕ) (h1 : 583 ≤ k) (h2 : k < 584) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 583 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf583_ok
theorem cr_582_584 (k : ℕ) (h1 : 582 ≤ k) (h2 : k < 584) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 583 then cr_582_583 k h1 h else cr_583_584 k (by omega) h2
theorem cr_581_584 (k : ℕ) (h1 : 581 ≤ k) (h2 : k < 584) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 582 then cr_581_582 k h1 h else cr_582_584 k (by omega) h2
theorem cr_579_584 (k : ℕ) (h1 : 579 ≤ k) (h2 : k < 584) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 581 then cr_579_581 k h1 h else cr_581_584 k (by omega) h2
theorem cr_574_584 (k : ℕ) (h1 : 574 ≤ k) (h2 : k < 584) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 579 then cr_574_579 k h1 h else cr_579_584 k (by omega) h2
theorem cr_584_585 (k : ℕ) (h1 : 584 ≤ k) (h2 : k < 585) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 584 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf584_ok
theorem cr_585_586 (k : ℕ) (h1 : 585 ≤ k) (h2 : k < 586) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 585 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf585_ok
theorem cr_584_586 (k : ℕ) (h1 : 584 ≤ k) (h2 : k < 586) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 585 then cr_584_585 k h1 h else cr_585_586 k (by omega) h2
theorem cr_586_587 (k : ℕ) (h1 : 586 ≤ k) (h2 : k < 587) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 586 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf586_ok
theorem cr_587_588 (k : ℕ) (h1 : 587 ≤ k) (h2 : k < 588) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 587 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf587_ok
theorem cr_588_589 (k : ℕ) (h1 : 588 ≤ k) (h2 : k < 589) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 588 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf588_ok
theorem cr_587_589 (k : ℕ) (h1 : 587 ≤ k) (h2 : k < 589) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 588 then cr_587_588 k h1 h else cr_588_589 k (by omega) h2
theorem cr_586_589 (k : ℕ) (h1 : 586 ≤ k) (h2 : k < 589) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 587 then cr_586_587 k h1 h else cr_587_589 k (by omega) h2
theorem cr_584_589 (k : ℕ) (h1 : 584 ≤ k) (h2 : k < 589) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 586 then cr_584_586 k h1 h else cr_586_589 k (by omega) h2
theorem cr_589_590 (k : ℕ) (h1 : 589 ≤ k) (h2 : k < 590) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 589 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf589_ok
theorem cr_590_591 (k : ℕ) (h1 : 590 ≤ k) (h2 : k < 591) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 590 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf590_ok
theorem cr_589_591 (k : ℕ) (h1 : 589 ≤ k) (h2 : k < 591) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 590 then cr_589_590 k h1 h else cr_590_591 k (by omega) h2
theorem cr_591_592 (k : ℕ) (h1 : 591 ≤ k) (h2 : k < 592) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 591 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf591_ok
theorem cr_592_593 (k : ℕ) (h1 : 592 ≤ k) (h2 : k < 593) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 592 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf592_ok
theorem cr_593_594 (k : ℕ) (h1 : 593 ≤ k) (h2 : k < 594) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 593 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf593_ok
theorem cr_592_594 (k : ℕ) (h1 : 592 ≤ k) (h2 : k < 594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 593 then cr_592_593 k h1 h else cr_593_594 k (by omega) h2
theorem cr_591_594 (k : ℕ) (h1 : 591 ≤ k) (h2 : k < 594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 592 then cr_591_592 k h1 h else cr_592_594 k (by omega) h2
theorem cr_589_594 (k : ℕ) (h1 : 589 ≤ k) (h2 : k < 594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 591 then cr_589_591 k h1 h else cr_591_594 k (by omega) h2
theorem cr_584_594 (k : ℕ) (h1 : 584 ≤ k) (h2 : k < 594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 589 then cr_584_589 k h1 h else cr_589_594 k (by omega) h2
theorem cr_574_594 (k : ℕ) (h1 : 574 ≤ k) (h2 : k < 594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 584 then cr_574_584 k h1 h else cr_584_594 k (by omega) h2
theorem cr_594_595 (k : ℕ) (h1 : 594 ≤ k) (h2 : k < 595) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 594 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf594_ok
theorem cr_595_596 (k : ℕ) (h1 : 595 ≤ k) (h2 : k < 596) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 595 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf595_ok
theorem cr_594_596 (k : ℕ) (h1 : 594 ≤ k) (h2 : k < 596) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 595 then cr_594_595 k h1 h else cr_595_596 k (by omega) h2
theorem cr_596_597 (k : ℕ) (h1 : 596 ≤ k) (h2 : k < 597) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 596 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf596_ok
theorem cr_597_598 (k : ℕ) (h1 : 597 ≤ k) (h2 : k < 598) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 597 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf597_ok
theorem cr_598_599 (k : ℕ) (h1 : 598 ≤ k) (h2 : k < 599) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 598 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf598_ok
theorem cr_597_599 (k : ℕ) (h1 : 597 ≤ k) (h2 : k < 599) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 598 then cr_597_598 k h1 h else cr_598_599 k (by omega) h2
theorem cr_596_599 (k : ℕ) (h1 : 596 ≤ k) (h2 : k < 599) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 597 then cr_596_597 k h1 h else cr_597_599 k (by omega) h2
theorem cr_594_599 (k : ℕ) (h1 : 594 ≤ k) (h2 : k < 599) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 596 then cr_594_596 k h1 h else cr_596_599 k (by omega) h2
theorem cr_599_600 (k : ℕ) (h1 : 599 ≤ k) (h2 : k < 600) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 599 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf599_ok
theorem cr_600_601 (k : ℕ) (h1 : 600 ≤ k) (h2 : k < 601) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 600 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf600_ok
theorem cr_599_601 (k : ℕ) (h1 : 599 ≤ k) (h2 : k < 601) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 600 then cr_599_600 k h1 h else cr_600_601 k (by omega) h2
theorem cr_601_602 (k : ℕ) (h1 : 601 ≤ k) (h2 : k < 602) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 601 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf601_ok
theorem cr_602_603 (k : ℕ) (h1 : 602 ≤ k) (h2 : k < 603) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 602 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf602_ok
theorem cr_603_604 (k : ℕ) (h1 : 603 ≤ k) (h2 : k < 604) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 603 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf603_ok
theorem cr_602_604 (k : ℕ) (h1 : 602 ≤ k) (h2 : k < 604) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 603 then cr_602_603 k h1 h else cr_603_604 k (by omega) h2
theorem cr_601_604 (k : ℕ) (h1 : 601 ≤ k) (h2 : k < 604) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 602 then cr_601_602 k h1 h else cr_602_604 k (by omega) h2
theorem cr_599_604 (k : ℕ) (h1 : 599 ≤ k) (h2 : k < 604) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 601 then cr_599_601 k h1 h else cr_601_604 k (by omega) h2
theorem cr_594_604 (k : ℕ) (h1 : 594 ≤ k) (h2 : k < 604) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 599 then cr_594_599 k h1 h else cr_599_604 k (by omega) h2
theorem cr_604_605 (k : ℕ) (h1 : 604 ≤ k) (h2 : k < 605) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 604 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf604_ok
theorem cr_605_606 (k : ℕ) (h1 : 605 ≤ k) (h2 : k < 606) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 605 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf605_ok
theorem cr_604_606 (k : ℕ) (h1 : 604 ≤ k) (h2 : k < 606) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 605 then cr_604_605 k h1 h else cr_605_606 k (by omega) h2
theorem cr_606_607 (k : ℕ) (h1 : 606 ≤ k) (h2 : k < 607) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 606 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf606_ok
theorem cr_607_608 (k : ℕ) (h1 : 607 ≤ k) (h2 : k < 608) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 607 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf607_ok
theorem cr_608_609 (k : ℕ) (h1 : 608 ≤ k) (h2 : k < 609) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 608 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf608_ok
theorem cr_607_609 (k : ℕ) (h1 : 607 ≤ k) (h2 : k < 609) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 608 then cr_607_608 k h1 h else cr_608_609 k (by omega) h2
theorem cr_606_609 (k : ℕ) (h1 : 606 ≤ k) (h2 : k < 609) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 607 then cr_606_607 k h1 h else cr_607_609 k (by omega) h2
theorem cr_604_609 (k : ℕ) (h1 : 604 ≤ k) (h2 : k < 609) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 606 then cr_604_606 k h1 h else cr_606_609 k (by omega) h2
theorem cr_609_610 (k : ℕ) (h1 : 609 ≤ k) (h2 : k < 610) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 609 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf609_ok
theorem cr_610_611 (k : ℕ) (h1 : 610 ≤ k) (h2 : k < 611) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 610 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf610_ok
theorem cr_611_612 (k : ℕ) (h1 : 611 ≤ k) (h2 : k < 612) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 611 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf611_ok
theorem cr_610_612 (k : ℕ) (h1 : 610 ≤ k) (h2 : k < 612) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 611 then cr_610_611 k h1 h else cr_611_612 k (by omega) h2
theorem cr_609_612 (k : ℕ) (h1 : 609 ≤ k) (h2 : k < 612) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 610 then cr_609_610 k h1 h else cr_610_612 k (by omega) h2
theorem cr_612_613 (k : ℕ) (h1 : 612 ≤ k) (h2 : k < 613) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 612 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf612_ok
theorem cr_613_614 (k : ℕ) (h1 : 613 ≤ k) (h2 : k < 614) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 613 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf613_ok
theorem cr_614_615 (k : ℕ) (h1 : 614 ≤ k) (h2 : k < 615) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 614 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf614_ok
theorem cr_613_615 (k : ℕ) (h1 : 613 ≤ k) (h2 : k < 615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 614 then cr_613_614 k h1 h else cr_614_615 k (by omega) h2
theorem cr_612_615 (k : ℕ) (h1 : 612 ≤ k) (h2 : k < 615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 613 then cr_612_613 k h1 h else cr_613_615 k (by omega) h2
theorem cr_609_615 (k : ℕ) (h1 : 609 ≤ k) (h2 : k < 615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 612 then cr_609_612 k h1 h else cr_612_615 k (by omega) h2
theorem cr_604_615 (k : ℕ) (h1 : 604 ≤ k) (h2 : k < 615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 609 then cr_604_609 k h1 h else cr_609_615 k (by omega) h2
theorem cr_594_615 (k : ℕ) (h1 : 594 ≤ k) (h2 : k < 615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 604 then cr_594_604 k h1 h else cr_604_615 k (by omega) h2
theorem cr_574_615 (k : ℕ) (h1 : 574 ≤ k) (h2 : k < 615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 594 then cr_574_594 k h1 h else cr_594_615 k (by omega) h2
theorem cr_615_616 (k : ℕ) (h1 : 615 ≤ k) (h2 : k < 616) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 615 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf615_ok
theorem cr_616_617 (k : ℕ) (h1 : 616 ≤ k) (h2 : k < 617) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 616 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf616_ok
theorem cr_615_617 (k : ℕ) (h1 : 615 ≤ k) (h2 : k < 617) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 616 then cr_615_616 k h1 h else cr_616_617 k (by omega) h2
theorem cr_617_618 (k : ℕ) (h1 : 617 ≤ k) (h2 : k < 618) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 617 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf617_ok
theorem cr_618_619 (k : ℕ) (h1 : 618 ≤ k) (h2 : k < 619) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 618 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf618_ok
theorem cr_619_620 (k : ℕ) (h1 : 619 ≤ k) (h2 : k < 620) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 619 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf619_ok
theorem cr_618_620 (k : ℕ) (h1 : 618 ≤ k) (h2 : k < 620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 619 then cr_618_619 k h1 h else cr_619_620 k (by omega) h2
theorem cr_617_620 (k : ℕ) (h1 : 617 ≤ k) (h2 : k < 620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 618 then cr_617_618 k h1 h else cr_618_620 k (by omega) h2
theorem cr_615_620 (k : ℕ) (h1 : 615 ≤ k) (h2 : k < 620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 617 then cr_615_617 k h1 h else cr_617_620 k (by omega) h2
theorem cr_620_621 (k : ℕ) (h1 : 620 ≤ k) (h2 : k < 621) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 620 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf620_ok
theorem cr_621_622 (k : ℕ) (h1 : 621 ≤ k) (h2 : k < 622) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 621 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf621_ok
theorem cr_620_622 (k : ℕ) (h1 : 620 ≤ k) (h2 : k < 622) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 621 then cr_620_621 k h1 h else cr_621_622 k (by omega) h2
theorem cr_622_623 (k : ℕ) (h1 : 622 ≤ k) (h2 : k < 623) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 622 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf622_ok
theorem cr_623_624 (k : ℕ) (h1 : 623 ≤ k) (h2 : k < 624) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 623 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf623_ok
theorem cr_624_625 (k : ℕ) (h1 : 624 ≤ k) (h2 : k < 625) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 624 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf624_ok
theorem cr_623_625 (k : ℕ) (h1 : 623 ≤ k) (h2 : k < 625) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 624 then cr_623_624 k h1 h else cr_624_625 k (by omega) h2
theorem cr_622_625 (k : ℕ) (h1 : 622 ≤ k) (h2 : k < 625) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 623 then cr_622_623 k h1 h else cr_623_625 k (by omega) h2
theorem cr_620_625 (k : ℕ) (h1 : 620 ≤ k) (h2 : k < 625) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 622 then cr_620_622 k h1 h else cr_622_625 k (by omega) h2
theorem cr_615_625 (k : ℕ) (h1 : 615 ≤ k) (h2 : k < 625) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 620 then cr_615_620 k h1 h else cr_620_625 k (by omega) h2
theorem cr_625_626 (k : ℕ) (h1 : 625 ≤ k) (h2 : k < 626) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 625 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf625_ok
theorem cr_626_627 (k : ℕ) (h1 : 626 ≤ k) (h2 : k < 627) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 626 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf626_ok
theorem cr_625_627 (k : ℕ) (h1 : 625 ≤ k) (h2 : k < 627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 626 then cr_625_626 k h1 h else cr_626_627 k (by omega) h2
theorem cr_627_628 (k : ℕ) (h1 : 627 ≤ k) (h2 : k < 628) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 627 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf627_ok
theorem cr_628_629 (k : ℕ) (h1 : 628 ≤ k) (h2 : k < 629) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 628 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf628_ok
theorem cr_629_630 (k : ℕ) (h1 : 629 ≤ k) (h2 : k < 630) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 629 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf629_ok
theorem cr_628_630 (k : ℕ) (h1 : 628 ≤ k) (h2 : k < 630) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 629 then cr_628_629 k h1 h else cr_629_630 k (by omega) h2
theorem cr_627_630 (k : ℕ) (h1 : 627 ≤ k) (h2 : k < 630) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 628 then cr_627_628 k h1 h else cr_628_630 k (by omega) h2
theorem cr_625_630 (k : ℕ) (h1 : 625 ≤ k) (h2 : k < 630) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 627 then cr_625_627 k h1 h else cr_627_630 k (by omega) h2
theorem cr_630_631 (k : ℕ) (h1 : 630 ≤ k) (h2 : k < 631) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 630 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf630_ok
theorem cr_631_632 (k : ℕ) (h1 : 631 ≤ k) (h2 : k < 632) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 631 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf631_ok
theorem cr_630_632 (k : ℕ) (h1 : 630 ≤ k) (h2 : k < 632) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 631 then cr_630_631 k h1 h else cr_631_632 k (by omega) h2
theorem cr_632_633 (k : ℕ) (h1 : 632 ≤ k) (h2 : k < 633) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 632 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf632_ok
theorem cr_633_634 (k : ℕ) (h1 : 633 ≤ k) (h2 : k < 634) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 633 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf633_ok
theorem cr_634_635 (k : ℕ) (h1 : 634 ≤ k) (h2 : k < 635) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 634 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf634_ok
theorem cr_633_635 (k : ℕ) (h1 : 633 ≤ k) (h2 : k < 635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 634 then cr_633_634 k h1 h else cr_634_635 k (by omega) h2
theorem cr_632_635 (k : ℕ) (h1 : 632 ≤ k) (h2 : k < 635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 633 then cr_632_633 k h1 h else cr_633_635 k (by omega) h2
theorem cr_630_635 (k : ℕ) (h1 : 630 ≤ k) (h2 : k < 635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 632 then cr_630_632 k h1 h else cr_632_635 k (by omega) h2
theorem cr_625_635 (k : ℕ) (h1 : 625 ≤ k) (h2 : k < 635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 630 then cr_625_630 k h1 h else cr_630_635 k (by omega) h2
theorem cr_615_635 (k : ℕ) (h1 : 615 ≤ k) (h2 : k < 635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 625 then cr_615_625 k h1 h else cr_625_635 k (by omega) h2
theorem cr_635_636 (k : ℕ) (h1 : 635 ≤ k) (h2 : k < 636) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 635 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf635_ok
theorem cr_636_637 (k : ℕ) (h1 : 636 ≤ k) (h2 : k < 637) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 636 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf636_ok
theorem cr_635_637 (k : ℕ) (h1 : 635 ≤ k) (h2 : k < 637) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 636 then cr_635_636 k h1 h else cr_636_637 k (by omega) h2
theorem cr_637_638 (k : ℕ) (h1 : 637 ≤ k) (h2 : k < 638) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 637 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf637_ok
theorem cr_638_639 (k : ℕ) (h1 : 638 ≤ k) (h2 : k < 639) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 638 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf638_ok
theorem cr_639_640 (k : ℕ) (h1 : 639 ≤ k) (h2 : k < 640) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 639 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf639_ok
theorem cr_638_640 (k : ℕ) (h1 : 638 ≤ k) (h2 : k < 640) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 639 then cr_638_639 k h1 h else cr_639_640 k (by omega) h2
theorem cr_637_640 (k : ℕ) (h1 : 637 ≤ k) (h2 : k < 640) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 638 then cr_637_638 k h1 h else cr_638_640 k (by omega) h2
theorem cr_635_640 (k : ℕ) (h1 : 635 ≤ k) (h2 : k < 640) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 637 then cr_635_637 k h1 h else cr_637_640 k (by omega) h2
theorem cr_640_641 (k : ℕ) (h1 : 640 ≤ k) (h2 : k < 641) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 640 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf640_ok
theorem cr_641_642 (k : ℕ) (h1 : 641 ≤ k) (h2 : k < 642) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 641 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf641_ok
theorem cr_640_642 (k : ℕ) (h1 : 640 ≤ k) (h2 : k < 642) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 641 then cr_640_641 k h1 h else cr_641_642 k (by omega) h2
theorem cr_642_643 (k : ℕ) (h1 : 642 ≤ k) (h2 : k < 643) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 642 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf642_ok
theorem cr_643_644 (k : ℕ) (h1 : 643 ≤ k) (h2 : k < 644) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 643 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf643_ok
theorem cr_644_645 (k : ℕ) (h1 : 644 ≤ k) (h2 : k < 645) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 644 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf644_ok
theorem cr_643_645 (k : ℕ) (h1 : 643 ≤ k) (h2 : k < 645) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 644 then cr_643_644 k h1 h else cr_644_645 k (by omega) h2
theorem cr_642_645 (k : ℕ) (h1 : 642 ≤ k) (h2 : k < 645) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 643 then cr_642_643 k h1 h else cr_643_645 k (by omega) h2
theorem cr_640_645 (k : ℕ) (h1 : 640 ≤ k) (h2 : k < 645) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 642 then cr_640_642 k h1 h else cr_642_645 k (by omega) h2
theorem cr_635_645 (k : ℕ) (h1 : 635 ≤ k) (h2 : k < 645) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 640 then cr_635_640 k h1 h else cr_640_645 k (by omega) h2
theorem cr_645_646 (k : ℕ) (h1 : 645 ≤ k) (h2 : k < 646) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 645 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf645_ok
theorem cr_646_647 (k : ℕ) (h1 : 646 ≤ k) (h2 : k < 647) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 646 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf646_ok
theorem cr_645_647 (k : ℕ) (h1 : 645 ≤ k) (h2 : k < 647) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 646 then cr_645_646 k h1 h else cr_646_647 k (by omega) h2
theorem cr_647_648 (k : ℕ) (h1 : 647 ≤ k) (h2 : k < 648) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 647 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf647_ok
theorem cr_648_649 (k : ℕ) (h1 : 648 ≤ k) (h2 : k < 649) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 648 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf648_ok
theorem cr_649_650 (k : ℕ) (h1 : 649 ≤ k) (h2 : k < 650) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 649 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf649_ok
theorem cr_648_650 (k : ℕ) (h1 : 648 ≤ k) (h2 : k < 650) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 649 then cr_648_649 k h1 h else cr_649_650 k (by omega) h2
theorem cr_647_650 (k : ℕ) (h1 : 647 ≤ k) (h2 : k < 650) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 648 then cr_647_648 k h1 h else cr_648_650 k (by omega) h2
theorem cr_645_650 (k : ℕ) (h1 : 645 ≤ k) (h2 : k < 650) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 647 then cr_645_647 k h1 h else cr_647_650 k (by omega) h2
theorem cr_650_651 (k : ℕ) (h1 : 650 ≤ k) (h2 : k < 651) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 650 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf650_ok
theorem cr_651_652 (k : ℕ) (h1 : 651 ≤ k) (h2 : k < 652) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 651 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf651_ok
theorem cr_652_653 (k : ℕ) (h1 : 652 ≤ k) (h2 : k < 653) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 652 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf652_ok
theorem cr_651_653 (k : ℕ) (h1 : 651 ≤ k) (h2 : k < 653) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 652 then cr_651_652 k h1 h else cr_652_653 k (by omega) h2
theorem cr_650_653 (k : ℕ) (h1 : 650 ≤ k) (h2 : k < 653) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 651 then cr_650_651 k h1 h else cr_651_653 k (by omega) h2
theorem cr_653_654 (k : ℕ) (h1 : 653 ≤ k) (h2 : k < 654) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 653 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf653_ok
theorem cr_654_655 (k : ℕ) (h1 : 654 ≤ k) (h2 : k < 655) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 654 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf654_ok
theorem cr_655_656 (k : ℕ) (h1 : 655 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 655 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf655_ok
theorem cr_654_656 (k : ℕ) (h1 : 654 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 655 then cr_654_655 k h1 h else cr_655_656 k (by omega) h2
theorem cr_653_656 (k : ℕ) (h1 : 653 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 654 then cr_653_654 k h1 h else cr_654_656 k (by omega) h2
theorem cr_650_656 (k : ℕ) (h1 : 650 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 653 then cr_650_653 k h1 h else cr_653_656 k (by omega) h2
theorem cr_645_656 (k : ℕ) (h1 : 645 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 650 then cr_645_650 k h1 h else cr_650_656 k (by omega) h2
theorem cr_635_656 (k : ℕ) (h1 : 635 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 645 then cr_635_645 k h1 h else cr_645_656 k (by omega) h2
theorem cr_615_656 (k : ℕ) (h1 : 615 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 635 then cr_615_635 k h1 h else cr_635_656 k (by omega) h2
theorem cr_574_656 (k : ℕ) (h1 : 574 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 615 then cr_574_615 k h1 h else cr_615_656 k (by omega) h2
theorem cr_492_656 (k : ℕ) (h1 : 492 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 574 then cr_492_574 k h1 h else cr_574_656 k (by omega) h2
theorem cr_328_656 (k : ℕ) (h1 : 328 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 492 then cr_328_492 k h1 h else cr_492_656 k (by omega) h2
theorem cr_0_656 (k : ℕ) (h1 : 0 ≤ k) (h2 : k < 656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 328 then cr_0_328 k h1 h else cr_328_656 k (by omega) h2

end Harris
