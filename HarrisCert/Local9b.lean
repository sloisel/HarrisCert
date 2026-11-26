module

public import HarrisCert.Local9a

/-!
# Local theorem, part 9b: positivity of `PcP (±1)` on `[-1, 1]`

The 64-cell test is checked by the kernel in chunks of 4 cells (one theorem per chunk keeps the
kernel's memory use low), then reassembled.
-/

@[expose] public section

namespace Harris

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_0 : pcR PcL1 64 0 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_4 : pcR PcL1 64 4 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_8 : pcR PcL1 64 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_12 : pcR PcL1 64 12 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_16 : pcR PcL1 64 16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_20 : pcR PcL1 64 20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_24 : pcR PcL1 64 24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_28 : pcR PcL1 64 28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_32 : pcR PcL1 64 32 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_36 : pcR PcL1 64 36 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_40 : pcR PcL1 64 40 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_44 : pcR PcL1 64 44 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_48 : pcR PcL1 64 48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_52 : pcR PcL1 64 52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_56 : pcR PcL1 64 56 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck1_60 : pcR PcL1 64 60 4 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_0 : pcR PcL2 64 0 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_4 : pcR PcL2 64 4 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_8 : pcR PcL2 64 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_12 : pcR PcL2 64 12 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_16 : pcR PcL2 64 16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_20 : pcR PcL2 64 20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_24 : pcR PcL2 64 24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_28 : pcR PcL2 64 28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_32 : pcR PcL2 64 32 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_36 : pcR PcL2 64 36 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_40 : pcR PcL2 64 40 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_44 : pcR PcL2 64 44 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_48 : pcR PcL2 64 48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_52 : pcR PcL2 64 52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_56 : pcR PcL2 64 56 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ck2_60 : pcR PcL2 64 60 4 = true := by decide +kernel

theorem Pc_pos1 : pcellsOK (PcP 1) 64 = true := by
  rw [PcL1_eq]
  refine pcellsOK_of fun j hj => ?_
  by_cases h0 : j < 4; · exact pcR_cell ck1_0 (by omega) (by omega)
  by_cases h4 : j < 8; · exact pcR_cell ck1_4 (by omega) (by omega)
  by_cases h8 : j < 12; · exact pcR_cell ck1_8 (by omega) (by omega)
  by_cases h12 : j < 16; · exact pcR_cell ck1_12 (by omega) (by omega)
  by_cases h16 : j < 20; · exact pcR_cell ck1_16 (by omega) (by omega)
  by_cases h20 : j < 24; · exact pcR_cell ck1_20 (by omega) (by omega)
  by_cases h24 : j < 28; · exact pcR_cell ck1_24 (by omega) (by omega)
  by_cases h28 : j < 32; · exact pcR_cell ck1_28 (by omega) (by omega)
  by_cases h32 : j < 36; · exact pcR_cell ck1_32 (by omega) (by omega)
  by_cases h36 : j < 40; · exact pcR_cell ck1_36 (by omega) (by omega)
  by_cases h40 : j < 44; · exact pcR_cell ck1_40 (by omega) (by omega)
  by_cases h44 : j < 48; · exact pcR_cell ck1_44 (by omega) (by omega)
  by_cases h48 : j < 52; · exact pcR_cell ck1_48 (by omega) (by omega)
  by_cases h52 : j < 56; · exact pcR_cell ck1_52 (by omega) (by omega)
  by_cases h56 : j < 60; · exact pcR_cell ck1_56 (by omega) (by omega)
  exact pcR_cell ck1_60 (by omega) (by omega)

theorem Pc_pos2 : pcellsOK (PcP (-1)) 64 = true := by
  rw [PcL2_eq]
  refine pcellsOK_of fun j hj => ?_
  by_cases h0 : j < 4; · exact pcR_cell ck2_0 (by omega) (by omega)
  by_cases h4 : j < 8; · exact pcR_cell ck2_4 (by omega) (by omega)
  by_cases h8 : j < 12; · exact pcR_cell ck2_8 (by omega) (by omega)
  by_cases h12 : j < 16; · exact pcR_cell ck2_12 (by omega) (by omega)
  by_cases h16 : j < 20; · exact pcR_cell ck2_16 (by omega) (by omega)
  by_cases h20 : j < 24; · exact pcR_cell ck2_20 (by omega) (by omega)
  by_cases h24 : j < 28; · exact pcR_cell ck2_24 (by omega) (by omega)
  by_cases h28 : j < 32; · exact pcR_cell ck2_28 (by omega) (by omega)
  by_cases h32 : j < 36; · exact pcR_cell ck2_32 (by omega) (by omega)
  by_cases h36 : j < 40; · exact pcR_cell ck2_36 (by omega) (by omega)
  by_cases h40 : j < 44; · exact pcR_cell ck2_40 (by omega) (by omega)
  by_cases h44 : j < 48; · exact pcR_cell ck2_44 (by omega) (by omega)
  by_cases h48 : j < 52; · exact pcR_cell ck2_48 (by omega) (by omega)
  by_cases h52 : j < 56; · exact pcR_cell ck2_52 (by omega) (by omega)
  by_cases h56 : j < 60; · exact pcR_cell ck2_56 (by omega) (by omega)
  exact pcR_cell ck2_60 (by omega) (by omega)

end Harris
