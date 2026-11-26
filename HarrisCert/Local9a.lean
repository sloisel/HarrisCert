module

public import HarrisCert.Local9

/-!
# Local theorem, part 9a: the explicit coefficient lists

`PcP e` (`e = ±1`) equals the explicit list `PcL1` resp. `PcL2`; checked once by the kernel.
-/

@[expose] public section

namespace Harris

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem PcL1_eq : PcP 1 = PcL1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem PcL2_eq : PcP (-1) = PcL2 := by decide +kernel

end Harris
