module

public import HarrisCert.Data.Slabs
public import HarrisCert.Data.CellsZ32
public import HarrisCert.Data.CellsZ64
public import HarrisCert.Data.CellsZ128
public import HarrisCert.Data.CellsZ256

/-! The tables used by the kernel checks. -/

@[expose] public section

namespace Harris

def tables : Tables := ⟨slabT, z32, z64, z128, z256⟩

theorem tables_valid : tables.Valid :=
  ⟨z32_eq, z64_eq, z128_eq, z256_eq, cells32_ok, cells64_ok, cells128_ok, cells256_ok⟩

end Harris
