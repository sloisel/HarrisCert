module

public import HarrisCert.Local8

/-!
# Local theorem, part 9: the `Λ₂` polynomial certificate

On the half circle `z = e · (1 + it)² / (1 + t²)` (`e = ±1`, `t ∈ [-1, 1]`), the polynomial `Pc e` equals
`(1+t²)^10 · (230 · 4r² |z + r|⁸ - m̂ᵀ A⁻¹ m̂)` where `m̂ = Cᵀ m̃(z)`. Its nonnegativity is checked in the kernel.
-/

@[expose] public section

namespace Harris

def rK : K3 := ⟨0, 1 / 3⟩
def DnP : CP := ([1, 0, 1], [])
def WnP (e : K3) : CP := (psc e [1, 0, -1], psc e [0, 2])
def WbP (e : K3) : CP := (psc e [1, 0, -1], psc e [0, -2])
def sqbP (e : K3) : CP := cmul (cadd (WbP e) (csc rK DnP)) (cadd (WbP e) (csc rK DnP))

def ckP (e : K3) : Fin 4 → CP :=
  ![cmul (sqbP e) (cmul (WnP e) (cmul (WnP e) (WnP e))),
    cmul (sqbP e) (cmul (csc (-2) (cmul (WnP e) (WnP e))) DnP),
    cmul (sqbP e) (cmul (csc (-2) (WnP e)) (cmul DnP DnP)),
    cmul (sqbP e) (cmul DnP (cmul DnP DnP))]

def nvecP (e : K3) : Fin 7 → PK :=
  ![(ckP e 0).2, (ckP e 1).2, (ckP e 2).2, (ckP e 3).2,
    padd (ckP e 0).1 (psc ⟨0, -1 / 6⟩ (ckP e 1).1), padd (ckP e 2).1 (psc ⟨0, -1 / 2⟩ (ckP e 1).1),
    (ckP e 3).1]

def nhatP (e : K3) (j : Fin 6) : PK := sumP 7 fun i => psc (Cm i j) (nvecP e i)

def quadP (e : K3) : PK := sumP 6 fun a => sumP 6 fun b => psc (Aim a b) (pmul (nhatP e a) (nhatP e b))

def N1P (e : K3) : PK :=
  padd (pmul (cadd (WnP e) (csc rK DnP)).1 (cadd (WnP e) (csc rK DnP)).1)
    (pmul (cadd (WnP e) (csc rK DnP)).2 (cadd (WnP e) (csc rK DnP)).2)

def PcP (e : K3) : PK :=
  padd (psc ⟨920 / 3, 0⟩ (pmul (pmul (pmul (pmul (N1P e) (N1P e)) (N1P e)) (N1P e)) (pmul DnP.1 DnP.1)))
    (psc (-1) (quadP e))

/-- `PcP 1` as an explicit coefficient list (printed by `#eval`; the equality is `PcL1_eq`). -/
def PcL1 : PK := [⟨210709417480 / 35921961, 121641791440 / 35921961⟩, ⟨0, 0⟩, ⟨236191616245600 / 6501874941, 317783360905120 / 15171041529⟩, ⟨0, 0⟩, ⟨484956280969480 / 5057013843, 277934364841520 / 5057013843⟩, ⟨0, 0⟩, ⟨2150622076863040 / 15171041529, 131246122021760 / 1685671281⟩, ⟨0, 0⟩, ⟨2113372023024400 / 15171041529, 859087205586080 / 15171041529⟩, ⟨0, 0⟩, ⟨3473920 / 27, -7580375694400 / 1685671281⟩, ⟨0, 0⟩, ⟨2242702241974000 / 15171041529, -993622861552480 / 15171041529⟩, ⟨0, 0⟩, ⟨2304704513160640 / 15171041529, -1289064991322240 / 15171041529⟩, ⟨0, 0⟩, ⟨513080987340280 / 5057013843, -295523513082320 / 5057013843⟩, ⟨0, 0⟩, ⟨244315671575200 / 6501874941, -987584273334560 / 45513124587⟩, ⟨0, 0⟩, ⟨211437189880 / 35921961, -13563523760 / 3991329⟩]

/-- `PcP (-1)` as an explicit coefficient list (the equality is `PcL2_eq`). -/
def PcL2 : PK := [⟨211437189880 / 35921961, -13563523760 / 3991329⟩, ⟨0, 0⟩, ⟨244315671575200 / 6501874941, -987584273334560 / 45513124587⟩, ⟨0, 0⟩, ⟨513080987340280 / 5057013843, -295523513082320 / 5057013843⟩, ⟨0, 0⟩, ⟨2304704513160640 / 15171041529, -1289064991322240 / 15171041529⟩, ⟨0, 0⟩, ⟨2242702241974000 / 15171041529, -993622861552480 / 15171041529⟩, ⟨0, 0⟩, ⟨3473920 / 27, -7580375694400 / 1685671281⟩, ⟨0, 0⟩, ⟨2113372023024400 / 15171041529, 859087205586080 / 15171041529⟩, ⟨0, 0⟩, ⟨2150622076863040 / 15171041529, 131246122021760 / 1685671281⟩, ⟨0, 0⟩, ⟨484956280969480 / 5057013843, 277934364841520 / 5057013843⟩, ⟨0, 0⟩, ⟨236191616245600 / 6501874941, 317783360905120 / 15171041529⟩, ⟨0, 0⟩, ⟨210709417480 / 35921961, 121641791440 / 35921961⟩]

/-- The cell test on the cells `lo, …, lo + k - 1` of the subdivision of `[-1, 1]` into `n` cells. -/
def pcR (p : PK) (n lo k : ℕ) : Bool := (List.range' lo k).all fun j => cellOK p (cellC n j) (cellD n)

lemma pcR_cell {p : PK} {n lo k : ℕ} (h : pcR p n lo k = true) {j : ℕ} (h1 : lo ≤ j) (h2 : j < lo + k) :
    cellOK p (cellC n j) (cellD n) = true := by
  simp only [pcR, List.all_eq_true, List.mem_range'_1] at h
  exact h j ⟨h1, h2⟩

lemma pcellsOK_of {p : PK} {n : ℕ} (h : ∀ j, j < n → cellOK p (cellC n j) (cellD n) = true) :
    pcellsOK p n = true := by
  simp only [pcellsOK, List.all_eq_true, List.mem_range]
  exact h

end Harris
