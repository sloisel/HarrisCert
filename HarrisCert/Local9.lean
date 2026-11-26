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

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Pc_pos1 : pcellsOK (PcP 1) 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Pc_pos2 : pcellsOK (PcP (-1)) 64 = true := by decide +kernel

end Harris
