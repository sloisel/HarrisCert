module

public import HarrisCert.Core.Nbar

/-!
# Integer version of `N̄` (computational core)

The cut is `γ_k = G_k / 2^e` with `G : Array ℤ`. The cell moments are `μ̂_i = Z_i / 2⁹⁶` with `Z` integer
(they are dyadic by construction, see `roundUp`). For each half circle, `Q = |P|²` has integer
coefficients at scale `2^{2e}`, and on each cell `A = Ẑ₀`, `B = Σ Q_i Ẑ_i` (the bound on the side of
the sign of `Q_i`), and `S ≥ 1` with `S² ≥ A·B`. Then `∫_cell |P| w ≤ S / 2^{96+e}`, and

`N(γ) ≤ (Σ S) / (2^{96+e} π_lo) ≤ NN / 2^f`  is checked as  `(Σ S) · 10²⁰ · 2^f ≤ NN · π₂₀ · 2^{96+e}`.
-/

@[expose] public section

namespace Harris

def zAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: zAdd p q

def zScale (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

def zMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => zAdd (zScale a q) (0 :: zMul p q)

abbrev ZPoly := List ℤ × List ℤ

def zcMul (a b : ZPoly) : ZPoly :=
  (zAdd (zMul a.1 b.1) (zScale (-1) (zMul a.2 b.2)), zAdd (zMul a.1 b.2) (zMul a.2 b.1))

def zcPow (p : ZPoly) : ℕ → ZPoly
  | 0 => ([1], [])
  | n + 1 => zcMul p (zcPow p n)

/-- `(1+it)^{2k} (1+t²)^{3-k}` with integer coefficients. -/
def basisZ (k : ℕ) : ZPoly := zcMul (zcPow ([1], [0, 1]) (2 * k)) (zcPow ([1, 0, 1], []) (3 - k))

def psigStepZ (G : Array ℤ) (σ : ℤ) (acc : ZPoly) (k : ℕ) : ZPoly :=
  let gr := σ ^ k * G.getD k 0
  let gi := σ ^ k * G.getD (k + 4) 0
  let B := basisZ k
  (zAdd acc.1 (zAdd (zScale gr B.1) (zScale (-gi) B.2)),
   zAdd acc.2 (zAdd (zScale gr B.2) (zScale gi B.1)))

def PsigZ (G : Array ℤ) (σ : ℤ) : ZPoly := (List.range 4).foldl (psigStepZ G σ) ([], [])

def absSqZ (P : ZPoly) : List ℤ := zAdd (zMul P.1 P.1) (zMul P.2 P.2)

/-- Integer cell data: `hi i = 2⁹⁶ μ̂⁺_i`, `lo i = 2⁹⁶ μ̂⁻_i`. -/
structure CellZ where
  hi : Array ℤ
  lo : Array ℤ
  deriving DecidableEq

/-- The integer version of a cell (exact, since the moments are rounded at scale `2⁹⁶`). -/
def CellData.toZ (c : CellData) : CellZ :=
  ⟨c.muHi.map fun x => (x * 2 ^ 96).num, c.muLo.map fun x => (x * 2 ^ 96).num⟩

def isqrtAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x => let y := (x + n / x) / 2; if y < x then isqrtAux n fuel y else x

/-- A number `S ≥ 1`, normally `⌊√n⌋ + 1` (only `S² ≥ n` is used, and it is checked). -/
def isqrtUp (n : ℕ) : ℕ := isqrtAux n 80 (2 ^ (Nat.log2 n / 2 + 1)) + 1

/-- `B = Σ Q_i Ẑ_i` with the bound chosen by the sign of `Q_i`. -/
def cellB (Q : List ℤ) (c : CellZ) : ℤ :=
  (Q.zipIdx.map fun (q, i) => q * (if 0 ≤ q then c.hi.getD i 0 else c.lo.getD i 0)).sum

def cellS (Q : List ℤ) (c : CellZ) : ℕ := isqrtUp (c.hi.getD 0 0 * cellB Q c).toNat

def cellOKZ (Q : List ℤ) (c : CellZ) : Bool :=
  decide (0 < c.hi.getD 0 0) &&
  decide (c.hi.getD 0 0 * cellB Q c ≤ ((cellS Q c : ℕ) : ℤ) * (cellS Q c : ℕ))

def sumS (Q : List ℤ) (cells : List CellZ) : ℕ := (cells.map (cellS Q)).sum

/-- `N(γ) ≤ NN / 2^f` for `γ = G / 2^e`, checked on the integer cells. -/
def nbarZOK (cells : List CellZ) (G : Array ℤ) (e : ℕ) (NN : ℤ) (f : ℕ) : Bool :=
  let Qp := absSqZ (PsigZ G 1)
  let Qm := absSqZ (PsigZ G (-1))
  decide (Qp.length ≤ 13) && decide (Qm.length ≤ 13) &&
  cells.all (cellOKZ Qp) && cells.all (cellOKZ Qm) &&
  decide (((sumS Qp cells + sumS Qm cells : ℕ) : ℤ) * 10 ^ 20 * 2 ^ f ≤
    NN * 314159265358979323846 * 2 ^ (96 + e))

/-- The rational cut of the integer data: `γ = G / 2^e`. -/
def gammaQ (G : Array ℤ) (e : ℕ) : Array ℚ := G.map (fun z : ℤ => (z : ℚ) / 2 ^ e)

end Harris
