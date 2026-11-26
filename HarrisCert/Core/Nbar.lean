module

public import HarrisCert.Core.Check

/-!
# Exact upper bound for `N(γ)` (computation)

`N(γ) = (1/π) Σ_{σ=±1} ∫_{-1}^{1} |P_σ(t)| w(t) dt` with `w = (1+t²)⁻⁴` and
`P_σ(t) = Σ_k σ^k γ_k (1+it)^{2k} (1+t²)^{3-k}` (see `Circle.lean`).

On each of `n` cells `[a,b]` of `[-1,1]` (midpoint `m`, half-width `δ`), with `s = t - m`:
* `E(s) = (1+t²)⁴`, `L(s) = w(m) + w'(m) s` with `w(m) = 1/e₀`, `w'(m) = -e₁/e₀²`;
* `E·L - 1 = s² H(s)` (the checker verifies that the two lowest coefficients vanish);
* a rational `c₂` with `H + c₂ E ≥ 0` for `|s| ≤ δ` (checked by a coefficient bound), so that
  `w ≤ U := L + c₂ s²` on the cell;
* `|P| U ≤ |P|² U / (2λ) + λ U / 2` for any `λ > 0`; both right-hand terms integrate to
  combinations of the moments `μᵢ = ∫ tⁱ U`, which are computed exactly and rounded outward.
-/

@[expose] public section

namespace Harris

/-! ## Polynomials as coefficient lists (constant term first) -/

def pAdd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: pAdd p q

def pScale (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

def pMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => pAdd (pScale a q) (0 :: pMul p q)

def pPow (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => pMul p (pPow p n)

/-- `Σ_{k≥1} |c_k| δ^k`. -/
def tailAbs (p : List ℚ) (δ : ℚ) : ℚ :=
  ((p.drop 1).zipIdx.map fun (c, k) => |c| * δ ^ (k + 1)).sum

/-! ## Complex polynomials `(re, im)` -/

abbrev CPoly := List ℚ × List ℚ
def cpMul (a b : CPoly) : CPoly :=
  (pAdd (pMul a.1 b.1) (pScale (-1) (pMul a.2 b.2)), pAdd (pMul a.1 b.2) (pMul a.2 b.1))
def cpPow (p : CPoly) : ℕ → CPoly
  | 0 => ([1], [])
  | n + 1 => cpMul p (cpPow p n)

/-- `(1+it)^{2k} (1+t²)^{3-k}`. -/
def basisK (k : ℕ) : CPoly := cpMul (cpPow ([1], [0, 1]) (2 * k)) (cpPow ([1, 0, 1], []) (3 - k))

/-- `P_σ` for `γ_k = g_k + i g_{k+4}`, `σ = ±1`. -/
def psigStep (g : Array ℚ) (σ : ℚ) (acc : CPoly) (k : ℕ) : CPoly :=
  let gr := σ ^ k * g.getD k 0
  let gi := σ ^ k * g.getD (k + 4) 0
  let B := basisK k
  (pAdd acc.1 (pAdd (pScale gr B.1) (pScale (-gi) B.2)),
   pAdd acc.2 (pAdd (pScale gr B.2) (pScale gi B.1)))

def Psig (g : Array ℚ) (σ : ℚ) : CPoly := (List.range 4).foldl (psigStep g σ) ([], [])

/-- `|P_σ|² = (Re P)² + (Im P)²` as a real polynomial. -/
def absSq (P : CPoly) : List ℚ := pAdd (pMul P.1 P.1) (pMul P.2 P.2)

/-! ## Cells -/

def roundUp (x : ℚ) (e : ℕ) : ℚ := (⌈x * 2 ^ e⌉ : ℚ) / 2 ^ e
def roundDn (x : ℚ) (e : ℕ) : ℚ := (⌊x * 2 ^ e⌋ : ℚ) / 2 ^ e

structure CellData where
  a : ℚ
  b : ℚ
  m : ℚ
  w0 : ℚ
  w1 : ℚ
  c2 : ℚ
  ok : Bool
  muHi : Array ℚ
  muLo : Array ℚ
  deriving Inhabited, DecidableEq

/-- `∫_a^b tᵖ dt`. -/
def powInt (a b : ℚ) (p : ℕ) : ℚ := (b ^ (p + 1) - a ^ (p + 1)) / (p + 1)

def mkCell (n j : ℕ) : CellData :=
  let a : ℚ := -1 + 2 * j / n
  let b : ℚ := a + 2 / n
  let m : ℚ := (a + b) / 2
  let δ : ℚ := 1 / n
  let E := pPow [1 + m ^ 2, 2 * m, 1] 4
  let e0 := E.getD 0 0
  let e1 := E.getD 1 0
  let w0 := 1 / e0
  let w1 := -e1 / e0 ^ 2
  let G := pAdd (pMul E [w0, w1]) [-1]
  let H := G.drop 2
  let den := e0 - tailAbs E δ
  -- F(c) = (H + c E)(0) - Σ_{k≥1} |(H + c E)_k| δ^k has slope ≥ den > 0, so one step from -h₀/e₀ suffices
  let Fc (c : ℚ) : ℚ := let K := pAdd H (pScale c E); K.getD 0 0 - tailAbs K δ
  let c2a := -(H.getD 0 0) / e0
  let c2raw := c2a + max 0 (-(Fc c2a)) / den
  let c2 := roundUp c2raw 64
  let K := pAdd H (pScale c2 E)
  let ok := decide (G.getD 0 0 = 0) && decide (G.getD 1 0 = 0) && decide (0 < e0) &&
    decide (tailAbs K δ ≤ K.getD 0 0)
  -- U(t) = A0 + A1 t + A2 t²
  let A0 := w0 - w1 * m + c2 * m ^ 2
  let A1 := w1 - 2 * c2 * m
  let A2 := c2
  let mu := (List.range 13).toArray.map fun i =>
    A0 * powInt a b i + A1 * powInt a b (i + 1) + A2 * powInt a b (i + 2)
  { a, b, m, w0, w1, c2, ok, muHi := mu.map (roundUp · 96), muLo := mu.map (roundDn · 96) }

def mkCells (n : ℕ) : Array CellData := (List.range n).toArray.map (mkCell n)

/-- A rational `λ > 0` close to `√(B/A)`. -/
def lamOf (A B : ℚ) : ℚ :=
  if 0 < A ∧ 0 < B then
    let r := B / A
    let k := Nat.sqrt (⌊r * 2 ^ 60⌋.toNat)
    if k = 0 then 1 / 2 ^ 30 else (k : ℚ) / 2 ^ 30
  else 1 / 2 ^ 30

/-- Contribution of one cell: `B/(2λ) + λ A/2` with `A ≥ ∫U` and `B ≥ ∫ Q U`. -/
def cellBound (Q : List ℚ) (c : CellData) : ℚ :=
  let B := (Q.zipIdx.map fun (q, i) => q * (if 0 ≤ q then c.muHi.getD i 0 else c.muLo.getD i 0)).sum
  let A := c.muHi.getD 0 0
  let lam := lamOf A B
  B / (2 * lam) + lam * A / 2

/-- Lower bound for `π` (Mathlib: `Real.pi_gt_d20`). -/
def piLo : ℚ := 314159265358979323846 / 10 ^ 20

def nbar (cells : Array CellData) (g : Array ℚ) : ℚ :=
  let one (σ : ℚ) : ℚ :=
    let Q := absSq (Psig g σ)
    cells.toList.foldl (fun s c => s + cellBound Q c) 0
  (one 1 + one (-1)) / piLo

def cellsOK (cells : Array CellData) : Bool := cells.toList.all (·.ok)

/-- The check of one cut: `N̄(γ) ≤ Nup` (and the degree bound used by the moment arrays). -/
def cutOK (cells : Array CellData) (c : Cut) : Bool :=
  decide ((absSq (Psig c.gamma 1)).length ≤ 13) && decide ((absSq (Psig c.gamma (-1))).length ≤ 13) &&
  decide (nbar cells c.gamma ≤ c.nup)

/-- Cuts `lo, …, hi-1` (for splitting the evaluation into parallel chunks). -/
def chunkOK (C : Cert) (lo hi : ℕ) : Bool :=
  let cells := mkCells C.cells
  (List.range' lo (hi - lo)).all fun i => cutOK cells (C.cuts.getD i default)

/-- Everything except the cuts. -/
def baseOK (C : Cert) : Bool :=
  decide (C.x0 = X0) && decide (0 < C.cells) && cellsOK (mkCells C.cells) &&
  checkNode C C.tree.size 0 rootLo rootHi

/-- The full check (used by the test executable). -/
def checkAll (C : Cert) : Bool := baseOK C && chunkOK C 0 C.cuts.size

end Harris
