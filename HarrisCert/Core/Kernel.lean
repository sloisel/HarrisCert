module

public import HarrisCert.Core.NbarZ

/-!
# The kernel-checked certificate format (computational core)

Each leaf carries one aggregated cut `γ* = Σ yᵢγᵢ` (weight 1) with a bound `Nup ≥ N̄(γ*)` computed on
`cells ∈ {32, 64, 128, 256}` cells, and its slab and McCormick multipliers. The bisection tree is a
structurally recursive term; large trees are split into subtrees joined by a skeleton.
-/

@[expose] public section

namespace Harris

structure ALeaf where
  opt : Bool
  G : Array ℤ
  e : ℕ
  NN : ℤ
  f : ℕ
  cells : ℕ
  slabs : Array (ℕ × ℚ)
  mcc : Array (ℕ × ℕ × ℚ)

inductive ATree
  | leaf (L : ALeaf)
  | split (v : ℕ) (mid : ℚ) (l r : ATree)

/-- The precomputed data: slab parameters and cell tables. -/
structure Tables where
  slabT : Array (Option ℚ)
  z32 : List CellZ
  z64 : List CellZ
  z128 : List CellZ
  z256 : List CellZ

def Tables.cellsFor (T : Tables) (n : ℕ) : List CellZ :=
  if n = 32 then T.z32 else if n = 64 then T.z64 else if n = 128 then T.z128 else T.z256

/-- The integer cell tables are those of `mkCells`, whose cells are certified. -/
def Tables.Valid (T : Tables) : Prop :=
  T.z32 = (mkCells 32).toList.map CellData.toZ ∧ T.z64 = (mkCells 64).toList.map CellData.toZ ∧
  T.z128 = (mkCells 128).toList.map CellData.toZ ∧ T.z256 = (mkCells 256).toList.map CellData.toZ ∧
  cellsOK (mkCells 32) = true ∧ cellsOK (mkCells 64) = true ∧ cellsOK (mkCells 128) = true ∧
  cellsOK (mkCells 256) = true

/-- A `Cert` carrying only the slab data (to reuse the row definitions of `Check.lean`). -/
def Tables.cert (T : Tables) : Cert :=
  { x0 := X0, cells := 0, slabT := T.slabT, cuts := #[], tree := #[], leaves := #[] }

def ALeaf.rows (T : Tables) (L : ALeaf) (lo hi : Fin 7 → ℚ) : List (ℚ × Row) :=
  (1, cutRow (gammaQ L.G L.e) ((L.NN : ℚ) / 2 ^ L.f)) ::
  ((L.slabs.toList.map fun (i, y) => (y, slabRowOf T.cert i)) ++
   (L.mcc.toList.filterMap fun (j, k, y) => if h : j < 3 then some (y, mccRow lo hi ⟨j, h⟩ k) else none))

def ALeaf.bound (T : Tables) (L : ALeaf) (lo hi : Fin 7 → ℚ) : Q3 :=
  let acc := accum (objVec L.opt, 0) (L.rows T lo hi)
  (List.finRange 10).foldl (fun s j => s + Q3.qmax (acc.1 j) (zLo lo hi j) (zHi lo hi j)) acc.2

def ALeaf.check (T : Tables) (L : ALeaf) (lo hi : Fin 7 → ℚ) : Bool :=
  decide (L.cells = 32 ∨ L.cells = 64 ∨ L.cells = 128 ∨ L.cells = 256) &&
  nbarZOK (T.cellsFor L.cells) L.G L.e L.NN L.f &&
  L.slabs.toList.all (fun iy => decide (0 ≤ iy.2)) &&
  L.mcc.toList.all (fun jky => decide (0 ≤ jky.2.2)) &&
  (if L.opt then (Mq - L.bound T lo hi).nonneg else !(L.bound T lo hi).nonneg)

def ATree.check (T : Tables) : ATree → (Fin 7 → ℚ) → (Fin 7 → ℚ) → Bool
  | .leaf L, lo, hi => L.check T lo hi
  | .split v m l r, lo, hi =>
    if hv : v < 7 then
      decide (lo ⟨v, hv⟩ < m) && decide (m < hi ⟨v, hv⟩) &&
      l.check T lo (Function.update hi ⟨v, hv⟩ m) && r.check T (Function.update lo ⟨v, hv⟩ m) hi
    else false

inductive Skel
  | sub (k : ℕ)
  | split (v : ℕ) (mid : ℚ) (l r : Skel)

def Skel.check (boxes : ℕ → (Fin 7 → ℚ) × (Fin 7 → ℚ)) : Skel → (Fin 7 → ℚ) → (Fin 7 → ℚ) → Bool
  | .sub k, lo, hi => decide (∀ j, lo j = (boxes k).1 j ∧ hi j = (boxes k).2 j)
  | .split v m l r, lo, hi =>
    if hv : v < 7 then
      l.check boxes lo (Function.update hi ⟨v, hv⟩ m) && r.check boxes (Function.update lo ⟨v, hv⟩ m) hi
    else false

end Harris
