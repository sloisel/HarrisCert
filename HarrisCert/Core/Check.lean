module

public import HarrisCert.Core.Q3

/-!
# The certificate rows and the leaf/tree checker (computational core)

All rows are written as `A ⋅ z ≤ β` with `z = (x₀,…,x₆, w₀, w₁, w₂)` and `w = (x₀x₅, x₁x₆, x₂x₃)`.
-/

@[expose] public section

namespace Harris

/-- The slab level `X₀`. -/
def X0 : ℚ := 7 / 10000

/-- The root box `[-1,1]² × [0,1] × [-1,1]⁴`. -/
def rootLo : Fin 7 → ℚ := ![-1, -1, 0, -1, -1, -1, -1]
def rootHi : Fin 7 → ℚ := fun _ => 1

/-! ## Data -/

structure Cut where
  gamma : Array ℚ
  nup : ℚ
  deriving Inhabited

structure Leaf where
  opt : Bool
  cuts : Array (ℕ × ℚ)
  slabs : Array (ℕ × ℚ)
  mcc : Array (ℕ × ℕ × ℚ)
  deriving Inhabited

inductive Node
  | leaf (k : ℕ)
  | split (v : ℕ) (mid : ℚ) (l r : ℕ)
  deriving Inhabited

structure Cert where
  x0 : ℚ
  cells : ℕ
  slabT : Array (Option ℚ)
  cuts : Array Cut
  tree : Array Node
  leaves : Array Leaf
  deriving Inhabited

/-! ## Rows -/

abbrev Vec := Fin 10 → Q3
abbrev Row := Vec × Q3

/-- `M = 8√3/9` and `r = √3/3` in `ℚ(√3)`. -/
def Mq : Q3 := ⟨0, 8 / 9⟩
def rq : Q3 := ⟨0, 1 / 3⟩

/-- The cut `Re Σ γ_k a_k ≤ Nup`, with `γ_k = g_k + i g_{k+4}`. -/
def cutRow (g : Array ℚ) (nup : ℚ) : Row :=
  (fun j => Q3.ofRat (match j.val with
    | 0 => g.getD 0 0 | 1 => -g.getD 4 0 | 2 => g.getD 1 0 | 3 => g.getD 2 0
    | 4 => -g.getD 6 0 | 5 => g.getD 3 0 | 6 => -g.getD 7 0 | _ => 0), Q3.ofRat nup)

/-- `u = e^{iα/2}` from the rational parameter `t` (`none` means `u = -1`). -/
def uOf : Option ℚ → ℚ × ℚ
  | none => (-1, 0)
  | some t => ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

/-- Moments of `h_α` in `ℚ(√3)`. -/
def aorbC (u : ℚ × ℚ) : Fin 4 → C3 :=
  let U : C3 := ⟨Q3.ofRat u.1, Q3.ofRat u.2⟩
  let Ub := C3.conj U
  ![0, C3.ofQ3 rq * U, C3.smul (2 / 3) Ub, C3.smul (-2 / 3) (C3.ofQ3 rq * (Ub * Ub * Ub))]

def reflC (b : Fin 4 → C3) : Fin 4 → C3 := fun k => C3.conj (b (Fin.rev k))

/-- `s` with `Re φ(a(x), b) = Σ s_j x_j`. -/
def slabS (b : Fin 4 → C3) : Fin 7 → Q3 :=
  let β0 := b 3
  let β1 := C3.smul (-2) (b 2)
  let β2 := C3.smul (-2) (b 1)
  let β3 := b 0
  ![β0.re, -β0.im, β1.re, β2.re, -β2.im, β3.re, -β3.im]

/-- The slab `X(a, b) ≥ X0`, i.e. `-s ⋅ x ≤ M - X0`. -/
def slabRow (x0 : ℚ) (b : Fin 4 → C3) : Row :=
  (fun j => if h : j.val < 7 then -(slabS b ⟨j.val, h⟩) else 0, Mq - Q3.ofRat x0)

/-- Slab row number `i`: point `i / 2`, orbit (`i` even) or reflected orbit (`i` odd). -/
def slabRowOf (C : Cert) (i : ℕ) : Row :=
  let b := aorbC (uOf (C.slabT.getD (i / 2) none))
  slabRow C.x0 (if i % 2 = 0 then b else reflC b)

/-- The products `w_j = x_p x_s`. -/
def pairP : Fin 3 → Fin 7 := ![0, 1, 2]
def pairS : Fin 3 → Fin 7 := ![5, 6, 3]

/-- A vector with three possibly nonzero entries (the indices are distinct in our use). -/
def vec3 (iw : Fin 10) (cw : Q3) (is : Fin 10) (cs : Q3) (ip : Fin 10) (cp : Q3) : Vec :=
  fun j => if j = iw then cw else if j = is then cs else if j = ip then cp else 0

def wIdx (j : Fin 3) : Fin 10 := ⟨7 + j.val, by omega⟩
def xIdx (i : Fin 7) : Fin 10 := ⟨i.val, by omega⟩

/-- McCormick row `k ∈ {0,1,2,3}` for the product `j`, on the box `[lo, hi]`. -/
def mccRow (lo hi : Fin 7 → ℚ) (j : Fin 3) (k : ℕ) : Row :=
  let p := pairP j; let s := pairS j
  let lp := lo p; let ls := lo s; let hp := hi p; let hs := hi s
  match k with
  | 0 => (vec3 (wIdx j) (Q3.ofRat (-1)) (xIdx s) (Q3.ofRat lp) (xIdx p) (Q3.ofRat ls), Q3.ofRat (lp * ls))
  | 1 => (vec3 (wIdx j) (Q3.ofRat (-1)) (xIdx s) (Q3.ofRat hp) (xIdx p) (Q3.ofRat hs), Q3.ofRat (hp * hs))
  | 2 => (vec3 (wIdx j) (Q3.ofRat 1) (xIdx s) (Q3.ofRat (-hp)) (xIdx p) (Q3.ofRat (-ls)),
          Q3.ofRat (-(hp * ls)))
  | _ => (vec3 (wIdx j) (Q3.ofRat 1) (xIdx s) (Q3.ofRat (-lp)) (xIdx p) (Q3.ofRat (-hs)),
          Q3.ofRat (-(lp * hs)))

/-! ## Leaf check -/

/-- Fold `κ ← κ - y A`, `b ← b + y β` over the weighted rows. -/
def accum (init : Vec × Q3) (rows : List (ℚ × Row)) : Vec × Q3 :=
  rows.foldl (fun acc yr => (fun j => acc.1 j - Q3.smul yr.1 (yr.2.1 j), acc.2 + Q3.smul yr.1 yr.2.2)) init

/-- Box of `z`: `x` from `[lo, hi]`, `w_j` from the four endpoint products. -/
def zLo (lo hi : Fin 7 → ℚ) (j : Fin 10) : ℚ :=
  if h : j.val < 7 then lo ⟨j.val, h⟩ else
    let jj : Fin 3 := ⟨j.val - 7, by omega⟩
    let p := pairP jj; let s := pairS jj
    min (min (lo p * lo s) (lo p * hi s)) (min (hi p * lo s) (hi p * hi s))
def zHi (lo hi : Fin 7 → ℚ) (j : Fin 10) : ℚ :=
  if h : j.val < 7 then hi ⟨j.val, h⟩ else
    let jj : Fin 3 := ⟨j.val - 7, by omega⟩
    let p := pairP jj; let s := pairS jj
    max (max (lo p * lo s) (lo p * hi s)) (max (hi p * lo s) (hi p * hi s))

/-- The objective `f = -Re q = -2 w₀ + 2 w₁ + 4 w₂` (or `0` for an infeasibility certificate). -/
def objVec (opt : Bool) : Vec :=
  fun j => if opt then (if j.val = 7 then Q3.ofRat (-2) else if j.val = 8 then Q3.ofRat 2
    else if j.val = 9 then Q3.ofRat 4 else 0) else 0

def leafRows (C : Cert) (L : Leaf) (lo hi : Fin 7 → ℚ) : List (ℚ × Row) :=
  (L.cuts.toList.map fun (i, y) => (y, cutRow (C.cuts.getD i default).gamma (C.cuts.getD i default).nup)) ++
  (L.slabs.toList.map fun (i, y) => (y, slabRowOf C i)) ++
  (L.mcc.toList.filterMap fun (j, k, y) => if h : j < 3 then some (y, mccRow lo hi ⟨j, h⟩ k) else none)

def leafBound (C : Cert) (L : Leaf) (lo hi : Fin 7 → ℚ) : Q3 :=
  let acc := accum (objVec L.opt, 0) (leafRows C L lo hi)
  (List.finRange 10).foldl (fun s j => s + Q3.qmax (acc.1 j) (zLo lo hi j) (zHi lo hi j)) acc.2

def leafIndicesOK (C : Cert) (L : Leaf) : Bool :=
  L.cuts.all (fun (i, y) => decide (i < C.cuts.size) && decide (0 ≤ y)) &&
  L.slabs.all (fun (i, y) => decide (i < 2 * C.slabT.size) && decide (0 ≤ y)) &&
  L.mcc.all (fun (_, _, y) => decide (0 ≤ y))

def checkLeaf (C : Cert) (L : Leaf) (lo hi : Fin 7 → ℚ) : Bool :=
  leafIndicesOK C L &&
  (if L.opt then (Mq - leafBound C L lo hi).nonneg else !(leafBound C L lo hi).nonneg)

/-! ## Tree check -/

def checkNode (C : Cert) : ℕ → ℕ → (Fin 7 → ℚ) → (Fin 7 → ℚ) → Bool
  | 0, _, _, _ => false
  | fuel + 1, id, lo, hi =>
    match C.tree[id]? with
    | none => false
    | some (.leaf k) =>
      match C.leaves[k]? with
      | none => false
      | some L => checkLeaf C L lo hi
    | some (.split v m l r) =>
      if hv : v < 7 then
        let vf : Fin 7 := ⟨v, hv⟩
        decide (lo vf < m) && decide (m < hi vf) &&
        checkNode C fuel l lo (Function.update hi vf m) &&
        checkNode C fuel r (Function.update lo vf m) hi
      else false

/-! ## Parsing -/

end Harris
