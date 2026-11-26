module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Function.Basic
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Exact arithmetic in `ℚ(√3)` (computational core)

`Q3` represents `p + q √3` with `p q : ℚ`; `C3` represents complex numbers over `ℚ(√3)`.
-/

@[expose] public section

namespace Harris

structure Q3 where
  p : ℚ
  q : ℚ
  deriving Inhabited, Repr, DecidableEq

namespace Q3

instance : Add Q3 := ⟨fun a b => ⟨a.p + b.p, a.q + b.q⟩⟩
instance : Neg Q3 := ⟨fun a => ⟨-a.p, -a.q⟩⟩
instance : Sub Q3 := ⟨fun a b => ⟨a.p - b.p, a.q - b.q⟩⟩
instance : Mul Q3 := ⟨fun a b => ⟨a.p * b.p + 3 * a.q * b.q, a.p * b.q + a.q * b.p⟩⟩
instance : Zero Q3 := ⟨⟨0, 0⟩⟩

/-- Embedding of `ℚ`. -/
def ofRat (x : ℚ) : Q3 := ⟨x, 0⟩

/-- Scalar multiplication by a rational. -/
def smul (s : ℚ) (a : Q3) : Q3 := ⟨s * a.p, s * a.q⟩

/-- Exact test of `0 ≤ p + q √3`. -/
def nonneg (a : Q3) : Bool :=
  if 0 ≤ a.p then (if 0 ≤ a.q then true else decide (3 * a.q ^ 2 ≤ a.p ^ 2))
  else (if 0 < a.q then decide (a.p ^ 2 ≤ 3 * a.q ^ 2) else false)

@[simp] lemma add_p (a b : Q3) : (a + b).p = a.p + b.p := rfl
@[simp] lemma add_q (a b : Q3) : (a + b).q = a.q + b.q := rfl
@[simp] lemma sub_p (a b : Q3) : (a - b).p = a.p - b.p := rfl
@[simp] lemma sub_q (a b : Q3) : (a - b).q = a.q - b.q := rfl
@[simp] lemma neg_p (a : Q3) : (-a).p = -a.p := rfl
@[simp] lemma neg_q (a : Q3) : (-a).q = -a.q := rfl
@[simp] lemma mul_p (a b : Q3) : (a * b).p = a.p * b.p + 3 * a.q * b.q := rfl
@[simp] lemma mul_q (a b : Q3) : (a * b).q = a.p * b.q + a.q * b.p := rfl
@[simp] lemma zero_p : (0 : Q3).p = 0 := rfl
@[simp] lemma zero_q : (0 : Q3).q = 0 := rfl
@[simp] lemma ofRat_p (x : ℚ) : (ofRat x).p = x := rfl
@[simp] lemma ofRat_q (x : ℚ) : (ofRat x).q = 0 := rfl
@[simp] lemma smul_p (s : ℚ) (a : Q3) : (smul s a).p = s * a.p := rfl
@[simp] lemma smul_q (s : ℚ) (a : Q3) : (smul s a).q = s * a.q := rfl

/-- `max (κ l) (κ h)` for `κ ∈ ℚ(√3)` and rational `l ≤ h`. -/
def qmax (κ : Q3) (l h : ℚ) : Q3 := if κ.nonneg then κ * ofRat h else κ * ofRat l

end Q3

/-- Complex numbers over `ℚ(√3)`. -/
structure C3 where
  re : Q3
  im : Q3
  deriving Inhabited, Repr

namespace C3

instance : Add C3 := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Neg C3 := ⟨fun a => ⟨-a.re, -a.im⟩⟩
instance : Mul C3 := ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩
instance : Zero C3 := ⟨⟨0, 0⟩⟩
def conj (a : C3) : C3 := ⟨a.re, -a.im⟩
def smul (s : ℚ) (a : C3) : C3 := ⟨Q3.smul s a.re, Q3.smul s a.im⟩
def ofQ3 (x : Q3) : C3 := ⟨x, 0⟩

@[simp] lemma add_re (a b : C3) : (a + b).re = a.re + b.re := rfl
@[simp] lemma add_im (a b : C3) : (a + b).im = a.im + b.im := rfl
@[simp] lemma neg_re (a : C3) : (-a).re = -a.re := rfl
@[simp] lemma neg_im (a : C3) : (-a).im = -a.im := rfl
@[simp] lemma mul_re (a b : C3) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] lemma mul_im (a b : C3) : (a * b).im = a.re * b.im + a.im * b.re := rfl
@[simp] lemma zero_re : (0 : C3).re = 0 := rfl
@[simp] lemma zero_im : (0 : C3).im = 0 := rfl
@[simp] lemma conj_re (a : C3) : (conj a).re = a.re := rfl
@[simp] lemma conj_im (a : C3) : (conj a).im = -a.im := rfl
@[simp] lemma smul_re (s : ℚ) (a : C3) : (smul s a).re = Q3.smul s a.re := rfl
@[simp] lemma smul_im (s : ℚ) (a : C3) : (smul s a).im = Q3.smul s a.im := rfl
@[simp] lemma ofQ3_re (x : Q3) : (ofQ3 x).re = x := rfl
@[simp] lemma ofQ3_im (x : Q3) : (ofQ3 x).im = 0 := rfl

end C3

end Harris
