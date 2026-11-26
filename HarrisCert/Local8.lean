module

public import HarrisCert.Local7

/-!
# Local theorem, part 8: polynomials over `ℚ(√3)` and a kernel-checkable positivity test

Polynomials are coefficient lists (constant term first) over `K3 = ℚ(√3)`; `pev p t` evaluates the real
image under `σ`. The positivity test on `[-1, 1]` splits the interval into `n` cells; on the cell with
centre `m` and half-width `δ` it Taylor-shifts `p` to `q(s) = p(m + s)` and checks
`q₀ - δ · Σ_{k≥1} |q_k| δ^{k-1} ≥ 0`.
-/

open MeasureTheory Complex

@[expose] public section

namespace Harris

abbrev PK := List K3

def padd : PK → PK → PK
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

def psc (c : K3) : PK → PK
  | [] => []
  | a :: p => c * a :: psc c p

def pmul : PK → PK → PK
  | [], _ => []
  | a :: p, q => padd (psc a q) (0 :: pmul p q)

noncomputable def pev : PK → ℝ → ℝ
  | [], _ => 0
  | a :: p, t => σ a + t * pev p t

@[simp] lemma pev_nil (t : ℝ) : pev [] t = 0 := rfl
@[simp] lemma pev_cons (a : K3) (p : PK) (t : ℝ) : pev (a :: p) t = σ a + t * pev p t := rfl

lemma pev_padd (p q : PK) (t : ℝ) : pev (padd p q) t = pev p t + pev q t := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q => simp only [padd, pev_cons, map_add, ih]; ring

lemma pev_psc (c : K3) (p : PK) (t : ℝ) : pev (psc c p) t = σ c * pev p t := by
  induction p with
  | nil => simp [psc]
  | cons a p ih => simp only [psc, pev_cons, map_mul, ih]; ring

lemma pev_pmul (p q : PK) (t : ℝ) : pev (pmul p q) t = pev p t * pev q t := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih => simp only [pmul, pev_padd, pev_psc, pev_cons, map_zero, ih]; ring

/-- Sum of `n` polynomials. -/
def sumP : (n : ℕ) → (Fin n → PK) → PK
  | 0, _ => []
  | n + 1, f => padd (f 0) (sumP n fun i => f i.succ)

lemma pev_sumP (n : ℕ) (f : Fin n → PK) (t : ℝ) : pev (sumP n f) t = ∑ i, pev (f i) t := by
  induction n with
  | zero => simp [sumP]
  | succ n ih => rw [sumP, pev_padd, ih, Fin.sum_univ_succ]

/-! ## Complex polynomials as pairs (real part, imaginary part) -/

abbrev CP := PK × PK

def cadd (a b : CP) : CP := (padd a.1 b.1, padd a.2 b.2)
def cmul (a b : CP) : CP :=
  (padd (pmul a.1 b.1) (psc (-1) (pmul a.2 b.2)), padd (pmul a.1 b.2) (pmul a.2 b.1))
def csc (c : K3) (a : CP) : CP := (psc c a.1, psc c a.2)

noncomputable def cev (a : CP) (t : ℝ) : ℂ := ⟨pev a.1 t, pev a.2 t⟩

lemma cev_cadd (a b : CP) (t : ℝ) : cev (cadd a b) t = cev a t + cev b t := by
  apply Complex.ext <;> simp [cev, cadd, pev_padd]

lemma cev_cmul (a b : CP) (t : ℝ) : cev (cmul a b) t = cev a t * cev b t := by
  apply Complex.ext <;> simp [cev, cmul, pev_padd, pev_psc, pev_pmul] <;> ring

lemma cev_csc (c : K3) (a : CP) (t : ℝ) : cev (csc c a) t = (σ c : ℂ) * cev a t := by
  apply Complex.ext <;> simp [cev, csc, pev_psc]

/-! ## Taylor shift and the cell test -/

def taylor (p : PK) (m : K3) : PK := p.foldr (fun a acc => padd [a] (pmul [m, 1] acc)) []

lemma pev_taylor (p : PK) (m : K3) (s : ℝ) : pev (taylor p m) s = pev p (σ m + s) := by
  induction p with
  | nil => simp [taylor]
  | cons a p ih =>
    simp only [taylor, List.foldr_cons] at ih ⊢
    rw [pev_padd, pev_pmul, ih]; simp

def absK (a : K3) : K3 := if a.nn then a else -a

lemma σ_absK (a : K3) : σ (absK a) = |σ a| := by
  unfold absK
  split_ifs with h
  · rw [abs_of_nonneg ((K3.nn_iff a).mp h)]
  · have : ¬ 0 ≤ σ a := fun h' => h ((K3.nn_iff a).mpr h')
    rw [map_neg, abs_of_neg (lt_of_not_ge this)]

/-- Horner evaluation of the absolute values of the coefficients. -/
def habs (p : PK) (d : K3) : K3 := p.foldr (fun a acc => absK a + d * acc) 0

lemma habs_nil (d : K3) : habs [] d = 0 := rfl
lemma habs_cons (a : K3) (p : PK) (d : K3) : habs (a :: p) d = absK a + d * habs p d := rfl

lemma habs_nonneg (p : PK) (d : K3) (hd : 0 ≤ σ d) : 0 ≤ σ (habs p d) := by
  induction p with
  | nil => simp [habs_nil]
  | cons a p ih =>
    rw [habs_cons, map_add, map_mul, σ_absK]; exact add_nonneg (abs_nonneg _) (mul_nonneg hd ih)

lemma pev_abs_le (p : PK) (d : K3) (hd : 0 ≤ σ d) (s : ℝ) (hs : |s| ≤ σ d) :
    |pev p s| ≤ σ (habs p d) := by
  induction p with
  | nil => simp [habs_nil]
  | cons a p ih =>
    rw [habs_cons, map_add, map_mul, σ_absK, pev_cons]
    have h1 : |σ a + s * pev p s| ≤ |σ a| + |s| * |pev p s| := by
      rw [← abs_mul]; exact abs_add_le _ _
    have h2 := mul_le_mul hs ih (abs_nonneg _) hd
    linarith

def cellOK (p : PK) (m d : K3) : Bool :=
  match taylor p m with
  | [] => true
  | a :: q => (a - d * habs q d).nn

lemma cellOK_sound (p : PK) (m d : K3) (h : cellOK p m d = true) (hd : 0 ≤ σ d) (s : ℝ)
    (hs : |s| ≤ σ d) : 0 ≤ pev p (σ m + s) := by
  rw [← pev_taylor]
  unfold cellOK at h
  cases hq : taylor p m with
  | nil => simp
  | cons a q =>
    rw [hq] at h
    have h1 := (K3.nn_iff _).mp h
    rw [map_sub, map_mul] at h1
    have h2 := pev_abs_le q d hd s hs
    have h3 : -(σ d * σ (habs q d)) ≤ s * pev q s := by
      have := abs_le.mp (le_trans (abs_mul s (pev q s)).le
        (mul_le_mul hs h2 (abs_nonneg _) hd))
      linarith [this.1]
    rw [pev_cons]; linarith

/-- Cell centres `-1 + (2j+1)/n`. -/
def cellC (n j : ℕ) : K3 := ⟨-1 + (2 * j + 1) / n, 0⟩
def cellD (n : ℕ) : K3 := ⟨1 / n, 0⟩

def pcellsOK (p : PK) (n : ℕ) : Bool := (List.range n).all fun j => cellOK p (cellC n j) (cellD n)

lemma σ_rat (p : ℚ) : σ (⟨p, 0⟩ : K3) = (p : ℝ) := by rw [σ_apply]; simp

lemma pcellsOK_sound (p : PK) (n : ℕ) (hn : 0 < n) (h : pcellsOK p n = true) (t : ℝ)
    (ht : |t| ≤ 1) : 0 ≤ pev p t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht' := abs_le.mp ht
  set F := ⌊(t + 1) * n / 2⌋₊ with hF
  set j := min F (n - 1) with hj
  have hjn : j < n := by omega
  have hcell := List.all_eq_true.mp h j (List.mem_range.mpr hjn)
  have hd : σ (cellD n) = 1 / n := by rw [cellD, σ_rat]; push_cast; ring
  have hc : σ (cellC n j) = -1 + (2 * j + 1) / n := by rw [cellC, σ_rat]; push_cast; ring
  have hdpos : 0 ≤ σ (cellD n) := by rw [hd]; positivity
  have hx : 0 ≤ (t + 1) * n / 2 := by apply div_nonneg _ (by norm_num); nlinarith
  have hfl : (F : ℝ) ≤ (t + 1) * n / 2 := Nat.floor_le hx
  have hfl2 : (t + 1) * n / 2 < F + 1 := Nat.lt_floor_add_one _
  have hjR : (j : ℝ) * 2 ≤ (t + 1) * n ∧ (t + 1) * n ≤ j * 2 + 2 := by
    by_cases hcase : F ≤ n - 1
    · have hjeq : j = F := by rw [hj]; exact min_eq_left hcase
      rw [hjeq]; constructor <;> linarith
    · push Not at hcase
      have hjeq : j = n - 1 := by rw [hj]; exact min_eq_right hcase.le
      have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hfl3 : (n : ℝ) ≤ F := by exact_mod_cast (show n ≤ F by omega)
      have ht1 : t = 1 := by
        have : (n : ℝ) * 2 ≤ (t + 1) * n := by linarith
        nlinarith
      rw [hjeq, hcast, ht1]; constructor <;> linarith
  have key : |t - σ (cellC n j)| ≤ σ (cellD n) := by
    rw [hc, hd, show t - (-1 + (2 * (j : ℝ) + 1) / n) = ((t + 1) * n - (2 * j + 1)) / n by
      field_simp; ring, abs_div, abs_of_pos hn', div_le_div_iff_of_pos_right hn', abs_le]
    constructor <;> linarith [hjR.1, hjR.2]
  have := cellOK_sound p (cellC n j) (cellD n) hcell hdpos (t - σ (cellC n j)) key
  rwa [add_sub_cancel] at this

end Harris
