import LeanForest.H0FTab
import LeanForest.Base.SplitCert

/-! **Rational upper bounds of the per-tree moments.** From the kernel-checked codeword tables
(`f(u)` exactly for `u ≤ 40`, `f(u) ≤ 1` beyond) the closed forms of `Ψ1(n)` and `Ψ2(n)` give
rational upper bounds, rounded up to `2^-128` after each stage. -/

open ENNReal

namespace LeanForest.Security.H0

variable [Params]

open Concrete LeanForest.Base.H0

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### The tables as upper bounds -/

/-- Upper bound of `f(u)`: exact for `u ≤ 40`, one beyond. -/
def fQ (u : ℕ) : ℚ := if u ≤ 40 then (fTab.getD u 0 : ℚ) / 256 ^ (u + 1) else 1

/-- Upper bound of `f2(u)`. -/
def f2Q (u : ℕ) : ℚ := if u ≤ 40 then (f2Tab.getD u 0 : ℚ) / 256 ^ (u + 2) else 1

theorem fR_le_fQ (u : ℕ) : fR u ≤ (fQ u : ℝ) := by
  unfold fQ
  split_ifs with hu
  · rw [fR_num, fNum, ← getD_sumTL 40 u hu, fTab_eq]
    push_cast
    rfl
  · exact_mod_cast (fR_unit u).2

theorem f2R_le_f2Q (u : ℕ) : f2R u ≤ (f2Q u : ℝ) := by
  unfold f2Q
  split_ifs with hu
  · rw [f2R_num, f2Num, ← getD_sumTL 40 u hu, f2Tab_eq]
    push_cast
    rfl
  · exact_mod_cast (f2R_unit u).2

/-! ### Binomial rows -/

/-- The rows of Pascal's triangle. -/
def pascal : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => List.zipWith (· + ·) (0 :: pascal n) (pascal n ++ [0])

theorem length_pascal : ∀ n, (pascal n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [pascal, List.length_zipWith, length_pascal n]

theorem pascal_getD : ∀ n k, (pascal n).getD k 0 = n.choose k
  | 0, k => by cases k <;> simp [pascal]
  | n + 1, k => by
      have hl := length_pascal n
      rcases lt_or_ge k (n + 2) with hk | hk
      · rw [List.getD_eq_getElem _ _ (by simp [pascal, List.length_zipWith, hl]; omega)]
        simp only [pascal, List.getElem_zipWith]
        cases k with
        | zero =>
            have h0 := pascal_getD n 0
            rw [List.getD_eq_getElem _ _ (by omega)] at h0
            rw [List.getElem_cons_zero, List.getElem_append_left (by omega), h0]
            simp
        | succ k =>
            rw [List.getElem_cons_succ, Nat.choose_succ_succ]
            have h1 := pascal_getD n k
            have h2 := pascal_getD n (k + 1)
            rw [List.getD_eq_getElem _ _ (by omega)] at h1
            rw [← h1]
            rcases lt_or_ge (k + 1) (n + 1) with hk' | hk'
            · rw [List.getElem_append_left (by omega)]
              rw [List.getD_eq_getElem _ _ (by omega)] at h2
              rw [h2]
            · rw [List.getElem_append_right (by omega)]
              have : k + 1 - (pascal n).length = 0 := by omega
              simp only [this, List.getElem_singleton, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]
      · rw [List.getD_eq_default _ _ (by simp [pascal, List.length_zipWith, hl]; omega),
          Nat.choose_eq_zero_of_lt (by omega)]

/-- A sum over `range` as a list sum. -/
theorem list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]; simp


/-! ### The rational bounds -/

/-- A binomial weight `C(n,i) a^i b^(n-i)`. -/
def binQ (n i : ℕ) (a b : ℚ) : ℚ := ((pascal n).getD i 0 : ℚ) * a ^ i * b ^ (n - i)

/-- The bound of `μ_i`. -/
def μQ (i : ℕ) : ℚ := rup (((List.range (i + 1)).map fun u => binQ i u (1 / 8) (7 / 8) * fQ u).sum) 128

/-- The bounds of `μ_i`, `i ≤ 150`. -/
def μL : List ℚ := (List.range 151).map μQ

/-- The bound of `Σ_u C(s,u) f(u) f(s-u)`. -/
def hQ (s : ℕ) : ℚ :=
  rup (((List.range (s + 1)).map fun u => ((pascal s).getD u 0 : ℚ) * fQ u * fQ (s - u)).sum) 128

def hL : List ℚ := (List.range 151).map hQ

/-- The bound of `ν_i`. -/
def νQ (i : ℕ) : ℚ :=
  rup (1 / 8 * ((List.range (i + 1)).map fun u => binQ i u (1 / 8) (7 / 8) * f2Q u).sum +
    7 / 8 * ((List.range (i + 1)).map fun s => binQ i s (1 / 8) (6 / 8) * hL.getD s 0).sum) 128

def νL : List ℚ := (List.range 151).map νQ

/-- The bound of `Σ_i C(s,i) μ_i^2 μ_(s-i)^2`. -/
def gQ (s : ℕ) : ℚ :=
  rup (((List.range (s + 1)).map fun i => ((pascal s).getD i 0 : ℚ) * μL.getD i 0 ^ 2 * μL.getD (s - i) 0 ^ 2).sum) 128

def gL : List ℚ := (List.range 151).map gQ

/-- The bound of `Ψ1(n)`. -/
def P1Q (n : ℕ) : ℚ :=
  rup (((List.range (n + 1)).map fun i => binQ n i (1 / 16) (15 / 16) * μL.getD i 0 ^ 2).sum) 128

/-- The bound of `Ψ2(n)`. -/
def P2Q (n : ℕ) : ℚ :=
  rup (1 / 16 * ((List.range (n + 1)).map fun i => binQ n i (1 / 16) (15 / 16) * νL.getD i 0 ^ 2).sum +
    15 / 16 * ((List.range (n + 1)).map fun s => binQ n s (1 / 16) (14 / 16) * gL.getD s 0).sum) 128

/-! ### Soundness -/

theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) (N i : ℕ) (hi : i < N) :
    ((List.range N).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem binQ_cast (n i : ℕ) (a b : ℚ) :
    ((binQ n i a b : ℚ) : ℝ) = (a : ℝ) ^ i * (b : ℝ) ^ (n - i) * (n.choose i : ℝ) := by
  unfold binQ
  rw [pascal_getD]
  push_cast
  ring

theorem binQ_nonneg (n i : ℕ) {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ binQ n i a b := by
  unfold binQ; positivity

theorem rup_ge_real {x : ℚ} {y : ℝ} (h : y ≤ (x : ℝ)) (P : ℕ) : y ≤ ((rup x P : ℚ) : ℝ) :=
  le_trans h (by exact_mod_cast le_rup x P)

theorem fQ_nonneg (u : ℕ) : (0 : ℝ) ≤ (fQ u : ℝ) := le_trans (fR_unit u).1 (fR_le_fQ u)

theorem μR_bounds (i : ℕ) : 0 ≤ μR i ∧ μR i ≤ (μQ i : ℝ) := by
  rw [μR_eq]
  refine ⟨Finset.sum_nonneg fun u _ => mul_nonneg (by positivity) (fR_unit u).1, ?_⟩
  unfold μQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun u _ => ?_
  rw [binQ_cast]
  push_cast
  exact mul_le_mul_of_nonneg_left (fR_le_fQ u) (by positivity)

theorem μL_getD (i : ℕ) (hi : i ≤ 150) : μL.getD i 0 = μQ i := getD_map_range μQ 0 151 i (by omega)


theorem hL_getD (s : ℕ) (hs : s ≤ 150) : hL.getD s 0 = hQ s := getD_map_range hQ 0 151 s (by omega)
theorem νL_getD (i : ℕ) (hi : i ≤ 150) : νL.getD i 0 = νQ i := getD_map_range νQ 0 151 i (by omega)
theorem gL_getD (s : ℕ) (hs : s ≤ 150) : gL.getD s 0 = gQ s := getD_map_range gQ 0 151 s (by omega)

theorem hR_le (s : ℕ) :
    ∑ u ∈ Finset.range (s + 1), (s.choose u : ℝ) * fR u * fR (s - u) ≤ (hQ s : ℝ) := by
  unfold hQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun u _ => ?_
  rw [pascal_getD]
  push_cast
  have h1 := fR_unit u
  have h2 := fR_unit (s - u)
  have h3 := fR_le_fQ u
  have h4 := fR_le_fQ (s - u)
  have hc : (0 : ℝ) ≤ s.choose u := Nat.cast_nonneg _
  calc (s.choose u : ℝ) * fR u * fR (s - u) ≤ (s.choose u : ℝ) * (fQ u : ℝ) * fR (s - u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc) h2.1
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (mul_nonneg hc (fQ_nonneg u))

theorem νR_bounds (i : ℕ) (hi : i ≤ 150) : 0 ≤ νR i ∧ νR i ≤ (νQ i : ℝ) := by
  unfold νR
  rw [νeqR_eq, νneR_eq]
  constructor
  · refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ => mul_nonneg (by positivity)
      (f2R_unit u).1)) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun u _ => mul_nonneg (mul_nonneg (by positivity) (fR_unit u).1) (fR_unit _).1)))
  unfold νQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range, list_sum_range]
  push_cast
  refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) (by norm_num))
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s hs => ?_) (by norm_num))
  · rw [binQ_cast]
    push_cast
    exact mul_le_mul_of_nonneg_left (f2R_le_f2Q u) (by positivity)
  · rw [binQ_cast, hL_getD s (by have := Finset.mem_range.1 hs; omega)]
    push_cast
    exact mul_le_mul_of_nonneg_left (hR_le s) (by positivity)

theorem gR_le (s : ℕ) (hs : s ≤ 150) :
    ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * μR i ^ 2 * μR (s - i) ^ 2 ≤ (gQ s : ℝ) := by
  unfold gQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [pascal_getD, μL_getD i (by omega), μL_getD (s - i) (by omega)]
  push_cast
  have h1 := μR_bounds i
  have h2 := μR_bounds (s - i)
  gcongr
  · exact h1.1
  · exact h1.2
  · exact h2.1
  · exact h2.2

/-- **The first moment bound.** -/
theorem Ψ1R_le (n : ℕ) (hn : n ≤ 150) : Ψ1R n ≤ (P1Q n : ℝ) := by
  rw [Ψ1R_eq]
  unfold P1Q
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [binQ_cast, μL_getD i (by omega)]
  push_cast
  have h1 := μR_bounds i
  gcongr
  · exact h1.1
  · exact h1.2

/-- **The second moment bound.** -/
theorem Ψ2R_le (n : ℕ) (hn : n ≤ 150) : Ψ2R n ≤ (P2Q n : ℝ) := by
  rw [Ψ2R_eq]
  unfold P2Q
  refine rup_ge_real ?_ 128
  rw [list_sum_range, list_sum_range]
  push_cast
  refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by norm_num))
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s hs => ?_) (by norm_num))
  · have hi' := Finset.mem_range.1 hi
    rw [binQ_cast, νL_getD i (by omega)]
    push_cast
    have h1 := νR_bounds i (by omega)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1.1 h1.2 2) (by positivity)
  · have hs' := Finset.mem_range.1 hs
    rw [binQ_cast, gL_getD s (by omega)]
    push_cast
    exact mul_le_mul_of_nonneg_left (gR_le s (by omega)) (by positivity)

/-! ### Integer numerators for the kernel

Every bound above is a dyadic rational. The kernel computes the numerators in `ℕ`: a binomial sum is
one pass over a row of Pascal's triangle, a row of powers and the earlier numerators (`dot3`), with no
list lookups inside the sum, and rounding up is a ceiling division (`cdiv`, `rup_dyadic`). Each
`…NL` list holds the numerators of the corresponding `…L` list or `…Q` function over a fixed power
of two. -/

/-- The sum of `a_i b_i c_i` over the common length. -/
def dot3 : List ℕ → List ℕ → List ℕ → ℕ
  | a :: as, b :: bs, c :: cs => a * b * c + dot3 as bs cs
  | _, _, _ => 0

theorem dot3_eq : ∀ (l1 l2 l3 : List ℕ) (n : ℕ), l1.length ≤ n →
    dot3 l1 l2 l3 = ∑ i ∈ Finset.range n, l1.getD i 0 * l2.getD i 0 * l3.getD i 0
  | _ :: as, _ :: bs, _ :: cs, n + 1, h => by
      rw [Finset.sum_range_succ', dot3, dot3_eq as bs cs n (by simpa using h)]
      simp [add_comm]
  | _ :: _, _ :: _, _ :: _, 0, h => by simp at h
  | [], _, _, n, _ => by simp [dot3]
  | _ :: _, [], _, n, _ => by simp [dot3]
  | _ :: _, _ :: _, [], n, _ => by simp [dot3]

/-- The powers `b^(n-i)`, `i ≤ n`. -/
def powsR (b n : ℕ) : List ℕ := (List.range (n + 1)).map fun i => b ^ (n - i)

/-- `Σ_i C(n,i) b^(n-i) v_i`. -/
def binN (b n : ℕ) (v : List ℕ) : ℕ := dot3 (pascal n) (powsR b n) v

/-- `Σ_i C(s,i) v_i w_(s-i)`. -/
def convN (s : ℕ) (v w : List ℕ) : ℕ := dot3 (pascal s) v (w.take (s + 1)).reverse

theorem binN_eq (b n : ℕ) (v : List ℕ) :
    binN b n v = ∑ i ∈ Finset.range (n + 1), n.choose i * b ^ (n - i) * v.getD i 0 := by
  rw [binN, dot3_eq _ _ _ (n + 1) (by rw [length_pascal])]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [pascal_getD, powsR, getD_map_range _ _ _ _ (Finset.mem_range.1 hi)]

theorem convN_eq (s : ℕ) (v w : List ℕ) (hw : s < w.length) :
    convN s v w = ∑ i ∈ Finset.range (s + 1), s.choose i * v.getD i 0 * w.getD (s - i) 0 := by
  rw [convN, dot3_eq _ _ _ (s + 1) (by rw [length_pascal])]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.1 hi
  have hlen : ((w.take (s + 1)).reverse).length = s + 1 := by simp; omega
  rw [pascal_getD, List.getD_eq_getElem ((w.take (s + 1)).reverse) 0 (by omega),
    List.getD_eq_getElem w 0 (by omega), List.getElem_reverse, List.getElem_take]
  congr 2
  simp only [List.length_take]
  omega

/-- `⌈a / b⌉`. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem ceil_cdiv (A B : ℕ) (hB : 0 < B) : ⌈(A : ℚ) / B⌉ = (cdiv A B : ℤ) := by
  unfold cdiv
  have h1 := Nat.lt_div_mul_add (a := A + B - 1) hB
  have h2 := Nat.div_mul_le_self (A + B - 1) B
  generalize (A + B - 1) / B = q at *
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  rw [Int.ceil_eq_iff, Int.cast_natCast, lt_div_iff₀ hB', div_le_iff₀ hB']
  constructor
  · have : q * B < A + B := by omega
    have : ((q * B : ℕ) : ℚ) < (A + B : ℕ) := by exact_mod_cast this
    push_cast at this
    linarith
  · have : A ≤ q * B := by omega
    exact_mod_cast this

theorem rup_dyadic (A E : ℕ) (hE : 128 ≤ E) :
    rup ((A : ℚ) / 2 ^ E) 128 = (cdiv A (2 ^ (E - 128)) : ℚ) / 2 ^ 128 := by
  unfold rup
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hE
  have : (A : ℚ) / 2 ^ (128 + k) * 2 ^ 128 = (A : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [this, ceil_cdiv _ _ (by positivity), Nat.add_sub_cancel_left]
  push_cast
  rfl

/-- Binomial weights with a dyadic denominator. -/
theorem binQ_sum (a b n e : ℕ) (x : ℕ → ℕ) :
    ∑ u ∈ Finset.range (n + 1), binQ n u (1 / 2 ^ a) (b / 2 ^ a) * ((x u : ℚ) / 2 ^ e) =
      ((∑ u ∈ Finset.range (n + 1), n.choose u * b ^ (n - u) * x u : ℕ) : ℚ) / 2 ^ (a * n + e) := by
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu))
  unfold binQ
  rw [pascal_getD, Nat.add_sub_cancel_left, mul_add, pow_add, pow_add, pow_mul, pow_mul]
  have ht : (2 : ℚ) ^ a ≠ 0 := by positivity
  generalize (2 : ℚ) ^ a = t at *
  simp only [div_pow, one_pow]
  field_simp

/-- Binomial convolutions with dyadic denominators. -/
theorem pascal_conv_sum (s e e' : ℕ) (x y : ℕ → ℕ) :
    ∑ u ∈ Finset.range (s + 1), ((pascal s).getD u 0 : ℚ) * ((x u : ℚ) / 2 ^ e) * ((y (s - u) : ℚ) / 2 ^ e') =
      ((∑ u ∈ Finset.range (s + 1), s.choose u * x u * y (s - u) : ℕ) : ℚ) / 2 ^ (e + e') := by
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [pascal_getD]
  field_simp
  ring

/-- The numerators of `fQ` over `2^328`. -/
def fNL : List ℕ := (List.range 151).map fun u => if u ≤ 40 then (fTab.getD u 0).toNat * 2 ^ (320 - 8 * u) else 2 ^ 328

/-- The numerators of `f2Q` over `2^336`. -/
def f2NL : List ℕ := (List.range 151).map fun u => if u ≤ 40 then (f2Tab.getD u 0).toNat * 2 ^ (320 - 8 * u) else 2 ^ 336

theorem fTab_nonneg (u : ℕ) (hu : u ≤ 40) : 0 ≤ fTab.getD u 0 := by
  rw [← fTab_eq, getD_sumTL 40 u hu]
  exact (fNum_mem u).1

theorem f2Tab_nonneg (u : ℕ) (hu : u ≤ 40) : 0 ≤ f2Tab.getD u 0 := by
  rw [← f2Tab_eq, getD_sumTL 40 u hu]
  exact (f2Num_mem u).1

theorem fQ_eq (u : ℕ) (hu : u ≤ 150) : fQ u = (fNL.getD u 0 : ℚ) / 2 ^ 328 := by
  rw [fNL, getD_map_range _ _ _ _ (by omega), fQ]
  split_ifs with h
  · have hc : ((fTab.getD u 0).toNat : ℚ) = (fTab.getD u 0 : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (fTab_nonneg u h)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hc, show (256 : ℚ) ^ (u + 1) = 2 ^ (8 * u + 8) by
        rw [show (256 : ℚ) = 2 ^ 8 by norm_num, ← pow_mul]; ring_nf,
      show (2 : ℚ) ^ 328 = 2 ^ (320 - 8 * u) * 2 ^ (8 * u + 8) by rw [← pow_add]; congr 1; omega]
    field_simp
  · rw [Nat.cast_pow, Nat.cast_ofNat, div_self (by positivity)]

theorem f2Q_eq (u : ℕ) (hu : u ≤ 150) : f2Q u = (f2NL.getD u 0 : ℚ) / 2 ^ 336 := by
  rw [f2NL, getD_map_range _ _ _ _ (by omega), f2Q]
  split_ifs with h
  · have hc : ((f2Tab.getD u 0).toNat : ℚ) = (f2Tab.getD u 0 : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (f2Tab_nonneg u h)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hc, show (256 : ℚ) ^ (u + 2) = 2 ^ (8 * u + 16) by
        rw [show (256 : ℚ) = 2 ^ 8 by norm_num, ← pow_mul]; ring_nf,
      show (2 : ℚ) ^ 336 = 2 ^ (320 - 8 * u) * 2 ^ (8 * u + 16) by rw [← pow_add]; congr 1; omega]
    field_simp
  · rw [Nat.cast_pow, Nat.cast_ofNat, div_self (by positivity)]

theorem binQ_sum_list (a b n e : ℕ) (v : List ℕ) (g : ℕ → ℚ) (p q : ℚ) (hp : p = 1 / 2 ^ a) (hq : q = b / 2 ^ a)
    (hg : ∀ u ≤ n, g u = (v.getD u 0 : ℚ) / 2 ^ e) :
    ∑ u ∈ Finset.range (n + 1), binQ n u p q * g u = (binN b n v : ℚ) / 2 ^ (a * n + e) := by
  rw [binN_eq, ← binQ_sum a b n e (fun u => v.getD u 0), hp, hq]
  exact Finset.sum_congr rfl fun u hu => by rw [hg u (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu))]

theorem pascal_conv_list (s e e' : ℕ) (v w : List ℕ) (hw : s < w.length) (g g' : ℕ → ℚ)
    (hg : ∀ u ≤ s, g u = (v.getD u 0 : ℚ) / 2 ^ e) (hg' : ∀ u ≤ s, g' u = (w.getD u 0 : ℚ) / 2 ^ e') :
    ∑ u ∈ Finset.range (s + 1), ((pascal s).getD u 0 : ℚ) * g u * g' (s - u) =
      (convN s v w : ℚ) / 2 ^ (e + e') := by
  rw [convN_eq s v w hw, ← pascal_conv_sum s e e' (fun u => v.getD u 0) (fun u => w.getD u 0)]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
  rw [hg u hu, hg' (s - u) (by omega)]

theorem getD_map_sq (l : List ℕ) (i : ℕ) : (l.map (· ^ 2)).getD i 0 = l.getD i 0 ^ 2 := by
  rcases lt_or_ge i l.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ h]
    rfl

/-- The numerators of `μL` over `2^128`. -/
def μNL : List ℕ := (List.range 151).map fun i => cdiv (binN 7 i fNL) (2 ^ (3 * i + 200))

theorem μQ_eq (i : ℕ) (hi : i ≤ 150) : μQ i = (μNL.getD i 0 : ℚ) / 2 ^ 128 := by
  rw [μNL, getD_map_range _ _ _ _ (by omega), μQ, list_sum_range,
    binQ_sum_list 3 7 i 328 fNL fQ (1 / 8) (7 / 8) (by norm_num) (by norm_num) (fun u hu => fQ_eq u (by omega)),
    rup_dyadic _ _ (by omega), show 3 * i + 328 - 128 = 3 * i + 200 by omega]

/-- The numerators of `hL` over `2^128`. -/
def hNL : List ℕ := (List.range 151).map fun s => cdiv (convN s fNL fNL) (2 ^ 528)

theorem hQ_eq (s : ℕ) (hs : s ≤ 150) : hQ s = (hNL.getD s 0 : ℚ) / 2 ^ 128 := by
  rw [hNL, getD_map_range _ _ _ _ (by omega), hQ, list_sum_range,
    pascal_conv_list s 328 328 fNL fNL (by rw [fNL, List.length_map, List.length_range]; omega) fQ fQ (fun u hu => fQ_eq u (by omega))
      (fun u hu => fQ_eq u (by omega)), rup_dyadic _ _ (by norm_num)]

/-- The numerators of `νL` over `2^128`. -/
def νNL : List ℕ := (List.range 151).map fun i =>
  cdiv (binN 7 i f2NL + 7 * 2 ^ 208 * binN 6 i hNL) (2 ^ (3 * i + 211))

theorem νQ_eq (i : ℕ) (hi : i ≤ 150) : νQ i = (νNL.getD i 0 : ℚ) / 2 ^ 128 := by
  rw [νNL, getD_map_range _ _ _ _ (by omega), νQ, list_sum_range, list_sum_range,
    binQ_sum_list 3 7 i 336 f2NL f2Q (1 / 8) (7 / 8) (by norm_num) (by norm_num) (fun u hu => f2Q_eq u (by omega)),
    binQ_sum_list 3 6 i 128 hNL (fun s => hL.getD s 0) (1 / 8) (6 / 8) (by norm_num) (by norm_num)
      (fun s hs => by rw [hL_getD s (by omega), hQ_eq s (by omega)])]
  have e : (1 / 8 : ℚ) * ((binN 7 i f2NL : ℕ) / 2 ^ (3 * i + 336)) + 7 / 8 * ((binN 6 i hNL : ℕ) / 2 ^ (3 * i + 128)) =
      ((binN 7 i f2NL + 7 * 2 ^ 208 * binN 6 i hNL : ℕ) : ℚ) / 2 ^ (3 * i + 339) := by
    push_cast
    rw [pow_add 2 (3 * i) 336, pow_add 2 (3 * i) 128, pow_add 2 (3 * i) 339]
    field_simp
    ring
  rw [e, rup_dyadic _ _ (by omega), show 3 * i + 339 - 128 = 3 * i + 211 by omega]

/-- The squared numerators of `μL`, over `2^256`. -/
def μ2NL : List ℕ := μNL.map (· ^ 2)

theorem μL_sq (i : ℕ) (hi : i ≤ 150) : μL.getD i 0 ^ 2 = (μ2NL.getD i 0 : ℚ) / 2 ^ 256 := by
  rw [μL_getD i hi, μQ_eq i hi, μ2NL, getD_map_sq]
  push_cast
  ring

/-- The numerators of `gL` over `2^128`. -/
def gNL : List ℕ := (List.range 151).map fun s => cdiv (convN s μ2NL μ2NL) (2 ^ 384)

theorem gQ_eq (s : ℕ) (hs : s ≤ 150) : gQ s = (gNL.getD s 0 : ℚ) / 2 ^ 128 := by
  rw [gNL, getD_map_range _ _ _ _ (by omega), gQ, list_sum_range,
    pascal_conv_list s 256 256 μ2NL μ2NL (by rw [μ2NL, μNL, List.length_map, List.length_map, List.length_range]; omega) (fun i => μL.getD i 0 ^ 2) (fun i => μL.getD i 0 ^ 2)
      (fun u hu => μL_sq u (by omega)) (fun u hu => μL_sq u (by omega)), rup_dyadic _ _ (by norm_num)]

theorem map_range_eq {g : ℕ → ℚ} {l : List ℕ} (hl : l.length = 151)
    (h : ∀ n ≤ 150, g n = (l.getD n 0 : ℚ) / 2 ^ 128) :
    (List.range 151).map g = l.map fun x : ℕ => (x : ℚ) / 2 ^ 128 := by
  refine List.ext_getElem (by simp [hl]) fun n h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_map, List.getElem_range, h n (by omega), List.getD_eq_getElem _ _ (by omega)]


end LeanForest.Security.H0
