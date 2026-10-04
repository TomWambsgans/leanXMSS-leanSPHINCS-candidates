import Mathlib

/-! Kernel-checkable rational certificate for the H-term bound: Stirling rows by a linear list
recursion, Touchard sums, the per-interval check and the interval chain, with the facts needed
to transfer a successful check to the reals. -/

namespace LeanSphincs.Security.H0

/-! ### Stirling rows -/

/-- `[k x_0, (k+1) x_1, …]`. -/
def mulIdx : ℕ → List ℕ → List ℕ
  | _, [] => []
  | k, x :: xs => k * x :: mulIdx (k + 1) xs

/-- Pointwise sum with zero padding. -/
def addLists : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addLists xs ys

/-- Next Stirling row: `S(n+1, j) = j S(n, j) + S(n, j-1)`. -/
def stirNext (row : List ℕ) : List ℕ := addLists (mulIdx 0 row) (0 :: row)

/-- The row `S(n, 0..n)` of Stirling numbers of the second kind. -/
def stirRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => stirNext (stirRow n)

theorem mulIdx_getD : ∀ (l : List ℕ) (k j : ℕ), (mulIdx k l).getD j 0 = (k + j) * l.getD j 0
  | [], k, j => by simp [mulIdx]
  | x :: xs, k, 0 => by simp [mulIdx]
  | x :: xs, k, j + 1 => by
      simp only [mulIdx, List.getD_cons_succ, mulIdx_getD xs (k + 1) j]
      ring_nf

theorem addLists_getD : ∀ (a b : List ℕ) (j : ℕ), (addLists a b).getD j 0 = a.getD j 0 + b.getD j 0
  | [], b, j => by simp [addLists]
  | x :: xs, [], j => by simp [addLists]
  | x :: xs, y :: ys, 0 => by simp [addLists]
  | x :: xs, y :: ys, j + 1 => by
      simp only [addLists, List.getD_cons_succ]
      exact addLists_getD xs ys j

theorem mulIdx_length : ∀ (l : List ℕ) (k : ℕ), (mulIdx k l).length = l.length
  | [], _ => rfl
  | x :: xs, k => by simp [mulIdx, mulIdx_length xs (k + 1)]

theorem addLists_length : ∀ (a b : List ℕ), (addLists a b).length = max a.length b.length
  | [], b => by simp [addLists]
  | x :: xs, [] => by simp [addLists]
  | x :: xs, y :: ys => by simp [addLists, addLists_length xs ys, Nat.succ_max_succ]

theorem stirRow_length : ∀ n, (stirRow n).length = n + 1
  | 0 => rfl
  | n + 1 => by
      simp only [stirRow, stirNext, addLists_length, mulIdx_length, List.length_cons, stirRow_length n]
      omega

theorem stirRow_getD : ∀ n j, (stirRow n).getD j 0 = Nat.stirlingSecond n j
  | 0, 0 => rfl
  | 0, j + 1 => by simp [stirRow]
  | n + 1, 0 => by
      simp only [stirRow, stirNext, addLists_getD, mulIdx_getD, List.getD_cons_zero]
      simp
  | n + 1, j + 1 => by
      simp only [stirRow, stirNext, addLists_getD, mulIdx_getD, List.getD_cons_succ, stirRow_getD n,
        Nat.stirlingSecond_succ_succ]
      ring

/-! ### Touchard sums -/

/-- `touchGo l μ p = p Σ_j l_j μ^j`. -/
def touchGo : List ℕ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | s :: l, μ, p => (s : ℚ) * p + touchGo l μ (p * μ)

theorem touchGo_eq : ∀ (l : List ℕ) (μ p : ℚ),
    touchGo l μ p = p * ∑ j ∈ Finset.range l.length, (l.getD j 0 : ℚ) * μ ^ j
  | [], _, _ => by simp [touchGo]
  | s :: l, μ, p => by
      rw [touchGo, touchGo_eq l μ (p * μ), List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => by ring
      · ring

/-- Touchard polynomial `T_n(μ) = Σ_j S(n,j) μ^j`, computed from the Stirling row. -/
def touchQ (n : ℕ) (μ : ℚ) : ℚ := touchGo (stirRow n) μ 1

theorem touchQ_eq (n : ℕ) (μ : ℚ) :
    touchQ n μ = ∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℚ) * μ ^ j := by
  rw [touchQ, touchGo_eq, one_mul, stirRow_length]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [stirRow_getD]

/-! ### The interval check -/

/-- Keygen credit `K`. -/
def kCredit (b : ℕ) : ℕ := 258 * 2 ^ b + 2 * (26 - b)

/-- Upper bound for the Poisson rate at the right end `qb` of an interval. -/
def muExactQ (b N qb R : ℕ) : ℚ :=
  ((N : ℚ) / 2 ^ b) * (1 + 2 ^ 26 / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) ^ (24 * R) *
    (1 + ((N : ℚ) * 2 ^ (26 - b) + qb) / ((2 : ℚ) ^ 128 - qb - 2 ^ 32))

/-- Lower bound for the baseline at the right end of an interval. -/
def betaQ (qb : ℕ) : ℚ := ((2 : ℚ) ^ 128 - 2 * qb) / (((2 : ℚ) ^ 128 - qb) * 2 ^ 127)

/-- Poisson mean of the per-leaf factor `(1 + 2^e 2^-266 k^24)^R`. -/
def PQ (R e : ℕ) (μ : ℚ) : ℚ :=
  ∑ s ∈ Finset.range (R + 1), (R.choose s : ℚ) * ((2 : ℚ) ^ e / 2 ^ 266) ^ s * touchQ (24 * s) μ

/-- `c_R = (R-1)^(R-1) / R^R`. -/
def cRQ (R : ℕ) : ℚ := ((R - 1 : ℕ) : ℚ) ^ (R - 1) / (R : ℚ) ^ R

/-- Prefactor `c_R / (t^R β^(R-1))`. -/
def AQ (R e : ℕ) (β : ℚ) : ℚ := cRQ R / (((2 : ℚ) ^ e) ^ R * β ^ (R - 1))

/-- A certificate entry: `(qa, qb, R, e, m)` with `t = 2^e` and rate bound `m / 2^64`. -/
abbrev Entry := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The main inequality of an entry, given the Poisson mean `P`. -/
def mainQ (b N qa qb R e : ℕ) (P : ℚ) : Prop :=
  (qb : ℚ) * AQ R e (betaQ qb) * (2 ^ b * (P - 1) / (1 - 2 ^ b * (P - 1))) +
      ((qb : ℚ) + kCredit b + N) / 2 ^ 200 ≤ ((qa : ℚ) / 2 ^ 128) ^ 2 + (kCredit b : ℚ) / 2 ^ 127

instance (b N qa qb R e : ℕ) (P : ℚ) : Decidable (mainQ b N qa qb R e P) := by
  unfold mainQ; infer_instance

/-- The check of one entry. -/
def checkI (b N : ℕ) (c : Entry) : Bool :=
  decide (1 ≤ c.2.2.1) && decide (2 * c.2.1 ≤ 2 ^ 128) &&
    decide (muExactQ b N c.2.1 c.2.2.1 ≤ (c.2.2.2.2 : ℚ) / 2 ^ 64) &&
    (decide (c.2.2.1 = 1) || decide (0 < betaQ c.2.1)) &&
    decide ((2 : ℚ) ^ b * (PQ c.2.2.1 c.2.2.2.1 ((c.2.2.2.2 : ℚ) / 2 ^ 64) - 1) < 1) &&
    decide (mainQ b N c.1 c.2.1 c.2.2.1 c.2.2.2.1 (PQ c.2.2.1 c.2.2.2.1 ((c.2.2.2.2 : ℚ) / 2 ^ 64)))

/-- Consecutive entries cover `[last, 2^127]`. -/
def chain (b N : ℕ) : ℕ → List Entry → Bool
  | last, [] => decide (2 ^ 127 < last)
  | last, c :: rest => decide (c.1 ≤ last) && checkI b N c && chain b N (c.2.1 + 1) rest

/-- A cover of every budget `0 ≤ q ≤ 2^127`. -/
def checkCover (b N : ℕ) (cover : List Entry) : Bool := chain b N 0 cover

theorem chain_sound (b N : ℕ) : ∀ (cover : List Entry) (last : ℕ), chain b N last cover = true →
    ∀ q, last ≤ q → q ≤ 2 ^ 127 → ∃ c ∈ cover, c.1 ≤ q ∧ q ≤ c.2.1 ∧ checkI b N c = true
  | [], last, h, q, hq, hq' => by
      simp only [chain, decide_eq_true_eq] at h
      omega
  | c :: rest, last, h, q, hq, hq' => by
      simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hc1, hc2⟩, hrest⟩ := h
      by_cases hle : q ≤ c.2.1
      · exact ⟨c, List.mem_cons_self .., by omega, hle, hc2⟩
      · obtain ⟨c', hc', h1, h2, h3⟩ := chain_sound b N rest _ hrest q (by omega) hq'
        exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2, h3⟩

theorem checkCover_sound (b N : ℕ) (cover : List Entry) (h : checkCover b N cover = true) (q : ℕ)
    (hq : q ≤ 2 ^ 127) : ∃ c ∈ cover, c.1 ≤ q ∧ q ≤ c.2.1 ∧ checkI b N c = true :=
  chain_sound b N cover 0 h q (Nat.zero_le _) hq

/-! ### Real-side facts -/

/-- Bernoulli: `(1+ε)^n - 1 ≤ nε / (1 - nε)` when `nε < 1`. -/
theorem pow_sub_one_le (ε : ℝ) (n : ℕ) (hε : 0 ≤ ε) (hn : n * ε < 1) :
    (1 + ε) ^ n - 1 ≤ n * ε / (1 - n * ε) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos'
  · subst h0; simp
  have hpos : 0 < 1 - n * ε := by linarith
  have hε1 : ε ≤ 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hpos'
    nlinarith
  have hb := one_add_mul_le_pow (a := -ε) (by linarith) n
  have hprod : (1 + ε) ^ n * (1 - n * ε) ≤ 1 := by
    calc (1 + ε) ^ n * (1 - n * ε) = (1 + ε) ^ n * (1 + n * (-ε)) := by ring
      _ ≤ (1 + ε) ^ n * (1 + -ε) ^ n := by gcongr
      _ = (1 - ε ^ 2) ^ n := by rw [← mul_pow]; ring_nf
      _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
  rw [le_div_iff₀ hpos]
  nlinarith

/-- The baseline at `q` is at least the rational lower bound at any `qb ≥ q`. -/
theorem betaQ_le (q qb : ℕ) (hq : q ≤ qb) (hqb : 2 * qb ≤ 2 ^ 128) :
    (betaQ qb : ℝ) ≤ (2 * ((2 : ℝ) ^ 128 - q) + 1) * ((2 : ℝ) ^ 128 - 2 * q) /
      ((2 : ℝ) ^ 128 * ((2 : ℝ) ^ 128 - q) ^ 2) := by
  unfold betaQ
  push_cast
  have hq' : (q : ℝ) ≤ qb := by exact_mod_cast hq
  have hqb' : 2 * (qb : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hqb
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hS1 : (0 : ℝ) < 2 ^ 128 - q := by linarith [show (0 : ℝ) < 2 ^ 128 by positivity]
  have hS2 : (0 : ℝ) < 2 ^ 128 - qb := by linarith [show (0 : ℝ) < 2 ^ 128 by positivity]
  have hS3 : (0 : ℝ) ≤ 2 ^ 128 - 2 * q := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ((2 : ℝ) ^ 128 - 2 * qb) * ((2 : ℝ) ^ 128 - q) ≤ ((2 : ℝ) ^ 128 - 2 * q) * ((2 : ℝ) ^ 128 - qb) := by
    nlinarith
  have h2 : (2 : ℝ) ^ 128 = 2 * 2 ^ 127 := by norm_num
  have h3 : 0 ≤ ((2 : ℝ) ^ 128 - 2 * q) * ((2 : ℝ) ^ 128 - q) := mul_nonneg hS3 hS1.le
  nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hS1), mul_nonneg h3 (le_of_lt hS2)]

end LeanSphincs.Security.H0
