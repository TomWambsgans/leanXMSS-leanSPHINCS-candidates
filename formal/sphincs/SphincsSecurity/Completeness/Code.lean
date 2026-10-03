import SphincsSecurity.Scheme

/-!
# How many digests the target-sum code accepts

The signer's counter search succeeds on a digest whose 42 three-bit digits sum to `T = 191` and
whose two padding bits are clear, so the search's failure probability is governed by how many of
the `2^128` digests that is. The count is the coefficient of `z^191` in `(1 + z + ... + z^7)^42`.

Counting it is one identity and one division. Packing the polynomial into a single natural number
in base `2^128`, which is above every coefficient, turns the product of the `42` factors into a
`Nat` power and the coefficient into one of its digits, so the kernel evaluates the whole count as
ordinary arithmetic on one large numeral.
-/

open Finset

set_option maxRecDepth 100000

namespace SphincsSecurity.Completeness

open TargetSum


/-- A base above every coefficient, so the coefficients are the digits. -/
def base : Nat := 2 ^ 128

theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)

theorem weight_pow (B : Nat) :
    (∑ d : Digit, B ^ d.val) ^ numChains = ∑ x : Encoding, B ^ (TargetSum.sum x) := by
  have hcard : (Finset.univ : Finset ChainIndex).card = numChains := by
    simp [Finset.card_univ]
  have h1 : (∑ d : Digit, B ^ d.val) ^ numChains
      = ∏ _i : ChainIndex, ∑ d : Digit, B ^ d.val := by
    rw [Finset.prod_const, hcard]
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl


/-- The number of codewords of digit sum `s`. -/
def codeCount (s : Nat) : Nat := (Finset.univ.filter (fun x : Encoding => TargetSum.sum x = s)).card

theorem sum_lt_295 (x : Encoding) : TargetSum.sum x < 295 := by
  have : TargetSum.sum x ≤ ∑ _i : ChainIndex, 7 :=
    Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x i).isLt)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  have hcard : Fintype.card ChainIndex = 42 := by simp [numChains]
  rw [hcard] at this
  omega

theorem sum_encoding_pow (B : Nat) :
    ∑ x : Encoding, B ^ (TargetSum.sum x) = ∑ s ∈ range 295, codeCount s * B ^ s := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := TargetSum.sum) (t := range 295)
    (fun x _ => Finset.mem_range.mpr (sum_lt_295 x)) (fun x => B ^ (TargetSum.sum x))]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, codeCount, smul_eq_mul]

theorem codeCount_lt_base (s : Nat) : codeCount s < base := by
  have h : codeCount s ≤ Fintype.card Encoding := Finset.card_filter_le _ _
  have hcard : Fintype.card Encoding = 8 ^ 42 := by
    simp [numChains, chainLength, winternitzBits]
  rw [hcard] at h
  exact Nat.lt_of_le_of_lt h (by decide)

theorem weight_eq : (∑ d : Digit, base ^ d.val) = (base ^ 8 - 1) / (base - 1) := by decide

theorem codeCount_target :
    codeCount targetSum = (∑ d : Digit, base ^ d.val) ^ numChains / base ^ targetSum % base := by
  rw [weight_pow, sum_encoding_pow]
  exact (digit_of_sum base (by decide) codeCount codeCount_lt_base 295 targetSum (by decide)).symm

theorem two_pow_le_codeCount : 2 ^ 114 ≤ codeCount targetSum := by
  rw [codeCount_target, weight_eq]
  decide


/-- A bounded-digit sum stays below the next power. -/
theorem sum_digits_lt (B : Nat) (hB : 0 < B) (v : Nat → Nat) (hv : ∀ j, v j < B) :
    ∀ n, ∑ j ∈ range n, v j * B ^ j < B ^ n := by
  intro n
  induction n with
  | zero => simpa using hB
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hle : v n * B ^ n ≤ (B - 1) * B ^ n :=
        Nat.mul_le_mul_right _ (by have := hv n; omega)
      have : B ^ n * B = (B - 1) * B ^ n + B ^ n := by
        cases B with
        | zero => omega
        | succ b => simp [Nat.succ_sub_one]; ring
      omega

def packHalf (v : Nat → Nat) : Nat := ∑ j ∈ range 21, v j * 8 ^ j

def lowDigit (x : Encoding) (j : Nat) : Nat :=
  if h : j < 21 then (x ⟨j, by simp only [numChains]; omega⟩).val else 0

def highDigit (x : Encoding) (j : Nat) : Nat :=
  if h : j < 21 then (x ⟨21 + j, by simp only [numChains]; omega⟩).val else 0

theorem lowDigit_lt (x : Encoding) (j : Nat) : lowDigit x j < 8 := by
  unfold lowDigit
  split
  · exact (x _).isLt
  · decide

theorem highDigit_lt (x : Encoding) (j : Nat) : highDigit x j < 8 := by
  unfold highDigit
  split
  · exact (x _).isLt
  · decide

theorem packHalf_lt (v : Nat → Nat) (hv : ∀ j, v j < 8) : packHalf v < 2 ^ 63 := by
  have h := sum_digits_lt 8 (by decide) v hv 21
  simpa [packHalf, show (8 : Nat) ^ 21 = 2 ^ 63 by norm_num] using h

theorem packHalf_digit (v : Nat → Nat) (hv : ∀ j, v j < 8) (k : Nat) (hk : k < 21) :
    packHalf v / 8 ^ k % 8 = v k :=
  digit_of_sum 8 (by decide) v hv 21 k hk

def packNat (x : Encoding) : Nat := packHalf (lowDigit x) + 2 ^ 64 * packHalf (highDigit x)

def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 128 := by
  have hlow := packHalf_lt _ (lowDigit_lt x)
  have hhigh := packHalf_lt _ (highDigit_lt x)
  have hmul : 2 ^ 64 * packHalf (highDigit x) ≤ 2 ^ 64 * 2 ^ 63 :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hhigh)
  have hpow : (2 : Nat) ^ 64 * 2 ^ 63 = 2 ^ 127 := by rw [← pow_add]
  have hbound : (2 : Nat) ^ 127 + 2 ^ 63 < 2 ^ 128 := by norm_num
  rw [hpow] at hmul
  unfold packNat
  omega

theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa [digestBits] using packNat_lt x)]

theorem encoding_val (d : Digest) (i : ChainIndex) :
    (digestEncoding d i).val = d.toNat / 2 ^ (digitOffset i) % 8 := by
  simp [digestEncoding, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow]

theorem low_field (A B k : Nat) (hk : k < 21) :
    (A + 2 ^ 64 * B) / 2 ^ (3 * k) % 8 = A / 2 ^ (3 * k) % 8 := by
  have hsplit : 2 ^ 64 * B = 2 ^ (3 * k) * (8 * (2 ^ (61 - 3 * k) * B)) := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.mul_assoc, ← Nat.mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (3 * k)), Nat.mul_comm 8,
    Nat.add_mul_mod_self_right]

theorem high_field (A B k : Nat) (hA : A < 2 ^ 64) :
    (A + 2 ^ 64 * B) / 2 ^ (64 + 3 * k) % 8 = B / 2 ^ (3 * k) % 8 := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ 64),
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hA, Nat.zero_add]

theorem digitOffset_low (i : ChainIndex) (h : i.val < 21) : digitOffset i = 3 * i.val := by
  simp [digitOffset, digitsPerHalf, numChains, winternitzBits, h]

theorem digitOffset_high (i : ChainIndex) (h : ¬ i.val < 21) :
    digitOffset i = 64 + 3 * (i.val - 21) := by
  have hi : i.val < 42 := by simpa [numChains] using i.isLt
  simp only [digitOffset, digitsPerHalf, numChains, winternitzBits,
    show ¬ i.val < 42 / 2 from by omega, if_false]
  omega

theorem packNat_lt_two_pow_127 (x : Encoding) : packNat x < 2 ^ 127 := by
  have hlow := packHalf_lt _ (lowDigit_lt x)
  have hhigh := packHalf_lt _ (highDigit_lt x)
  have hmul : 2 ^ 64 * packHalf (highDigit x) ≤ 2 ^ 64 * (2 ^ 63 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hpow : (2 : Nat) ^ 64 * (2 ^ 63 - 1) = 2 ^ 127 - 2 ^ 64 := by
    rw [Nat.mul_sub, ← pow_add]
    norm_num
  have hb : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  rw [hpow] at hmul
  have hle : (2 : Nat) ^ 64 ≤ 2 ^ 127 := by norm_num
  unfold packNat
  omega

theorem pack_padding_low (x : Encoding) : (pack x).getLsbD 63 = false := by
  have hlow := packHalf_lt _ (lowDigit_lt x)
  have hsplit : packNat x / 2 ^ 63 = 2 * packHalf (highDigit x) := by
    unfold packNat
    rw [show (2 : Nat) ^ 64 * packHalf (highDigit x) = 2 ^ 63 * (2 * packHalf (highDigit x)) by
      rw [← Nat.mul_assoc, show (2 : Nat) ^ 63 * 2 = 2 ^ 64 by norm_num]]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 63), Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hbit : (pack x).toNat.testBit 63 = false := by
    rw [toNat_pack, Nat.testBit_eq_decide_div_mod_eq, hsplit]
    simp [Nat.mul_mod_right]
  simpa [BitVec.getLsbD] using hbit

theorem pack_padding_high (x : Encoding) : (pack x).getLsbD 127 = false := by
  have hbit : (pack x).toNat.testBit 127 = false := by
    rw [toNat_pack]
    exact Nat.testBit_lt_two_pow (packNat_lt_two_pow_127 x)
  simpa [BitVec.getLsbD] using hbit

theorem digestEncoding_pack (x : Encoding) : digestEncoding (pack x) = x := by
  funext i
  apply Fin.ext
  rw [encoding_val, toNat_pack]
  have hi42 : i.val < 42 := by simpa [numChains] using i.isLt
  by_cases hi : i.val < 21
  · rw [digitOffset_low i hi]
    unfold packNat
    rw [low_field _ _ _ hi,
      show (2 : Nat) ^ (3 * i.val) = 8 ^ i.val by rw [pow_mul]; norm_num,
      packHalf_digit _ (lowDigit_lt x) i.val hi, lowDigit, dif_pos hi]
  · have hlow := packHalf_lt _ (lowDigit_lt x)
    have hstep : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
    rw [digitOffset_high i hi]
    unfold packNat
    rw [high_field _ _ _ (by omega),
      show (2 : Nat) ^ (3 * (i.val - 21)) = 8 ^ (i.val - 21) by rw [pow_mul]; norm_num,
      packHalf_digit _ (highDigit_lt x) (i.val - 21) (by omega),
      highDigit, dif_pos (show i.val - 21 < 21 by omega)]
    congr 1
    exact congrArg x (Fin.ext (show 21 + (i.val - 21) = i.val by omega))

theorem decodeDigest_pack (x : Encoding) (hx : Valid x) : decodeDigest (pack x) = some x := by
  rw [decodeDigest, if_pos ⟨pack_padding_low x, pack_padding_high x, by rw [digestEncoding_pack]; exact hx⟩,
    digestEncoding_pack]

/-- The signer's counter search accepts at least `2^114` of the `2^128` digests. -/
theorem two_pow_le_card_accepting :
    2 ^ 114 ≤ (Finset.univ.filter fun d : Digest => (decodeDigest d).isSome).card := by
  refine le_trans two_pow_le_codeCount ?_
  rw [codeCount]
  apply Finset.card_le_card_of_injOn pack
  · intro x hx
    have hvalid : Valid x := (Finset.mem_filter.mp hx).2
    simp [decodeDigest_pack x hvalid]
  · intro left hleft right hright heq
    have hl : Valid left := (Finset.mem_filter.mp hleft).2
    have hr : Valid right := (Finset.mem_filter.mp hright).2
    have := decodeDigest_pack left hl
    rw [heq, decodeDigest_pack right hr] at this
    exact (Option.some.inj this).symm

end SphincsSecurity.Completeness
