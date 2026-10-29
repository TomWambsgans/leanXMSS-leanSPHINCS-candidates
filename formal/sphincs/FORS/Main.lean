import FORS.Lifetimes

/-!
# leanSPHINCS, FORS variant: every security theorem

This file states every security theorem of the library: one theorem per configuration (height,
shape, kept subtree and FORS), 39 in all, then `requestedSecurity`, which collects them. The proofs live elsewhere
(`Lifetimes.lean`, from the certificates of `Certificates/`); here each one is a single reference,
so a statement below that is not exactly the one proved does not typecheck.

**What is proved.** `Secure127 P` (below) for the scheme with parameters `P`: in the SUF-CMA game
(`Statement.lean`), the adversary gets the public key, the hash (a random oracle) and a signing
oracle that it may ask for at most `N` signatures (the signature limit of `P`); it wins if it
outputs a message and a signature that verify, other than a pair the signing oracle answered. If
every run of the game makes at most `q ≥ 1` hash queries in total (the adversary's, and those of key
generation, signing and verification), it wins with probability at most `q / 2^127`.

**The parameters** (`Scheme.lean`). Every key has an index of `h` bits, `h ∈ {20, 22, 24, 26, 28}`,
and a few-time signature of `k` FORS trees of height `a`: `k = 24` and `a = 10`, the same for every
pruning of a height so that verification does not depend on it, except the layered keys of the
lifetimes `2^24` and `2^26`, both at `h = 24`, with 19 and 23 trees of height 9 (`scripts/scheme.py`).
Layered keys are at `h ∈ {24, 26, 28}`:
* `.pruned (h := h) (b := h) (k := k) (a := a) (N := N)`: the **full key**, one tree of height `h`,
  all built;
* `.pruned (h := h) (b := b) (k := k) (a := a) (N := N)`: a **pruned key**, the same tree, of which
  key generation builds only a subtree of height `b`; the signer grinds its randomizer until the
  index lands in it;
* `.layered (h := h) (d := 3) (ℓ := ℓ) (k := k) (a := a) (N := N)`: a **layered key**, three layers,
  the two lower ones of height `ℓ` and the top one of height `h - 2ℓ`.

**The hash** is not a parameter: the random oracle stands for Keccak-256, BLAKE2s and SHA-256
alike, so each theorem covers the three hashes. Sizes and verification costs, which depend on the
hash, are in `Configurations.lean`.
-/

namespace FORS

open Security ENNReal

/-- **The claim**, for the scheme with parameters `P`: every adversary whose runs of the SUF-CMA game
make at most `q ≥ 1` hash queries in total forges with probability at most `q / 2^127`. -/
def Secure127 (P : Params) : Prop :=
  letI := P
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : Adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ 127 : ℕ) : ℝ≥0∞)

/-! ## h = 20 -/

/-- Full key: 17,650,000 signatures. -/
theorem h20_full : Secure127 (.pruned (h := 20) (b := 20) (k := 24) (a := 10) (N := 17_650_000)) :=
  Lifetimes.h20_full_bits
/-- Pruned key, kept subtree of height 14: 327,400 signatures. -/
theorem h20_pruned14 : Secure127 (.pruned (h := 20) (b := 14) (k := 24) (a := 10) (N := 327_400)) :=
  Lifetimes.h20_pruned14_bits
/-- Pruned key, kept subtree of height 13: 168,300 signatures. -/
theorem h20_pruned13 : Secure127 (.pruned (h := 20) (b := 13) (k := 24) (a := 10) (N := 168_300)) :=
  Lifetimes.h20_pruned13_bits
/-- Pruned key, kept subtree of height 12: 86,430 signatures. -/
theorem h20_pruned12 : Secure127 (.pruned (h := 20) (b := 12) (k := 24) (a := 10) (N := 86_430)) :=
  Lifetimes.h20_pruned12_bits
/-- Pruned key, kept subtree of height 10: 22,850 signatures. -/
theorem h20_pruned10 : Secure127 (.pruned (h := 20) (b := 10) (k := 24) (a := 10) (N := 22_850)) :=
  Lifetimes.h20_pruned10_bits
/-- Pruned key, kept subtree of height 8: 6,036 signatures. -/
theorem h20_pruned8 : Secure127 (.pruned (h := 20) (b := 8) (k := 24) (a := 10) (N := 6_036)) :=
  Lifetimes.h20_pruned8_bits

/-! ## h = 22 -/

/-- Full key: 72,220,000 signatures. -/
theorem h22_full : Secure127 (.pruned (h := 22) (b := 22) (k := 24) (a := 10) (N := 72_220_000)) :=
  Lifetimes.h22_full_bits
/-- Pruned key, kept subtree of height 20: 19,240,000 signatures. -/
theorem h22_pruned20 : Secure127 (.pruned (h := 22) (b := 20) (k := 24) (a := 10) (N := 19_240_000)) :=
  Lifetimes.h22_pruned20_bits
/-- Pruned key, kept subtree of height 14: 356,000 signatures. -/
theorem h22_pruned14 : Secure127 (.pruned (h := 22) (b := 14) (k := 24) (a := 10) (N := 356_000)) :=
  Lifetimes.h22_pruned14_bits
/-- Pruned key, kept subtree of height 13: 182,800 signatures. -/
theorem h22_pruned13 : Secure127 (.pruned (h := 22) (b := 13) (k := 24) (a := 10) (N := 182_800)) :=
  Lifetimes.h22_pruned13_bits
/-- Pruned key, kept subtree of height 12: 93,890 signatures. -/
theorem h22_pruned12 : Secure127 (.pruned (h := 22) (b := 12) (k := 24) (a := 10) (N := 93_890)) :=
  Lifetimes.h22_pruned12_bits
/-- Pruned key, kept subtree of height 10: 24,790 signatures. -/
theorem h22_pruned10 : Secure127 (.pruned (h := 22) (b := 10) (k := 24) (a := 10) (N := 24_790)) :=
  Lifetimes.h22_pruned10_bits
/-- Pruned key, kept subtree of height 8: 6,547 signatures. -/
theorem h22_pruned8 : Secure127 (.pruned (h := 22) (b := 8) (k := 24) (a := 10) (N := 6_547)) :=
  Lifetimes.h22_pruned8_bits

/-! ## h = 24 (layered: 10 + 7 + 7) -/

/-- Full key: 293,000,000 signatures. -/
theorem h24_full : Secure127 (.pruned (h := 24) (b := 24) (k := 24) (a := 10) (N := 293_000_000)) :=
  Lifetimes.h24_full_bits
/-- Pruned key, kept subtree of height 20: 20,920,000 signatures. -/
theorem h24_pruned20 : Secure127 (.pruned (h := 24) (b := 20) (k := 24) (a := 10) (N := 20_920_000)) :=
  Lifetimes.h24_pruned20_bits
/-- Pruned key, kept subtree of height 14: 387,200 signatures. -/
theorem h24_pruned14 : Secure127 (.pruned (h := 24) (b := 14) (k := 24) (a := 10) (N := 387_200)) :=
  Lifetimes.h24_pruned14_bits
/-- Pruned key, kept subtree of height 13: 198,700 signatures. -/
theorem h24_pruned13 : Secure127 (.pruned (h := 24) (b := 13) (k := 24) (a := 10) (N := 198_700)) :=
  Lifetimes.h24_pruned13_bits
/-- Pruned key, kept subtree of height 12: 101,900 signatures. -/
theorem h24_pruned12 : Secure127 (.pruned (h := 24) (b := 12) (k := 24) (a := 10) (N := 101_900)) :=
  Lifetimes.h24_pruned12_bits
/-- Pruned key, kept subtree of height 10: 26,860 signatures. -/
theorem h24_pruned10 : Secure127 (.pruned (h := 24) (b := 10) (k := 24) (a := 10) (N := 26_860)) :=
  Lifetimes.h24_pruned10_bits
/-- Pruned key, kept subtree of height 8: 7,099 signatures. -/
theorem h24_pruned8 : Secure127 (.pruned (h := 24) (b := 8) (k := 24) (a := 10) (N := 7_099)) :=
  Lifetimes.h24_pruned8_bits
/-- Layered key, 10 + 7 + 7: 293,000,000 signatures. -/
theorem h24_layered : Secure127 (.layered (h := 24) (d := 3) (ℓ := 7) (k := 24) (a := 10) (N := 293_000_000)) :=
  Lifetimes.h24_layered_bits
/-- Layered key, 10 + 7 + 7, 23 FORS trees of height 9 (the lifetime `2^26`): 73,380,000 signatures. -/
theorem h24_layered_k23 : Secure127 (.layered (h := 24) (d := 3) (ℓ := 7) (k := 23) (a := 9) (N := 73_380_000)) :=
  Lifetimes.h24_layered_k23_bits
/-- Layered key, 10 + 7 + 7, 19 FORS trees of height 9 (the lifetime `2^24`): 16,777,216 signatures. -/
theorem h24_layered_k19 : Secure127 (.layered (h := 24) (d := 3) (ℓ := 7) (k := 19) (a := 9) (N := 16_777_216)) :=
  Lifetimes.h24_layered_k19_bits

/-! ## h = 26 (layered: 10 + 8 + 8) -/

/-- Full key: 1,182,000,000 signatures. -/
theorem h26_full : Secure127 (.pruned (h := 26) (b := 26) (k := 24) (a := 10) (N := 1_182_000_000)) :=
  Lifetimes.h26_full_bits
/-- Pruned key, kept subtree of height 20: 22,750,000 signatures. -/
theorem h26_pruned20 : Secure127 (.pruned (h := 26) (b := 20) (k := 24) (a := 10) (N := 22_750_000)) :=
  Lifetimes.h26_pruned20_bits
/-- Pruned key, kept subtree of height 14: 419,700 signatures. -/
theorem h26_pruned14 : Secure127 (.pruned (h := 26) (b := 14) (k := 24) (a := 10) (N := 419_700)) :=
  Lifetimes.h26_pruned14_bits
/-- Pruned key, kept subtree of height 13: 215,400 signatures. -/
theorem h26_pruned13 : Secure127 (.pruned (h := 26) (b := 13) (k := 24) (a := 10) (N := 215_400)) :=
  Lifetimes.h26_pruned13_bits
/-- Pruned key, kept subtree of height 12: 110,500 signatures. -/
theorem h26_pruned12 : Secure127 (.pruned (h := 26) (b := 12) (k := 24) (a := 10) (N := 110_500)) :=
  Lifetimes.h26_pruned12_bits
/-- Pruned key, kept subtree of height 10: 29,130 signatures. -/
theorem h26_pruned10 : Secure127 (.pruned (h := 26) (b := 10) (k := 24) (a := 10) (N := 29_130)) :=
  Lifetimes.h26_pruned10_bits
/-- Pruned key, kept subtree of height 8: 7,677 signatures. -/
theorem h26_pruned8 : Secure127 (.pruned (h := 26) (b := 8) (k := 24) (a := 10) (N := 7_677)) :=
  Lifetimes.h26_pruned8_bits
/-- Layered key, 10 + 8 + 8: 1,182,000,000 signatures. -/
theorem h26_layered : Secure127 (.layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10) (N := 1_182_000_000)) :=
  Lifetimes.h26_layered_bits

/-! ## h = 28 (layered: 10 + 9 + 9) -/

/-- Full key: 4,731,000,000 signatures. -/
theorem h28_full : Secure127 (.pruned (h := 28) (b := 28) (k := 24) (a := 10) (N := 4_731_000_000)) :=
  Lifetimes.h28_full_bits
/-- Pruned key, kept subtree of height 20: 24,710,000 signatures. -/
theorem h28_pruned20 : Secure127 (.pruned (h := 28) (b := 20) (k := 24) (a := 10) (N := 24_710_000)) :=
  Lifetimes.h28_pruned20_bits
/-- Pruned key, kept subtree of height 14: 455,600 signatures. -/
theorem h28_pruned14 : Secure127 (.pruned (h := 28) (b := 14) (k := 24) (a := 10) (N := 455_600)) :=
  Lifetimes.h28_pruned14_bits
/-- Pruned key, kept subtree of height 13: 233,500 signatures. -/
theorem h28_pruned13 : Secure127 (.pruned (h := 28) (b := 13) (k := 24) (a := 10) (N := 233_500)) :=
  Lifetimes.h28_pruned13_bits
/-- Pruned key, kept subtree of height 12: 119,800 signatures. -/
theorem h28_pruned12 : Secure127 (.pruned (h := 28) (b := 12) (k := 24) (a := 10) (N := 119_800)) :=
  Lifetimes.h28_pruned12_bits
/-- Pruned key, kept subtree of height 10: 31,600 signatures. -/
theorem h28_pruned10 : Secure127 (.pruned (h := 28) (b := 10) (k := 24) (a := 10) (N := 31_600)) :=
  Lifetimes.h28_pruned10_bits
/-- Pruned key, kept subtree of height 8: 8,313 signatures. -/
theorem h28_pruned8 : Secure127 (.pruned (h := 28) (b := 8) (k := 24) (a := 10) (N := 8_313)) :=
  Lifetimes.h28_pruned8_bits
/-- Layered key, 10 + 9 + 9: 4,731,000,000 signatures. -/
theorem h28_layered : Secure127 (.layered (h := 28) (d := 3) (ℓ := 9) (k := 24) (a := 10) (N := 4_731_000_000)) :=
  Lifetimes.h28_layered_bits

/-! ## All together -/

/-- The 39 configurations above. -/
def configurations : List Params := [
  .pruned 20 20 24 10 17_650_000, .pruned 20 14 24 10 327_400, .pruned 20 13 24 10 168_300,
  .pruned 20 12 24 10 86_430, .pruned 20 10 24 10 22_850, .pruned 20 8 24 10 6_036,
  .pruned 22 22 24 10 72_220_000, .pruned 22 20 24 10 19_240_000,
  .pruned 22 14 24 10 356_000, .pruned 22 13 24 10 182_800, .pruned 22 12 24 10 93_890,
  .pruned 22 10 24 10 24_790, .pruned 22 8 24 10 6_547,
  .pruned 24 24 24 10 293_000_000, .pruned 24 20 24 10 20_920_000, .pruned 24 14 24 10 387_200,
  .pruned 24 13 24 10 198_700, .pruned 24 12 24 10 101_900, .pruned 24 10 24 10 26_860,
  .pruned 24 8 24 10 7_099, .layered 24 3 7 24 10 293_000_000, .layered 24 3 7 23 9 73_380_000,
  .layered 24 3 7 19 9 16_777_216, .pruned 26 26 24 10 1_182_000_000,
  .pruned 26 20 24 10 22_750_000, .pruned 26 14 24 10 419_700, .pruned 26 13 24 10 215_400,
  .pruned 26 12 24 10 110_500, .pruned 26 10 24 10 29_130, .pruned 26 8 24 10 7_677,
  .layered 26 3 8 24 10 1_182_000_000, .pruned 28 28 24 10 4_731_000_000,
  .pruned 28 20 24 10 24_710_000, .pruned 28 14 24 10 455_600, .pruned 28 13 24 10 233_500,
  .pruned 28 12 24 10 119_800, .pruned 28 10 24 10 31_600, .pruned 28 8 24 10 8_313,
  .layered 28 3 9 24 10 4_731_000_000]

/-- **Main theorem**: every configuration has 127 bits of SUF-CMA security. -/
theorem requestedSecurity : ∀ P ∈ configurations, Secure127 P := by
  simp only [configurations, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨h20_full, h20_pruned14, h20_pruned13, h20_pruned12, h20_pruned10, h20_pruned8,
    h22_full, h22_pruned20, h22_pruned14, h22_pruned13, h22_pruned12, h22_pruned10, h22_pruned8,
    h24_full, h24_pruned20, h24_pruned14, h24_pruned13, h24_pruned12, h24_pruned10,
    h24_pruned8, h24_layered, h24_layered_k23, h24_layered_k19, h26_full, h26_pruned20, h26_pruned14, h26_pruned13, h26_pruned12,
    h26_pruned10, h26_pruned8, h26_layered, h28_full, h28_pruned20, h28_pruned14, h28_pruned13,
    h28_pruned12, h28_pruned10, h28_pruned8, h28_layered⟩

/-- `Secure127` is the target `SecurityBits P 127` of `Statement.lean`, spelled out. -/
theorem secure127_iff (P : Params) : Secure127 P ↔ SecurityBits P 127 := Iff.rfl

end FORS
