import LeanFors.Lifetimes

/-!
# leanSPHINCS: every security theorem

This file states every security theorem of the library: one theorem per height, shape and kept
subtree, 32 in all, then `requestedSecurity`, which collects them. The proofs live elsewhere
(`Lifetimes.lean`, from the certificates of `Certificates/`); here each one is a single reference,
so a statement below that is not exactly the one proved does not typecheck.

**What is proved.** `Secure127 P` (below) for the scheme with parameters `P`: in the SUF-CMA game
(`Statement.lean`), the adversary gets the public key, the hash (a random oracle) and a signing
oracle that it may ask for at most `N` signatures (the signature limit of `P`); it wins if it
outputs a message and a signature that verify, other than a pair the signing oracle answered. If
every run of the game makes at most `q ≥ 1` hash queries in total (the adversary's, and those of key
generation, signing and verification), it wins with probability at most `q / 2^127`.

**The parameters** (`Scheme.lean`). Every key has an index of `h` bits, `h ∈ {22, 24, 26, 28}`:
* `.pruned (h := h) (b := h) (N := N)`: the **full key**, one tree of height `h`, all built;
* `.pruned (h := h) (b := b) (N := N)`: a **pruned key**, the same tree, of which key generation
  builds only a subtree of height `b`; the signer grinds its randomizer until the index lands in it;
* `.layered (h := h) (d := 3) (ℓ := ℓ) (N := N)`: a **layered key**, three layers, the two lower
  ones of height `ℓ` and the top one of height `h - 2ℓ`.

**The hash** is not a parameter: the random oracle stands for Keccak-256, BLAKE2s and SHA-256
alike, so each theorem covers the three hashes. Sizes and verification costs, which depend on the
hash, are in `Configurations.lean`.
-/

namespace LeanFors

open Security ENNReal

/-- **The claim**, for the scheme with parameters `P`: every adversary whose runs of the SUF-CMA game
make at most `q ≥ 1` hash queries in total forges with probability at most `q / 2^127`. -/
def Secure127 (P : Params) : Prop :=
  letI := P
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : Adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ 127 : ℕ) : ℝ≥0∞)

/-! ## h = 22 (layered: 10 + 6 + 6) -/

/-- Full key: 81,860,000 signatures. -/
theorem h22_full : Secure127 (.pruned (h := 22) (b := 22) (N := 81_860_000)) := Lifetimes.h22_full_bits
/-- Pruned key, kept subtree of height 20: 21,760,000 signatures. -/
theorem h22_pruned20 : Secure127 (.pruned (h := 22) (b := 20) (N := 21_760_000)) := Lifetimes.h22_pruned20_bits
/-- Pruned key, kept subtree of height 14: 405,300 signatures. -/
theorem h22_pruned14 : Secure127 (.pruned (h := 22) (b := 14) (N := 405_300)) := Lifetimes.h22_pruned14_bits
/-- Pruned key, kept subtree of height 13: 208,500 signatures. -/
theorem h22_pruned13 : Secure127 (.pruned (h := 22) (b := 13) (N := 208_500)) := Lifetimes.h22_pruned13_bits
/-- Pruned key, kept subtree of height 12: 107,200 signatures. -/
theorem h22_pruned12 : Secure127 (.pruned (h := 22) (b := 12) (N := 107_200)) := Lifetimes.h22_pruned12_bits
/-- Pruned key, kept subtree of height 10: 28,410 signatures. -/
theorem h22_pruned10 : Secure127 (.pruned (h := 22) (b := 10) (N := 28_410)) := Lifetimes.h22_pruned10_bits
/-- Pruned key, kept subtree of height 8: 7,514 signatures. -/
theorem h22_pruned8 : Secure127 (.pruned (h := 22) (b := 8) (N := 7_514)) := Lifetimes.h22_pruned8_bits
/-- Layered key, 10 + 6 + 6: 81,860,000 signatures. -/
theorem h22_layered : Secure127 (.layered (h := 22) (d := 3) (ℓ := 6) (N := 81_860_000)) := Lifetimes.h22_layered_bits

/-! ## h = 24 (layered: 12 + 6 + 6) -/

/-- Full key: 336,700,000 signatures. -/
theorem h24_full : Secure127 (.pruned (h := 24) (b := 24) (N := 336_700_000)) := Lifetimes.h24_full_bits
/-- Pruned key, kept subtree of height 20: 23,830,000 signatures. -/
theorem h24_pruned20 : Secure127 (.pruned (h := 24) (b := 20) (N := 23_830_000)) := Lifetimes.h24_pruned20_bits
/-- Pruned key, kept subtree of height 14: 441,500 signatures. -/
theorem h24_pruned14 : Secure127 (.pruned (h := 24) (b := 14) (N := 441_500)) := Lifetimes.h24_pruned14_bits
/-- Pruned key, kept subtree of height 13: 226,800 signatures. -/
theorem h24_pruned13 : Secure127 (.pruned (h := 24) (b := 13) (N := 226_800)) := Lifetimes.h24_pruned13_bits
/-- Pruned key, kept subtree of height 12: 116,600 signatures. -/
theorem h24_pruned12 : Secure127 (.pruned (h := 24) (b := 12) (N := 116_600)) := Lifetimes.h24_pruned12_bits
/-- Pruned key, kept subtree of height 10: 30,810 signatures. -/
theorem h24_pruned10 : Secure127 (.pruned (h := 24) (b := 10) (N := 30_810)) := Lifetimes.h24_pruned10_bits
/-- Pruned key, kept subtree of height 8: 8,154 signatures. -/
theorem h24_pruned8 : Secure127 (.pruned (h := 24) (b := 8) (N := 8_154)) := Lifetimes.h24_pruned8_bits
/-- Layered key, 12 + 6 + 6: 336,700,000 signatures. -/
theorem h24_layered : Secure127 (.layered (h := 24) (d := 3) (ℓ := 6) (N := 336_700_000)) := Lifetimes.h24_layered_bits

/-! ## h = 26 (layered: 12 + 7 + 7) -/

/-- Full key: 1,381,000,000 signatures. -/
theorem h26_full : Secure127 (.pruned (h := 26) (b := 26) (N := 1_381_000_000)) := Lifetimes.h26_full_bits
/-- Pruned key, kept subtree of height 20: 26,030,000 signatures. -/
theorem h26_pruned20 : Secure127 (.pruned (h := 26) (b := 20) (N := 26_030_000)) := Lifetimes.h26_pruned20_bits
/-- Pruned key, kept subtree of height 14: 480,100 signatures. -/
theorem h26_pruned14 : Secure127 (.pruned (h := 26) (b := 14) (N := 480_100)) := Lifetimes.h26_pruned14_bits
/-- Pruned key, kept subtree of height 13: 246,900 signatures. -/
theorem h26_pruned13 : Secure127 (.pruned (h := 26) (b := 13) (N := 246_900)) := Lifetimes.h26_pruned13_bits
/-- Pruned key, kept subtree of height 12: 126,900 signatures. -/
theorem h26_pruned12 : Secure127 (.pruned (h := 26) (b := 12) (N := 126_900)) := Lifetimes.h26_pruned12_bits
/-- Pruned key, kept subtree of height 10: 33,480 signatures. -/
theorem h26_pruned10 : Secure127 (.pruned (h := 26) (b := 10) (N := 33_480)) := Lifetimes.h26_pruned10_bits
/-- Pruned key, kept subtree of height 8: 8,830 signatures. -/
theorem h26_pruned8 : Secure127 (.pruned (h := 26) (b := 8) (N := 8_830)) := Lifetimes.h26_pruned8_bits
/-- Layered key, 12 + 7 + 7: 1,381,000,000 signatures. -/
theorem h26_layered : Secure127 (.layered (h := 26) (d := 3) (ℓ := 7) (N := 1_381_000_000)) := Lifetimes.h26_layered_bits

/-! ## h = 28 (layered: 12 + 8 + 8) -/

/-- Full key: 5,634,000,000 signatures. -/
theorem h28_full : Secure127 (.pruned (h := 28) (b := 28) (N := 5_634_000_000)) := Lifetimes.h28_full_bits
/-- Pruned key, kept subtree of height 20: 28,350,000 signatures. -/
theorem h28_pruned20 : Secure127 (.pruned (h := 28) (b := 20) (N := 28_350_000)) := Lifetimes.h28_pruned20_bits
/-- Pruned key, kept subtree of height 14: 522,000 signatures. -/
theorem h28_pruned14 : Secure127 (.pruned (h := 28) (b := 14) (N := 522_000)) := Lifetimes.h28_pruned14_bits
/-- Pruned key, kept subtree of height 13: 267,900 signatures. -/
theorem h28_pruned13 : Secure127 (.pruned (h := 28) (b := 13) (N := 267_900)) := Lifetimes.h28_pruned13_bits
/-- Pruned key, kept subtree of height 12: 137,400 signatures. -/
theorem h28_pruned12 : Secure127 (.pruned (h := 28) (b := 12) (N := 137_400)) := Lifetimes.h28_pruned12_bits
/-- Pruned key, kept subtree of height 10: 36,190 signatures. -/
theorem h28_pruned10 : Secure127 (.pruned (h := 28) (b := 10) (N := 36_190)) := Lifetimes.h28_pruned10_bits
/-- Pruned key, kept subtree of height 8: 9,541 signatures. -/
theorem h28_pruned8 : Secure127 (.pruned (h := 28) (b := 8) (N := 9_541)) := Lifetimes.h28_pruned8_bits
/-- Layered key, 12 + 8 + 8: 5,634,000,000 signatures. -/
theorem h28_layered : Secure127 (.layered (h := 28) (d := 3) (ℓ := 8) (N := 5_634_000_000)) := Lifetimes.h28_layered_bits

/-! ## All together -/

/-- The 32 configurations above. -/
def configurations : List Params := [
  .pruned 22 22 81_860_000, .pruned 22 20 21_760_000, .pruned 22 14 405_300, .pruned 22 13 208_500,
  .pruned 22 12 107_200, .pruned 22 10 28_410, .pruned 22 8 7_514, .layered 22 3 6 81_860_000,
  .pruned 24 24 336_700_000, .pruned 24 20 23_830_000, .pruned 24 14 441_500, .pruned 24 13 226_800,
  .pruned 24 12 116_600, .pruned 24 10 30_810, .pruned 24 8 8_154, .layered 24 3 6 336_700_000,
  .pruned 26 26 1_381_000_000, .pruned 26 20 26_030_000, .pruned 26 14 480_100, .pruned 26 13 246_900,
  .pruned 26 12 126_900, .pruned 26 10 33_480, .pruned 26 8 8_830, .layered 26 3 7 1_381_000_000,
  .pruned 28 28 5_634_000_000, .pruned 28 20 28_350_000, .pruned 28 14 522_000, .pruned 28 13 267_900,
  .pruned 28 12 137_400, .pruned 28 10 36_190, .pruned 28 8 9_541, .layered 28 3 8 5_634_000_000]

/-- **Main theorem**: every configuration has 127 bits of SUF-CMA security. -/
theorem requestedSecurity : ∀ P ∈ configurations, Secure127 P := by
  simp only [configurations, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨h22_full, h22_pruned20, h22_pruned14, h22_pruned13, h22_pruned12, h22_pruned10, h22_pruned8,
    h22_layered, h24_full, h24_pruned20, h24_pruned14, h24_pruned13, h24_pruned12, h24_pruned10,
    h24_pruned8, h24_layered, h26_full, h26_pruned20, h26_pruned14, h26_pruned13, h26_pruned12,
    h26_pruned10, h26_pruned8, h26_layered, h28_full, h28_pruned20, h28_pruned14, h28_pruned13,
    h28_pruned12, h28_pruned10, h28_pruned8, h28_layered⟩

/-- `Secure127` is the target `SecurityBits P 127` of `Statement.lean`, spelled out. -/
theorem secure127_iff (P : Params) : Secure127 P ↔ SecurityBits P 127 := Iff.rfl

end LeanFors
