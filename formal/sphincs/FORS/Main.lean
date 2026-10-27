import FORS.Lifetimes

/-!
# leanSPHINCS, FORS variant: every security theorem

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

**The parameters** (`Scheme.lean`). Every key has an index of `h` bits, `h ∈ {22, 24, 26, 28}`,
and a few-time signature of `k` FORS trees of height `a` (`a = 10` and `k = 25` throughout, so that
verification is the same for every pruning; `scripts/scheme.py`):
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

/-! ## h = 22 (layered: 10 + 6 + 6) -/

/-- Full key: 86,910,000 signatures. -/
theorem h22_full : Secure127 (.pruned (h := 22) (b := 22) (k := 25) (a := 10) (N := 86_910_000)) :=
  Lifetimes.h22_full_bits
/-- Pruned key, kept subtree of height 20: 23,050,000 signatures. -/
theorem h22_pruned20 : Secure127 (.pruned (h := 22) (b := 20) (k := 25) (a := 10) (N := 23_050_000)) :=
  Lifetimes.h22_pruned20_bits
/-- Pruned key, kept subtree of height 14: 424,100 signatures. -/
theorem h22_pruned14 : Secure127 (.pruned (h := 22) (b := 14) (k := 25) (a := 10) (N := 424_100)) :=
  Lifetimes.h22_pruned14_bits
/-- Pruned key, kept subtree of height 13: 217,700 signatures. -/
theorem h22_pruned13 : Secure127 (.pruned (h := 22) (b := 13) (k := 25) (a := 10) (N := 217_700)) :=
  Lifetimes.h22_pruned13_bits
/-- Pruned key, kept subtree of height 12: 111,800 signatures. -/
theorem h22_pruned12 : Secure127 (.pruned (h := 22) (b := 12) (k := 25) (a := 10) (N := 111_800)) :=
  Lifetimes.h22_pruned12_bits
/-- Pruned key, kept subtree of height 10: 29,440 signatures. -/
theorem h22_pruned10 : Secure127 (.pruned (h := 22) (b := 10) (k := 25) (a := 10) (N := 29_440)) :=
  Lifetimes.h22_pruned10_bits
/-- Pruned key, kept subtree of height 8: 7,759 signatures. -/
theorem h22_pruned8 : Secure127 (.pruned (h := 22) (b := 8) (k := 25) (a := 10) (N := 7_759)) :=
  Lifetimes.h22_pruned8_bits
/-- Layered key, 10 + 6 + 6: 86,910,000 signatures. -/
theorem h22_layered : Secure127 (.layered (h := 22) (d := 3) (ℓ := 6) (k := 25) (a := 10) (N := 86_910_000)) :=
  Lifetimes.h22_layered_bits

/-! ## h = 24 (layered: 10 + 7 + 7) -/

/-- Full key: 354,200,000 signatures. -/
theorem h24_full : Secure127 (.pruned (h := 24) (b := 24) (k := 25) (a := 10) (N := 354_200_000)) :=
  Lifetimes.h24_full_bits
/-- Pruned key, kept subtree of height 20: 24,970,000 signatures. -/
theorem h24_pruned20 : Secure127 (.pruned (h := 24) (b := 20) (k := 25) (a := 10) (N := 24_970_000)) :=
  Lifetimes.h24_pruned20_bits
/-- Pruned key, kept subtree of height 14: 459,500 signatures. -/
theorem h24_pruned14 : Secure127 (.pruned (h := 24) (b := 14) (k := 25) (a := 10) (N := 459_500)) :=
  Lifetimes.h24_pruned14_bits
/-- Pruned key, kept subtree of height 13: 235,700 signatures. -/
theorem h24_pruned13 : Secure127 (.pruned (h := 24) (b := 13) (k := 25) (a := 10) (N := 235_700)) :=
  Lifetimes.h24_pruned13_bits
/-- Pruned key, kept subtree of height 12: 120,900 signatures. -/
theorem h24_pruned12 : Secure127 (.pruned (h := 24) (b := 12) (k := 25) (a := 10) (N := 120_900)) :=
  Lifetimes.h24_pruned12_bits
/-- Pruned key, kept subtree of height 10: 31,760 signatures. -/
theorem h24_pruned10 : Secure127 (.pruned (h := 24) (b := 10) (k := 25) (a := 10) (N := 31_760)) :=
  Lifetimes.h24_pruned10_bits
/-- Pruned key, kept subtree of height 8: 8,359 signatures. -/
theorem h24_pruned8 : Secure127 (.pruned (h := 24) (b := 8) (k := 25) (a := 10) (N := 8_359)) :=
  Lifetimes.h24_pruned8_bits
/-- Layered key, 10 + 7 + 7: 354,200,000 signatures. -/
theorem h24_layered : Secure127 (.layered (h := 24) (d := 3) (ℓ := 7) (k := 25) (a := 10) (N := 354_200_000)) :=
  Lifetimes.h24_layered_bits

/-! ## h = 26 (layered: 10 + 8 + 8) -/

/-- Full key: 1,426,000,000 signatures. -/
theorem h26_full : Secure127 (.pruned (h := 26) (b := 26) (k := 25) (a := 10) (N := 1_426_000_000)) :=
  Lifetimes.h26_full_bits
/-- Pruned key, kept subtree of height 20: 27,030,000 signatures. -/
theorem h26_pruned20 : Secure127 (.pruned (h := 26) (b := 20) (k := 25) (a := 10) (N := 27_030_000)) :=
  Lifetimes.h26_pruned20_bits
/-- Pruned key, kept subtree of height 14: 496,100 signatures. -/
theorem h26_pruned14 : Secure127 (.pruned (h := 26) (b := 14) (k := 25) (a := 10) (N := 496_100)) :=
  Lifetimes.h26_pruned14_bits
/-- Pruned key, kept subtree of height 13: 254,400 signatures. -/
theorem h26_pruned13 : Secure127 (.pruned (h := 26) (b := 13) (k := 25) (a := 10) (N := 254_400)) :=
  Lifetimes.h26_pruned13_bits
/-- Pruned key, kept subtree of height 12: 130,500 signatures. -/
theorem h26_pruned12 : Secure127 (.pruned (h := 26) (b := 12) (k := 25) (a := 10) (N := 130_500)) :=
  Lifetimes.h26_pruned12_bits
/-- Pruned key, kept subtree of height 10: 34,330 signatures. -/
theorem h26_pruned10 : Secure127 (.pruned (h := 26) (b := 10) (k := 25) (a := 10) (N := 34_330)) :=
  Lifetimes.h26_pruned10_bits
/-- Pruned key, kept subtree of height 8: 9,019 signatures. -/
theorem h26_pruned8 : Secure127 (.pruned (h := 26) (b := 8) (k := 25) (a := 10) (N := 9_019)) :=
  Lifetimes.h26_pruned8_bits
/-- Layered key, 10 + 8 + 8: 1,426,000,000 signatures. -/
theorem h26_layered : Secure127 (.layered (h := 26) (d := 3) (ℓ := 8) (k := 25) (a := 10) (N := 1_426_000_000)) :=
  Lifetimes.h26_layered_bits

/-! ## h = 28 (layered: 10 + 9 + 9) -/

/-- Full key: 5,707,000,000 signatures. -/
theorem h28_full : Secure127 (.pruned (h := 28) (b := 28) (k := 25) (a := 10) (N := 5_707_000_000)) :=
  Lifetimes.h28_full_bits
/-- Pruned key, kept subtree of height 20: 29,240,000 signatures. -/
theorem h28_pruned20 : Secure127 (.pruned (h := 28) (b := 20) (k := 25) (a := 10) (N := 29_240_000)) :=
  Lifetimes.h28_pruned20_bits
/-- Pruned key, kept subtree of height 14: 536,400 signatures. -/
theorem h28_pruned14 : Secure127 (.pruned (h := 28) (b := 14) (k := 25) (a := 10) (N := 536_400)) :=
  Lifetimes.h28_pruned14_bits
/-- Pruned key, kept subtree of height 13: 275,000 signatures. -/
theorem h28_pruned13 : Secure127 (.pruned (h := 28) (b := 13) (k := 25) (a := 10) (N := 275_000)) :=
  Lifetimes.h28_pruned13_bits
/-- Pruned key, kept subtree of height 12: 140,900 signatures. -/
theorem h28_pruned12 : Secure127 (.pruned (h := 28) (b := 12) (k := 25) (a := 10) (N := 140_900)) :=
  Lifetimes.h28_pruned12_bits
/-- Pruned key, kept subtree of height 10: 37,030 signatures. -/
theorem h28_pruned10 : Secure127 (.pruned (h := 28) (b := 10) (k := 25) (a := 10) (N := 37_030)) :=
  Lifetimes.h28_pruned10_bits
/-- Pruned key, kept subtree of height 8: 9,721 signatures. -/
theorem h28_pruned8 : Secure127 (.pruned (h := 28) (b := 8) (k := 25) (a := 10) (N := 9_721)) :=
  Lifetimes.h28_pruned8_bits
/-- Layered key, 10 + 9 + 9: 5,707,000,000 signatures. -/
theorem h28_layered : Secure127 (.layered (h := 28) (d := 3) (ℓ := 9) (k := 25) (a := 10) (N := 5_707_000_000)) :=
  Lifetimes.h28_layered_bits

/-! ## All together -/

/-- The 32 configurations above. -/
def configurations : List Params := [
  .pruned 22 22 25 10 86_910_000, .pruned 22 20 25 10 23_050_000, .pruned 22 14 25 10 424_100,
  .pruned 22 13 25 10 217_700, .pruned 22 12 25 10 111_800, .pruned 22 10 25 10 29_440,
  .pruned 22 8 25 10 7_759, .layered 22 3 6 25 10 86_910_000, .pruned 24 24 25 10 354_200_000,
  .pruned 24 20 25 10 24_970_000, .pruned 24 14 25 10 459_500, .pruned 24 13 25 10 235_700,
  .pruned 24 12 25 10 120_900, .pruned 24 10 25 10 31_760, .pruned 24 8 25 10 8_359,
  .layered 24 3 7 25 10 354_200_000, .pruned 26 26 25 10 1_426_000_000, .pruned 26 20 25 10 27_030_000,
  .pruned 26 14 25 10 496_100, .pruned 26 13 25 10 254_400, .pruned 26 12 25 10 130_500,
  .pruned 26 10 25 10 34_330, .pruned 26 8 25 10 9_019, .layered 26 3 8 25 10 1_426_000_000,
  .pruned 28 28 25 10 5_707_000_000, .pruned 28 20 25 10 29_240_000, .pruned 28 14 25 10 536_400,
  .pruned 28 13 25 10 275_000, .pruned 28 12 25 10 140_900, .pruned 28 10 25 10 37_030,
  .pruned 28 8 25 10 9_721, .layered 28 3 9 25 10 5_707_000_000]

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

end FORS
