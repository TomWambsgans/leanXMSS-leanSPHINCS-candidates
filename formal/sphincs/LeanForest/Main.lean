import LeanForest.Lifetimes

/-!
# leanSPHINCS: the main theorem

An auditor reads three files: `Scheme.lean` (the scheme, its parameters `Params` and the
constructors `Params.pruned` and `Params.layered`), `Statement.lean` (the SUF-CMA game and the
target `SecurityBits`) and this one: the 32 proved configurations and the main theorem.

A configuration does not depend on the hash: the random oracle stands for Keccak-256, BLAKE2s and
SHA-256 alike, and only the sizes and verification costs depend on it (`Configurations.lean`). Per
height `h ∈ {22, 24, 26, 28}` there are the full key `Params.pruned h h N`, six pruned keys
`Params.pruned h b N` that keep a subtree of height `b ∈ {20, 14, 13, 12, 10, 8}`, and the layered
key `Params.layered h 3 ℓ N` of three layers, the two lower ones of height `ℓ`. `N` is the
signature limit.

The proofs are generated: `Lifetimes.lean` proves one theorem per configuration from the certificates
of `Certificates/`, which the kernel checks. The proof below only collects them, so a configuration of
this list that is not exactly the one a proof is about does not typecheck.
-/

namespace LeanForest

/-- The 32 proved configurations. -/
def configurations : List Params := [
  -- h = 22: the full key; b = 20, 14, 13, 12, 10, 8; layered 10 + 6 + 6
  .pruned 22 22 81860000, .pruned 22 20 21760000, .pruned 22 14 405300, .pruned 22 13 208500,
  .pruned 22 12 107200, .pruned 22 10 28410, .pruned 22 8 7514, .layered 22 3 6 81860000,
  -- h = 24: the full key; b = 20, 14, 13, 12, 10, 8; layered 12 + 6 + 6
  .pruned 24 24 336700000, .pruned 24 20 23830000, .pruned 24 14 441500, .pruned 24 13 226800,
  .pruned 24 12 116600, .pruned 24 10 30810, .pruned 24 8 8154, .layered 24 3 6 336700000,
  -- h = 26: the full key; b = 20, 14, 13, 12, 10, 8; layered 12 + 7 + 7
  .pruned 26 26 1381000000, .pruned 26 20 26030000, .pruned 26 14 480100, .pruned 26 13 246900,
  .pruned 26 12 126900, .pruned 26 10 33480, .pruned 26 8 8830, .layered 26 3 7 1381000000,
  -- h = 28: the full key; b = 20, 14, 13, 12, 10, 8; layered 12 + 8 + 8
  .pruned 28 28 5634000000, .pruned 28 20 28350000, .pruned 28 14 522000, .pruned 28 13 267900,
  .pruned 28 12 137400, .pruned 28 10 36190, .pruned 28 8 9541, .layered 28 3 8 5634000000]

theorem configurations_length : configurations.length = 32 := rfl

/-- **Main theorem.** Each of the 32 configurations has 127 bits of classical SUF-CMA security in
the random-oracle model: an adversary whose runs make at most `q ≥ 1` hash queries in all (key
generation, signing and verification included) forges with probability at most `q / 2^127`. -/
theorem requestedSecurity : ∀ P ∈ configurations, SecurityBits P 127 := by
  simp only [configurations, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨Lifetimes.h22_full_bits, Lifetimes.h22_pruned20_bits, Lifetimes.h22_pruned14_bits, Lifetimes.h22_pruned13_bits,
    Lifetimes.h22_pruned12_bits, Lifetimes.h22_pruned10_bits, Lifetimes.h22_pruned8_bits, Lifetimes.h22_layered_bits,
    Lifetimes.h24_full_bits, Lifetimes.h24_pruned20_bits, Lifetimes.h24_pruned14_bits, Lifetimes.h24_pruned13_bits,
    Lifetimes.h24_pruned12_bits, Lifetimes.h24_pruned10_bits, Lifetimes.h24_pruned8_bits, Lifetimes.h24_layered_bits,
    Lifetimes.h26_full_bits, Lifetimes.h26_pruned20_bits, Lifetimes.h26_pruned14_bits, Lifetimes.h26_pruned13_bits,
    Lifetimes.h26_pruned12_bits, Lifetimes.h26_pruned10_bits, Lifetimes.h26_pruned8_bits, Lifetimes.h26_layered_bits,
    Lifetimes.h28_full_bits, Lifetimes.h28_pruned20_bits, Lifetimes.h28_pruned14_bits, Lifetimes.h28_pruned13_bits,
    Lifetimes.h28_pruned12_bits, Lifetimes.h28_pruned10_bits, Lifetimes.h28_pruned8_bits, Lifetimes.h28_layered_bits⟩

end LeanForest
