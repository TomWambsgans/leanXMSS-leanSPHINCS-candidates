import FORS.Scheme.VerificationCost

/-! **The FORS configurations: sizes and verification costs.** A configuration is a height `h`
(22, 24, 26, 28), a shape (pruned: one tree of height `h`, of which key generation builds a kept
subtree; layered: a hypertree of three layers, a top layer of at most 12 over two equal layers of at
least 6), FORS of `k = 25` trees of height `a = 10` (the same for every pruning) and a hash
(Keccak-256, BLAKE2s, SHA-256). The size of a signature and the compressions of an accepted
verification depend only on the height, the number of layers and FORS (`Layout.signature_size`,
`Cost.verification_compressions`): the theorems below hold for every `Params` of the configuration,
whatever its kept subtree and signature limit. The figures are those of `scripts/scheme.py`. -/

open OracleComp

namespace FORS.Configurations

variable [Params]

open Concrete Cost

section h22_pruned_k25

variable (hH : totalHeight = 22) (hd : numLayers = 1) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 22, one tree, `k = 25`: 5,796 bytes. -/
theorem size_h22_pruned_k25 (signature : Signature) : (serializeSignature signature).length = 5796 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 22, one tree, `k = 25`: an accepted signature costs 353 Keccak-f permutations. -/
theorem keccak256_h22_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 353 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 22, one tree, `k = 25`: an accepted signature costs 371 compressions. -/
theorem blake2s_h22_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 371 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 22, one tree, `k = 25`: an accepted signature costs 371 compressions. -/
theorem sha256_h22_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 371 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h22_pruned_k25

section h22_layered_k25

variable (hH : totalHeight = 22) (hd : numLayers = 3) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 22, layers 10 + 6 + 6, `k = 25`: 7,852 bytes. -/
theorem size_h22_layered_k25 (signature : Signature) : (serializeSignature signature).length = 7852 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 22, layers 10 + 6 + 6, `k = 25`: an accepted signature costs 499 Keccak-f permutations. -/
theorem keccak256_h22_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 499 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 22, layers 10 + 6 + 6, `k = 25`: an accepted signature costs 535 compressions. -/
theorem blake2s_h22_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 535 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 22, layers 10 + 6 + 6, `k = 25`: an accepted signature costs 535 compressions. -/
theorem sha256_h22_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 535 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h22_layered_k25

section h24_pruned_k25

variable (hH : totalHeight = 24) (hd : numLayers = 1) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 24, one tree, `k = 25`: 5,828 bytes. -/
theorem size_h24_pruned_k25 (signature : Signature) : (serializeSignature signature).length = 5828 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 24, one tree, `k = 25`: an accepted signature costs 355 Keccak-f permutations. -/
theorem keccak256_h24_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 355 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 24, one tree, `k = 25`: an accepted signature costs 373 compressions. -/
theorem blake2s_h24_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 373 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 24, one tree, `k = 25`: an accepted signature costs 373 compressions. -/
theorem sha256_h24_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 373 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h24_pruned_k25

section h24_layered_k25

variable (hH : totalHeight = 24) (hd : numLayers = 3) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 24, layers 12 + 6 + 6, `k = 25`: 7,884 bytes. -/
theorem size_h24_layered_k25 (signature : Signature) : (serializeSignature signature).length = 7884 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 24, layers 12 + 6 + 6, `k = 25`: an accepted signature costs 501 Keccak-f permutations. -/
theorem keccak256_h24_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 501 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 24, layers 12 + 6 + 6, `k = 25`: an accepted signature costs 537 compressions. -/
theorem blake2s_h24_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 537 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 24, layers 12 + 6 + 6, `k = 25`: an accepted signature costs 537 compressions. -/
theorem sha256_h24_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 537 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h24_layered_k25

section h26_pruned_k25

variable (hH : totalHeight = 26) (hd : numLayers = 1) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 26, one tree, `k = 25`: 5,860 bytes. -/
theorem size_h26_pruned_k25 (signature : Signature) : (serializeSignature signature).length = 5860 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 26, one tree, `k = 25`: an accepted signature costs 357 Keccak-f permutations. -/
theorem keccak256_h26_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 357 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 26, one tree, `k = 25`: an accepted signature costs 375 compressions. -/
theorem blake2s_h26_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 375 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 26, one tree, `k = 25`: an accepted signature costs 375 compressions. -/
theorem sha256_h26_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 375 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h26_pruned_k25

section h26_layered_k25

variable (hH : totalHeight = 26) (hd : numLayers = 3) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 26, layers 12 + 7 + 7, `k = 25`: 7,916 bytes. -/
theorem size_h26_layered_k25 (signature : Signature) : (serializeSignature signature).length = 7916 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 26, layers 12 + 7 + 7, `k = 25`: an accepted signature costs 503 Keccak-f permutations. -/
theorem keccak256_h26_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 503 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 26, layers 12 + 7 + 7, `k = 25`: an accepted signature costs 539 compressions. -/
theorem blake2s_h26_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 539 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 26, layers 12 + 7 + 7, `k = 25`: an accepted signature costs 539 compressions. -/
theorem sha256_h26_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 539 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h26_layered_k25

section h28_pruned_k25

variable (hH : totalHeight = 28) (hd : numLayers = 1) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 28, one tree, `k = 25`: 5,892 bytes. -/
theorem size_h28_pruned_k25 (signature : Signature) : (serializeSignature signature).length = 5892 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 28, one tree, `k = 25`: an accepted signature costs 359 Keccak-f permutations. -/
theorem keccak256_h28_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 359 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 28, one tree, `k = 25`: an accepted signature costs 377 compressions. -/
theorem blake2s_h28_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 377 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 28, one tree, `k = 25`: an accepted signature costs 377 compressions. -/
theorem sha256_h28_pruned_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 377 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h28_pruned_k25

section h28_layered_k25

variable (hH : totalHeight = 28) (hd : numLayers = 3) (hk : forsTrees = 25) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 28, layers 12 + 8 + 8, `k = 25`: 7,948 bytes. -/
theorem size_h28_layered_k25 (signature : Signature) : (serializeSignature signature).length = 7948 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 28, layers 12 + 8 + 8, `k = 25`: an accepted signature costs 505 Keccak-f permutations. -/
theorem keccak256_h28_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 505 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 28, layers 12 + 8 + 8, `k = 25`: an accepted signature costs 541 compressions. -/
theorem blake2s_h28_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 541 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 28, layers 12 + 8 + 8, `k = 25`: an accepted signature costs 541 compressions. -/
theorem sha256_h28_layered_k25 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 541 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h28_layered_k25

end FORS.Configurations
