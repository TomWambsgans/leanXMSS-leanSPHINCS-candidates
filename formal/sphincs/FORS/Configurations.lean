import FORS.Scheme.VerificationCost

/-! **The FORS configurations: sizes and verification costs.** A configuration is a height `h`
(20, 22, 24, 26, 28), a shape (pruned: one tree of height `h`, of which key generation builds a kept
subtree; layered: a hypertree of three layers, a top layer of 10 (8 at
`h = 20`) over two equal layers of 6 to 9), FORS of `k = 24` trees of height `a = 10` (the same in every configuration) and a hash
(Keccak-256, BLAKE2s, SHA-256). The size of a signature and the compressions of an accepted
verification depend only on the height, the number of layers and FORS (`Layout.signature_size`,
`Cost.verification_compressions`): the theorems below hold for every `Params` of the configuration,
whatever its kept subtree and signature limit. The figures are those of `scripts/scheme.py`. -/

open OracleComp

namespace FORS.Configurations

variable [Params]

open Concrete Cost

section h20_pruned_k24

variable (hH : totalHeight = 20) (hd : numLayers = 1) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 20, one tree, `k = 24`: 5,588 bytes. -/
theorem size_h20_pruned_k24 (signature : Signature) : (serializeSignature signature).length = 5588 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 20, one tree, `k = 24`: an accepted signature costs 340 Keccak-f permutations. -/
theorem keccak256_h20_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 340 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 20, one tree, `k = 24`: an accepted signature costs 358 compressions. -/
theorem blake2s_h20_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 358 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 20, one tree, `k = 24`: an accepted signature costs 359 compressions. -/
theorem sha256_h20_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 359 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h20_pruned_k24

section h20_layered_k24

variable (hH : totalHeight = 20) (hd : numLayers = 3) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 20, layers 8 + 6 + 6, `k = 24`: 7,644 bytes. -/
theorem size_h20_layered_k24 (signature : Signature) : (serializeSignature signature).length = 7644 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 20, layers 8 + 6 + 6, `k = 24`: an accepted signature costs 486 Keccak-f permutations. -/
theorem keccak256_h20_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 486 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 20, layers 8 + 6 + 6, `k = 24`: an accepted signature costs 522 compressions. -/
theorem blake2s_h20_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 522 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 20, layers 8 + 6 + 6, `k = 24`: an accepted signature costs 523 compressions. -/
theorem sha256_h20_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 523 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h20_layered_k24

section h22_pruned_k24

variable (hH : totalHeight = 22) (hd : numLayers = 1) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 22, one tree, `k = 24`: 5,620 bytes. -/
theorem size_h22_pruned_k24 (signature : Signature) : (serializeSignature signature).length = 5620 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 22, one tree, `k = 24`: an accepted signature costs 342 Keccak-f permutations. -/
theorem keccak256_h22_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 342 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 22, one tree, `k = 24`: an accepted signature costs 360 compressions. -/
theorem blake2s_h22_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 360 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 22, one tree, `k = 24`: an accepted signature costs 361 compressions. -/
theorem sha256_h22_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 361 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h22_pruned_k24

section h22_layered_k24

variable (hH : totalHeight = 22) (hd : numLayers = 3) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 22, layers 10 + 6 + 6, `k = 24`: 7,676 bytes. -/
theorem size_h22_layered_k24 (signature : Signature) : (serializeSignature signature).length = 7676 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 22, layers 10 + 6 + 6, `k = 24`: an accepted signature costs 488 Keccak-f permutations. -/
theorem keccak256_h22_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 488 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 22, layers 10 + 6 + 6, `k = 24`: an accepted signature costs 524 compressions. -/
theorem blake2s_h22_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 524 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 22, layers 10 + 6 + 6, `k = 24`: an accepted signature costs 525 compressions. -/
theorem sha256_h22_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 525 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h22_layered_k24

section h24_pruned_k24

variable (hH : totalHeight = 24) (hd : numLayers = 1) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 24, one tree, `k = 24`: 5,652 bytes. -/
theorem size_h24_pruned_k24 (signature : Signature) : (serializeSignature signature).length = 5652 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 24, one tree, `k = 24`: an accepted signature costs 344 Keccak-f permutations. -/
theorem keccak256_h24_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 344 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 24, one tree, `k = 24`: an accepted signature costs 362 compressions. -/
theorem blake2s_h24_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 362 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 24, one tree, `k = 24`: an accepted signature costs 363 compressions. -/
theorem sha256_h24_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 363 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h24_pruned_k24

section h24_layered_k24

variable (hH : totalHeight = 24) (hd : numLayers = 3) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 24, layers 10 + 7 + 7, `k = 24`: 7,708 bytes. -/
theorem size_h24_layered_k24 (signature : Signature) : (serializeSignature signature).length = 7708 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 24, layers 10 + 7 + 7, `k = 24`: an accepted signature costs 490 Keccak-f permutations. -/
theorem keccak256_h24_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 490 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 24, layers 10 + 7 + 7, `k = 24`: an accepted signature costs 526 compressions. -/
theorem blake2s_h24_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 526 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 24, layers 10 + 7 + 7, `k = 24`: an accepted signature costs 527 compressions. -/
theorem sha256_h24_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 527 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h24_layered_k24

section h26_pruned_k24

variable (hH : totalHeight = 26) (hd : numLayers = 1) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 26, one tree, `k = 24`: 5,684 bytes. -/
theorem size_h26_pruned_k24 (signature : Signature) : (serializeSignature signature).length = 5684 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 26, one tree, `k = 24`: an accepted signature costs 346 Keccak-f permutations. -/
theorem keccak256_h26_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 346 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 26, one tree, `k = 24`: an accepted signature costs 364 compressions. -/
theorem blake2s_h26_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 364 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 26, one tree, `k = 24`: an accepted signature costs 365 compressions. -/
theorem sha256_h26_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 365 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h26_pruned_k24

section h26_layered_k24

variable (hH : totalHeight = 26) (hd : numLayers = 3) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 26, layers 10 + 8 + 8, `k = 24`: 7,740 bytes. -/
theorem size_h26_layered_k24 (signature : Signature) : (serializeSignature signature).length = 7740 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 26, layers 10 + 8 + 8, `k = 24`: an accepted signature costs 492 Keccak-f permutations. -/
theorem keccak256_h26_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 492 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 26, layers 10 + 8 + 8, `k = 24`: an accepted signature costs 528 compressions. -/
theorem blake2s_h26_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 528 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 26, layers 10 + 8 + 8, `k = 24`: an accepted signature costs 529 compressions. -/
theorem sha256_h26_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 529 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h26_layered_k24

section h28_pruned_k24

variable (hH : totalHeight = 28) (hd : numLayers = 1) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 28, one tree, `k = 24`: 5,716 bytes. -/
theorem size_h28_pruned_k24 (signature : Signature) : (serializeSignature signature).length = 5716 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 28, one tree, `k = 24`: an accepted signature costs 348 Keccak-f permutations. -/
theorem keccak256_h28_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 348 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 28, one tree, `k = 24`: an accepted signature costs 366 compressions. -/
theorem blake2s_h28_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 366 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 28, one tree, `k = 24`: an accepted signature costs 367 compressions. -/
theorem sha256_h28_pruned_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 367 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h28_pruned_k24

section h28_layered_k24

variable (hH : totalHeight = 28) (hd : numLayers = 3) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 28, layers 10 + 9 + 9, `k = 24`: 7,772 bytes. -/
theorem size_h28_layered_k24 (signature : Signature) : (serializeSignature signature).length = 7772 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 28, layers 10 + 9 + 9, `k = 24`: an accepted signature costs 494 Keccak-f permutations. -/
theorem keccak256_h28_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 494 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- BLAKE2s, height 28, layers 10 + 9 + 9, `k = 24`: an accepted signature costs 530 compressions. -/
theorem blake2s_h28_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 530 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

/-- SHA-256, height 28, layers 10 + 9 + 9, `k = 24`: an accepted signature costs 531 compressions. -/
theorem sha256_h28_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 531 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, digestCalls,
    messageDigestBits, hH, hd, hk, ha]
  rfl

end h28_layered_k24

end FORS.Configurations
