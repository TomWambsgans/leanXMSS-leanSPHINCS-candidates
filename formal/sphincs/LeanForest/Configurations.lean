import LeanForest.Scheme.VerificationCost

/-! **The 30 configurations: sizes and verification costs.** A configuration is a height `h` (20, 22,
24, 26, 28, for lifetimes of about `2^24` to `2^32` signatures), a shape (pruned: one tree of height `h`,
of which key generation builds a kept subtree; layered: a hypertree of three layers, a top layer of 10
(8 at h = 20) over two equal layers of 6 to 9) and a hash (Keccak-256, BLAKE2s, SHA-256). The size of a
signature and the compressions of an accepted verification depend only on the height and the number of layers
(`Layout.signature_size`, `Cost.verification_compressions`): the theorems below hold for every
`Params` of the configuration, whatever its kept subtree and signature limit. The figures are those of
`scripts/scheme.py`. -/

open OracleComp

namespace LeanForest.Configurations

variable [Params]

open Concrete Cost

section h20_pruned

variable (hH : totalHeight = 20) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 20, one tree: 4,180 bytes. -/
theorem size_h20_pruned (signature : Signature) : (serializeSignature signature).length = 4180 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 20, one tree: an accepted signature costs 256 Keccak-f permutations. -/
theorem keccak256_h20_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 256 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 20, one tree: an accepted signature costs 292 compressions. -/
theorem blake2s_h20_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 292 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 20, one tree: an accepted signature costs 293 compressions. -/
theorem sha256_h20_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 293 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h20_pruned

section h20_layered

variable (hH : totalHeight = 20) (hd : numLayers = 3)
include hH hd

/-- Signature size, height 20, layers 8 + 6 + 6: 6,236 bytes. -/
theorem size_h20_layered (signature : Signature) : (serializeSignature signature).length = 6236 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 20, layers 8 + 6 + 6: an accepted signature costs 402 Keccak-f permutations. -/
theorem keccak256_h20_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 402 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 20, layers 8 + 6 + 6: an accepted signature costs 456 compressions. -/
theorem blake2s_h20_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 456 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 20, layers 8 + 6 + 6: an accepted signature costs 457 compressions. -/
theorem sha256_h20_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 457 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h20_layered

section h22_pruned

variable (hH : totalHeight = 22) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 22, one tree: 4,212 bytes. -/
theorem size_h22_pruned (signature : Signature) : (serializeSignature signature).length = 4212 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 22, one tree: an accepted signature costs 258 Keccak-f permutations. -/
theorem keccak256_h22_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 258 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 22, one tree: an accepted signature costs 294 compressions. -/
theorem blake2s_h22_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 294 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 22, one tree: an accepted signature costs 295 compressions. -/
theorem sha256_h22_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 295 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h22_pruned

section h22_layered

variable (hH : totalHeight = 22) (hd : numLayers = 3)
include hH hd

/-- Signature size, height 22, layers 10 + 6 + 6: 6,268 bytes. -/
theorem size_h22_layered (signature : Signature) : (serializeSignature signature).length = 6268 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 22, layers 10 + 6 + 6: an accepted signature costs 404 Keccak-f permutations. -/
theorem keccak256_h22_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 404 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 22, layers 10 + 6 + 6: an accepted signature costs 458 compressions. -/
theorem blake2s_h22_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 458 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 22, layers 10 + 6 + 6: an accepted signature costs 459 compressions. -/
theorem sha256_h22_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 459 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h22_layered

section h24_pruned

variable (hH : totalHeight = 24) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 24, one tree: 4,244 bytes. -/
theorem size_h24_pruned (signature : Signature) : (serializeSignature signature).length = 4244 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 24, one tree: an accepted signature costs 260 Keccak-f permutations. -/
theorem keccak256_h24_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 260 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 24, one tree: an accepted signature costs 296 compressions. -/
theorem blake2s_h24_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 296 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 24, one tree: an accepted signature costs 297 compressions. -/
theorem sha256_h24_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 297 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h24_pruned

section h24_layered

variable (hH : totalHeight = 24) (hd : numLayers = 3)
include hH hd

/-- Signature size, height 24, layers 10 + 7 + 7: 6,300 bytes. -/
theorem size_h24_layered (signature : Signature) : (serializeSignature signature).length = 6300 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 24, layers 10 + 7 + 7: an accepted signature costs 406 Keccak-f permutations. -/
theorem keccak256_h24_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 406 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 24, layers 10 + 7 + 7: an accepted signature costs 460 compressions. -/
theorem blake2s_h24_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 460 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 24, layers 10 + 7 + 7: an accepted signature costs 461 compressions. -/
theorem sha256_h24_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 461 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h24_layered

section h26_pruned

variable (hH : totalHeight = 26) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 26, one tree: 4,276 bytes. -/
theorem size_h26_pruned (signature : Signature) : (serializeSignature signature).length = 4276 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 26, one tree: an accepted signature costs 262 Keccak-f permutations. -/
theorem keccak256_h26_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 262 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 26, one tree: an accepted signature costs 298 compressions. -/
theorem blake2s_h26_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 298 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 26, one tree: an accepted signature costs 299 compressions. -/
theorem sha256_h26_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 299 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h26_pruned

section h26_layered

variable (hH : totalHeight = 26) (hd : numLayers = 3)
include hH hd

/-- Signature size, height 26, layers 10 + 8 + 8: 6,332 bytes. -/
theorem size_h26_layered (signature : Signature) : (serializeSignature signature).length = 6332 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 26, layers 10 + 8 + 8: an accepted signature costs 408 Keccak-f permutations. -/
theorem keccak256_h26_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 408 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 26, layers 10 + 8 + 8: an accepted signature costs 462 compressions. -/
theorem blake2s_h26_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 462 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 26, layers 10 + 8 + 8: an accepted signature costs 463 compressions. -/
theorem sha256_h26_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 463 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h26_layered

section h28_pruned

variable (hH : totalHeight = 28) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 28, one tree: 4,308 bytes. -/
theorem size_h28_pruned (signature : Signature) : (serializeSignature signature).length = 4308 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 28, one tree: an accepted signature costs 264 Keccak-f permutations. -/
theorem keccak256_h28_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 264 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 28, one tree: an accepted signature costs 300 compressions. -/
theorem blake2s_h28_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 300 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 28, one tree: an accepted signature costs 301 compressions. -/
theorem sha256_h28_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 301 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h28_pruned

section h28_layered

variable (hH : totalHeight = 28) (hd : numLayers = 3)
include hH hd

/-- Signature size, height 28, layers 10 + 9 + 9: 6,364 bytes. -/
theorem size_h28_layered (signature : Signature) : (serializeSignature signature).length = 6364 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 28, layers 10 + 9 + 9: an accepted signature costs 410 Keccak-f permutations. -/
theorem keccak256_h28_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 410 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 28, layers 10 + 9 + 9: an accepted signature costs 464 compressions. -/
theorem blake2s_h28_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 464 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 28, layers 10 + 9 + 9: an accepted signature costs 465 compressions. -/
theorem sha256_h28_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 465 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h28_layered

end LeanForest.Configurations
