import LeanForest.VerificationCost

/-! **The 24 configurations: sizes and verification costs.** A configuration is a height `h` (22, 24,
26, 28, for lifetimes of about `2^26` to `2^32` signatures), a shape (pruned: one tree of height `h`,
of which key generation builds a kept subtree; layered: a hypertree whose bottom layers have height 6
and whose top layer is at most 12) and a hash (Keccak-256, BLAKE2s, SHA-256). The size of a signature
and the compressions of an accepted verification depend only on the height and the number of layers
(`Layout.signature_size`, `Cost.verification_compressions`): the theorems below hold for every
`Params` of the configuration, whatever its kept subtree and signature limit. The figures are those of
`scripts/scheme.py`. -/

open OracleComp

namespace LeanForest.Configurations

variable [Params]

open Concrete Cost

section h22_pruned

variable (hH : totalHeight = 22) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 22, one tree: 4,212 bytes. -/
theorem size_h22_pruned (signature : Signature) : (serializeSignature signature).length = 4212 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 22, one tree: an accepted signature costs 263 Keccak-f permutations. -/
theorem keccak256_h22_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 263 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 22, one tree: an accepted signature costs 299 compressions. -/
theorem blake2s_h22_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 299 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 22, one tree: an accepted signature costs 300 compressions. -/
theorem sha256_h22_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 300 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h22_pruned

section h22_layered

variable (hH : totalHeight = 22) (hd : numLayers = 3)
include hH hd

/-- Signature size, height 22, layers 10 + 6 + 6: 6,268 bytes. -/
theorem size_h22_layered (signature : Signature) : (serializeSignature signature).length = 6268 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 22, layers 10 + 6 + 6: an accepted signature costs 419 Keccak-f permutations. -/
theorem keccak256_h22_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 419 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 22, layers 10 + 6 + 6: an accepted signature costs 473 compressions. -/
theorem blake2s_h22_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 473 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 22, layers 10 + 6 + 6: an accepted signature costs 474 compressions. -/
theorem sha256_h22_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 474 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h22_layered

section h24_pruned

variable (hH : totalHeight = 24) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 24, one tree: 4,244 bytes. -/
theorem size_h24_pruned (signature : Signature) : (serializeSignature signature).length = 4244 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 24, one tree: an accepted signature costs 265 Keccak-f permutations. -/
theorem keccak256_h24_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 265 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 24, one tree: an accepted signature costs 301 compressions. -/
theorem blake2s_h24_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 301 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 24, one tree: an accepted signature costs 302 compressions. -/
theorem sha256_h24_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 302 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h24_pruned

section h24_layered

variable (hH : totalHeight = 24) (hd : numLayers = 3)
include hH hd

/-- Signature size, height 24, layers 12 + 6 + 6: 6,300 bytes. -/
theorem size_h24_layered (signature : Signature) : (serializeSignature signature).length = 6300 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 24, layers 12 + 6 + 6: an accepted signature costs 421 Keccak-f permutations. -/
theorem keccak256_h24_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 421 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 24, layers 12 + 6 + 6: an accepted signature costs 475 compressions. -/
theorem blake2s_h24_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 475 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 24, layers 12 + 6 + 6: an accepted signature costs 476 compressions. -/
theorem sha256_h24_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 476 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h24_layered

section h26_pruned

variable (hH : totalHeight = 26) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 26, one tree: 4,276 bytes. -/
theorem size_h26_pruned (signature : Signature) : (serializeSignature signature).length = 4276 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 26, one tree: an accepted signature costs 267 Keccak-f permutations. -/
theorem keccak256_h26_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 267 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 26, one tree: an accepted signature costs 303 compressions. -/
theorem blake2s_h26_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 303 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 26, one tree: an accepted signature costs 304 compressions. -/
theorem sha256_h26_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 304 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h26_pruned

section h26_layered

variable (hH : totalHeight = 26) (hd : numLayers = 4)
include hH hd

/-- Signature size, height 26, layers 8 + 6 + 6 + 6: 7,360 bytes. -/
theorem size_h26_layered (signature : Signature) : (serializeSignature signature).length = 7360 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 26, layers 8 + 6 + 6 + 6: an accepted signature costs 501 Keccak-f permutations. -/
theorem keccak256_h26_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 501 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 26, layers 8 + 6 + 6 + 6: an accepted signature costs 564 compressions. -/
theorem blake2s_h26_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 564 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 26, layers 8 + 6 + 6 + 6: an accepted signature costs 565 compressions. -/
theorem sha256_h26_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 565 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h26_layered

section h28_pruned

variable (hH : totalHeight = 28) (hd : numLayers = 1)
include hH hd

/-- Signature size, height 28, one tree: 4,308 bytes. -/
theorem size_h28_pruned (signature : Signature) : (serializeSignature signature).length = 4308 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 28, one tree: an accepted signature costs 269 Keccak-f permutations. -/
theorem keccak256_h28_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 269 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 28, one tree: an accepted signature costs 305 compressions. -/
theorem blake2s_h28_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 305 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 28, one tree: an accepted signature costs 306 compressions. -/
theorem sha256_h28_pruned (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 306 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h28_pruned

section h28_layered

variable (hH : totalHeight = 28) (hd : numLayers = 4)
include hH hd

/-- Signature size, height 28, layers 10 + 6 + 6 + 6: 7,392 bytes. -/
theorem size_h28_layered (signature : Signature) : (serializeSignature signature).length = 7392 := by
  rw [signature_size, hH, hd]

/-- Keccak-256, height 28, layers 10 + 6 + 6 + 6: an accepted signature costs 503 Keccak-f permutations. -/
theorem keccak256_h28_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 503 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- BLAKE2s, height 28, layers 10 + 6 + 6 + 6: an accepted signature costs 566 compressions. -/
theorem blake2s_h28_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .blake2s f pk message signature = 566 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

/-- SHA-256, height 28, layers 10 + 6 + 6 + 6: an accepted signature costs 567 compressions. -/
theorem sha256_h28_layered (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .sha256 f pk message signature = 567 := by
  rw [verification_compressions _ f pk message signature haccept, verifyCost, hH, hd]
  rfl

end h28_layered

end LeanForest.Configurations
