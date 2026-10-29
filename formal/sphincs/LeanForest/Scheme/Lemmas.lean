import LeanForest.Scheme

/-! Facts about the specification (`Scheme.lean`): the definitions that only the proofs use, the
codeword table as a rule (`codewordCodes_eq_rule`), the randomizer walk, which does not come back
within `2^128` steps (`walk_iterate_ne`), and the bounds that the parameters (`Params`) give. -/

namespace LeanForest

variable [Params]

/-! ### Definitions of the proofs

Values that the specification does not use but the proofs name: the codeword sum, the bottom layer,
the order of the layers in a signature, the key on the path of an index, the kept leaves, the start
and the values of a single chain, and the end of a signature once a randomizer lands. -/

/-- The deficit sum of a codeword. -/
def codewordSum : Nat := 5

/-- The bottom layer, whose WOTS+C keys sign the forest keys. -/
def bottomLayer : Layer := ⟨numLayers - 1, Nat.sub_lt Params.numLayers_pos Nat.one_pos⟩

/-- The layer `k` steps above the bottom one (the top layer from `k = numLayers - 1` on): the
signature lists the layers in that order. -/
def layerUp (k : Nat) : Layer := ⟨numLayers - 1 - k, by have := Params.numLayers_pos; omega⟩

/-- A leaf of a layer's tree that its kept part holds: one of the top layer's kept subtree, any leaf
below the top layer. -/
def Kept (parameter : PublicParameter) (lay : Layer) (leaf : LeafIndex) : Prop :=
  leaf.val / 2 ^ keptHeight lay = keptPosition parameter lay

namespace Concrete

/-- A WOTS+C key of the hypertree: its layer, its tree and its leaf in that tree. -/
abbrev OtsKey := Layer × TreeIndex × LeafIndex

/-- The key of layer `lay` on the path of `idx`. -/
def keyAt (index : Index) (lay : Layer) : OtsKey := (lay, treeIndexAt index lay, leafIndexAt index lay)

end Concrete

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The start of one chain of a one-time key, by its own derivation. The signer calls `otsSecrets`;
this is the value of each of its entries (`Completeness.eval_otsSecrets`). -/
def otsStart (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.ots lay tree leaf (chainPair chainIdx)) seed
  return hashHalf chainIdx.val output

/-- The start `x_{i,0}` of one chain of a child, by its own derivation. The signer calls
`forestSecrets`; this is the value of each of its entries (`Completeness.eval_forestSecrets`). -/
def forestStart (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.forest index c s j a (fchainPair i)) seed
  return hashHalf i.val output

/-- The forest chain value `x_{i,pos}` of a child, by its own derivation. The signer computes the 6
chains of a child from one call of `forestSecrets` (`childLeaf`, `coordOpen`); this is the value of
each of them. -/
def chainValue (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (seed : MasterSeed) (pos : Nat) : m Digest := do
  let secret ← forestStart parameter index c s j a i seed
  forestWalk parameter index c s j a i 0 pos secret

/-- Assemble the signature once a randomizer lands: the digest, the forest opening and the layers. -/
def finishSign (sk : SecretKey) (message : Message) (randomness : Randomness) :
    OracleComp HashSpec (Option Signature) := do
  let digest ← messageDigest sk.parameter sk.root message randomness
  let index := digestIndex digest
  let opening ← forestOpen sk.parameter index (digestMarks digest) sk.seed
  let some layers ← sequenceLayers (fun lay => signLayer sk index lay) | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

/-! ### The codeword table -/

/-- The table as a rule. The codewords are the base-5 numbers below `5^6` with digit sum 5, in
increasing (that is, lexicographic) order; they are sorted by decreasing sum of squared digits (at
most 17), and entry `t` is codeword number `t mod 214`. -/
def codewordRule : List Nat :=
  let digit (c i : Nat) : Nat := c / 5 ^ i % 5
  let words := (List.range (5 ^ 6)).filter fun c => ((List.range 6).map (digit c)).sum = 5
  let sorted := (List.range 18).reverse.flatMap fun k =>
    words.filter fun c => ((List.range 6).map fun i => digit c i ^ 2).sum = k
  (List.range 256).map fun t => sorted.getD (t % 214) 0

theorem codewordCodes_eq_rule : codewordCodes = codewordRule := by decide +kernel

/-! ### The randomizer walk -/

theorem walkStep_toNat_mod_two (half : Randomness) : (walkStep half).toNat % 2 = 1 := by
  unfold walkStep
  rw [BitVec.toNat_or, Nat.or_mod_two_eq_one]
  right
  rfl

/-- `j` steps of the walk from `y`. -/
theorem walk_iterate (step y : Randomness) (j : Nat) :
    (fun x : Randomness => x + step)^[j] y = y + (j : Randomness) * step := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      push_cast
      ring

/-- A walk with an odd step does not come back within `2^128` steps. -/
theorem walk_iterate_ne (half y : Randomness) (j : Nat) (hj : j + 1 < 2 ^ 128) :
    (fun x : Randomness => x + walkStep half)^[j] (y + walkStep half) ≠ y := by
  rw [walk_iterate]
  intro h
  have hzero : ((j + 1 : Nat) : Randomness) * walkStep half = 0 := by
    push_cast
    linear_combination h
  have h2 := congrArg BitVec.toNat hzero
  have hd : (2 : Nat) ^ digestBits = 2 ^ 128 := rfl
  rw [BitVec.toNat_mul, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, hd, Nat.mod_eq_of_lt hj] at h2
  have hdvd : 2 ^ 128 ∣ (j + 1) * (walkStep half).toNat := Nat.dvd_of_mod_eq_zero h2
  have hcop : Nat.Coprime (2 ^ 128) (walkStep half).toNat :=
    Nat.Coprime.pow_left 128 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (walkStep_toNat_mod_two half)))
  have := Nat.le_of_dvd (Nat.succ_pos j) (hcop.dvd_of_dvd_mul_right hdvd)
  omega

/-! ### Bounds of the parameters -/

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt' {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

theorem totalHeight_le_28 : totalHeight ≤ 28 := Params.totalHeight_le

theorem subtreeHeight_le_total : subtreeHeight ≤ totalHeight := Params.subtreeHeight_le

theorem numLayers_pos : 0 < numLayers := Params.numLayers_pos

/-- The index field lies inside the hash output. -/
theorem indexOffset_add_le : Concrete.indexOffset + totalHeight ≤ hashOutputBits := by
  have := totalHeight_le_28
  have := Params.forestCoords_le
  unfold Concrete.indexOffset hashOutputBits subHeight topHeight
  omega

/-- The index field lies inside the truncated digest. -/
theorem indexOffset_add_le_digest : Concrete.indexOffset + totalHeight ≤ messageDigestBits := by
  unfold Concrete.indexOffset messageDigestBits subHeight topHeight coordBits
  omega

theorem two_pow_totalHeight_le : 2 ^ totalHeight ≤ 2 ^ 28 :=
  Nat.pow_le_pow_right (by decide) totalHeight_le_28

theorem index_lt_two_pow_32 (index : Index) : index.val < 2 ^ 32 :=
  lt_of_lt_of_le index.isLt (two_pow_totalHeight_le.trans (by decide))

theorem maxLayerHeight_le : maxLayerHeight ≤ totalHeight := Nat.sub_le _ _

/-- The top layer is at least as tall as a lower one. -/
theorem lowerHeight_le_max : lowerHeight ≤ maxLayerHeight := by
  have h1 := Params.lower_le
  have h2 := Params.numLayers_pos
  unfold maxLayerHeight
  have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

theorem lowerHeight_pos : 0 < lowerHeight := lt_of_lt_of_le (by decide) Params.lowerHeight_ge

theorem maxLayerHeight_pos : 0 < maxLayerHeight :=
  lt_of_lt_of_le lowerHeight_pos lowerHeight_le_max

theorem messageDigestBits_le : messageDigestBits ≤ hashOutputBits := by
  have := totalHeight_le_28
  have := Params.forestCoords_le
  unfold messageDigestBits hashOutputBits coordBits
  omega

/-- At most 4 layers: the layers below the top have height at least 6 and `h ≤ 28`. -/
theorem numLayers_le : numLayers ≤ 4 := by
  have h1 := Params.lower_le
  have := totalHeight_le_28
  have h2 : 6 * numLayers ≤ lowerHeight * numLayers := Nat.mul_le_mul_right numLayers Params.lowerHeight_ge
  omega

theorem tree_lt_two_pow_32 (tree : TreeIndex) : tree.val < 2 ^ 32 :=
  lt_of_lt_of_le tree.isLt (two_pow_totalHeight_le.trans (by decide))

theorem leaf_lt_two_pow_32 (leaf : LeafIndex) : leaf.val < 2 ^ 32 :=
  lt_of_lt_of_le leaf.isLt ((Nat.pow_le_pow_right (by decide) maxLayerHeight_le).trans
    (two_pow_totalHeight_le.trans (by decide)))

/-- The layer byte names the layer. -/
theorem layerByte_lt (lay : Layer) : layerByte lay < 2 ^ 8 := by
  have := numLayers_le
  unfold layerByte
  omega

theorem layerByte_injective {lay lay' : Layer} (h : layerByte lay = layerByte lay') : lay = lay' := by
  have := lay.isLt; have := lay'.isLt
  unfold layerByte at h
  exact Fin.ext (by omega)

/-- The layer byte, as encoded, names the layer. -/
theorem layerByte_ofNat_injective {lay lay' : Layer}
    (h : BitVec.ofNat 8 (layerByte lay) = BitVec.ofNat 8 (layerByte lay')) : lay = lay' :=
  layerByte_injective (ofNat_inj_of_lt' (layerByte_lt lay) (layerByte_lt lay') h)

end LeanForest
