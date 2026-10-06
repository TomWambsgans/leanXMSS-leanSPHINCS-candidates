import LeanForest.Uniform
import Mathlib.Data.BitVec

/-!
The full view of a 234-bit message digest (its index and the 26-bit field of each of the 8 trees)
is a bijection, so a uniform digest gives a uniform view. A field decodes to the tree's mark: the
leaf of the tree, and for each of the two subtrees the WOTS key and the codeword index. Coverage of a
view by disclosed fields: every chain of both WOTS keys of every tree is disclosed at or below the
position the view needs.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000
set_option exponentiation.threshold 512

namespace LeanForest.Concrete

/-- The 26 bits of one tree's field. -/
abbrev FieldVal := Fin (2 ^ coordBits)

abbrev FullDigestView := Index × (Coord → FieldVal)

/-- The field of tree `c` of a digest. -/
def coordField (digest : MessageDigest) (c : Coord) : FieldVal :=
  (digest.extractLsb' (coordOffset c) coordBits).toFin

def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, coordField digest)

theorem fullDigestView_injective : Function.Injective fullDigestView := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hindex : position < totalHeight
  · have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin view.1) heq
    have hbit := congrArg (fun bits : BitVec totalHeight => bits.getLsbD position) hcomponent
    simpa [fullDigestView, digestIndex, BitVec.getLsbD_extractLsb', hindex] using hbit
  · let treeIndex := (position - totalHeight) / coordBits
    have htreeIndex : treeIndex < forestCoords := by
      have hposition' : position < 234 := by
        simpa [messageDigestBits, totalHeight, forestCoords, coordBits] using hposition
      have hindex' : 26 ≤ position := by
        simpa [totalHeight] using Nat.le_of_not_gt hindex
      simp only [treeIndex, forestCoords, coordBits, totalHeight]
      omega
    let tree : Coord := ⟨treeIndex, htreeIndex⟩
    let within := (position - totalHeight) % coordBits
    have hwithin : within < coordBits := by
      simp only [within, coordBits]
      omega
    have hoffset : totalHeight + coordBits * tree.val + within = position := by
      have hindex' : totalHeight ≤ position := Nat.le_of_not_gt hindex
      simp only [tree, treeIndex, within]
      calc
        totalHeight + coordBits * ((position - totalHeight) / coordBits) +
            (position - totalHeight) % coordBits =
            totalHeight + ((position - totalHeight) % coordBits +
              coordBits * ((position - totalHeight) / coordBits)) := by omega
        _ = totalHeight + (position - totalHeight) := by rw [Nat.mod_add_div]
        _ = position := Nat.add_sub_of_le hindex'
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin (view.2 tree)) heq
    change left.extractLsb' (totalHeight + coordBits * tree.val) coordBits =
      right.extractLsb' (totalHeight + coordBits * tree.val) coordBits at hcomponent
    have hbit := congrArg (fun bits : BitVec coordBits => bits.getLsbD within) hcomponent
    simp only [BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and] at hbit
    rwa [hoffset] at hbit

theorem fullDigestView_bijective : Function.Bijective fullDigestView := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fullDigestView_injective, ?_⟩
  rw [card_bitVec, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← pow_add]
  rfl

theorem evalDist_fullDigestView_uniform :
    𝒟[fullDigestView <$> ($ᵗ MessageDigest : ProbComp MessageDigest)] =
    𝒟[($ᵗ FullDigestView : ProbComp FullDigestView)] :=
  evalDist_map_bijective_uniform_cross (α := MessageDigest) (β := FullDigestView)
    fullDigestView fullDigestView_bijective

/-! ### Decoding a field -/

/-- The mark of a tree read from its field. -/
def decodeMark (v : FieldVal) : CoordMark where
  super := ((BitVec.ofFin v).extractLsb' 0 topHeight).toFin
  child := fun j => ((BitVec.ofFin v).extractLsb' (childOffset j) subHeight).toFin
  word := fun j => ((BitVec.ofFin v).extractLsb' (wordOffset j) 8).toFin

theorem extractLsb'_extractLsb' {w : Nat} (x : BitVec w) (o s len len' : Nat) (h : s + len ≤ len') :
    (x.extractLsb' o len').extractLsb' s len = x.extractLsb' (o + s) len := by
  ext k hk
  simp
  rw [decide_eq_true (show s + k < len' by omega), Bool.true_and, Nat.add_assoc]

/-- The marks the verifier reads are the decoded fields. -/
theorem digestMarks_eq (digest : MessageDigest) (c : Coord) :
    digestMarks digest c = decodeMark (coordField digest c) := by
  have hj : ∀ j : SubIdx, childOffset j + subHeight ≤ coordBits ∧ wordOffset j + 8 ≤ coordBits := by
    intro j
    have := j.isLt
    simp only [childOffset, wordOffset, subHeight, coordBits]
    omega
  simp only [digestMarks, decodeMark, coordField, BitVec.ofFin_toFin]
  congr 1
  · rw [extractLsb'_extractLsb' _ _ _ _ _ (by decide), Nat.add_zero]
  · funext j
    rw [extractLsb'_extractLsb' _ _ _ _ _ (hj j).1]
  · funext j
    rw [extractLsb'_extractLsb' _ _ _ _ _ (hj j).2]

/-! ### Coverage -/

/-- The deficit `d_i` that target field `t` needs at chain `i` of subtree `j`: the verifier starts
at position `4 - d_i`. -/
def chainNeed (t : FieldVal) (j : SubIdx) (i : FChain) : Nat := (lut ((decodeMark t).word j) i).val

/-- A disclosed field `v` opens the WOTS key that target field `t` needs in subtree `j`, at chain
`i`, at or below the position `t` needs. -/
def KeyCovers (v t : FieldVal) (j : SubIdx) (i : FChain) : Prop :=
  (decodeMark v).super = (decodeMark t).super ∧ (decodeMark v).child j = (decodeMark t).child j ∧
    chainNeed t j i ≤ chainNeed v j i

instance (v t : FieldVal) (j : SubIdx) (i : FChain) : Decidable (KeyCovers v t j i) := by
  unfold KeyCovers; infer_instance

/-- The revealed positions of every forest chain. -/
abbrev Disclosures := Index → Coord → SuperIdx → SubIdx → ChildIdx → FChain → Finset FPos

/-- Chain `i` of the WOTS key that the view selects in tree `c`, subtree `j`, needs only the public
top, or has a revealed position at or below the one the view needs. -/
def ChainCov (revealed : Disclosures) (view : FullDigestView) (c : Coord) (j : SubIdx) (i : FChain) : Prop :=
  chainNeed (view.2 c) j i = 0 ∨
    ∃ p ∈ revealed view.1 c (decodeMark (view.2 c)).super j ((decodeMark (view.2 c)).child j) i,
      p.val ≤ chainTop - chainNeed (view.2 c) j i

instance (revealed : Disclosures) (view : FullDigestView) (c : Coord) (j : SubIdx) (i : FChain) :
    Decidable (ChainCov revealed view c j i) := by
  unfold ChainCov; infer_instance

/-- Every chain of both WOTS keys of every tree that the view selects is covered. -/
def Covered (revealed : Disclosures) (view : FullDigestView) : Prop :=
  ∀ (c : Coord) (j : SubIdx) (i : FChain), ChainCov revealed view c j i

instance (revealed : Disclosures) : DecidablePred (Covered revealed) := fun view => by
  unfold Covered; infer_instance

end LeanForest.Concrete
