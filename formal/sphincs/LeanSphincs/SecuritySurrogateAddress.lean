import LeanSphincs.SecurityTreeWitness

/-! Keep the exact off-spine address when extracting a surrogate preimage. Assigning the
surrogate target only at this address avoids a multi-target loss and cannot overlap a prepared
canonical node. The first-divergence extraction follows leanVM b7a107256. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security
open Concrete
attribute [local irreducible] Seeded.treeNode Seeded.treeRoot Seeded.spineNode
set_option maxHeartbeats 600000

/-- Siblings have the same parent and opposite low bits. -/
theorem quotient_eq_sibling {index reference level : Nat}
    (hparent : index / 2 ^ (level + 1) = reference / 2 ^ (level + 1))
    (hbit : index.testBit level ≠ reference.testBit level) :
    index / 2 ^ level = Nat.xor (reference / 2 ^ level) 1 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hparent
  have hbit' : (index / 2 ^ level).testBit 0 ≠ (reference / 2 ^ level).testBit 0 := by
    simpa only [← Nat.testBit_add, Nat.zero_add] using hbit
  have hiparts := Nat.div_add_mod (index / 2 ^ level) 2
  have hrparts := Nat.div_add_mod (reference / 2 ^ level) 2
  cases hi : (index / 2 ^ level).testBit 0 <;>
    cases hr : (reference / 2 ^ level).testBit 0 <;>
    simp only [hi, hr, ne_eq, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
      not_true_eq_false] at hbit'
  · have himod := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hi
    have hrmod := Nat.mod_two_eq_one_iff_testBit_zero.mpr hr
    change index / 2 ^ level = reference / 2 ^ level ^^^ 1
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hrmod)]
    omega
  · have himod := Nat.mod_two_eq_one_iff_testBit_zero.mpr hi
    have hrmod := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hr
    change index / 2 ^ level = reference / 2 ^ level ^^^ 1
    rw [Nat.xor_one_of_even (Nat.even_iff.mpr hrmod)]
    omega

theorem xor_one_ne (index : Nat) : Nat.xor index 1 ≠ index := by
  intro heq
  change index ^^^ 1 = index at heq
  by_cases heven : index % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr heven)] at heq
    omega
  · have hodd : index % 2 = 1 := by omega
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hodd)] at heq
    omega

variable [Params]

def spineIndex (parameter : PublicParameter) (level : Nat) : Nat :=
  subtreePosition parameter / 2 ^ (level - subtreeHeight)

def boundaryIndex (parameter : PublicParameter) (level : Nat) : Nat :=
  Nat.xor (spineIndex parameter level) 1

/-- Retained-subtree nodes below its root and the unique spine nodes above it. -/
def KeptNode (parameter : PublicParameter) (level index : Nat) : Prop :=
  if level ≤ subtreeHeight then index / 2 ^ (subtreeHeight - level) = subtreePosition parameter
  else index = spineIndex parameter level

theorem boundary_not_kept (parameter : PublicParameter) (level : Nat)
    (hlevel : subtreeHeight ≤ level) : ¬KeptNode parameter level (boundaryIndex parameter level) := by
  unfold KeptNode
  by_cases heq : level = subtreeHeight
  · subst level
    simp only [le_refl, ↓reduceIte, Nat.sub_self, pow_zero, Nat.div_one,
      boundaryIndex, spineIndex]
    exact xor_one_ne _
  · rw [if_neg (by omega : ¬level ≤ subtreeHeight)]
    exact xor_one_ne _

/-- The actual outside-subtree witness hits the surrogate at its one off-spine node address. -/
theorem outside_subtree_addressed_witness (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed)
    (leaf reference : LeafIndex) (path : Nat → Digest) (value : Digest)
    (hb : 0 < subtreeHeight) (hreference : Landed parameter reference)
    (houtside : ¬Landed parameter leaf)
    (hfold : evalWithAnswerFn f (treeFold parameter lay tree leaf path totalHeight value :
      OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest)) :
    (∃ level, level < totalHeight ∧
      MerkleMatch f parameter (fun height index => .node lay tree height index)
        leaf.val reference.val path (canonicalTreePath f parameter lay tree seed reference)
        value (Completeness.node f parameter lay tree seed 0 reference.val) level) ∨
    ∃ level, level < totalHeight ∧
      SurrogatePreimage f parameter lay tree seed leaf path value level ∧
        leaf.val / 2 ^ level = boundaryIndex parameter level := by
  have hparent : leaf.val / 2 ^ totalHeight = reference.val / 2 ^ totalHeight := by
    have hl : leaf.val < 2 ^ totalHeight := leaf.isLt
    have hr : reference.val < 2 ^ totalHeight := reference.isLt
    rw [Nat.div_eq_of_lt hl, Nat.div_eq_of_lt hr]
  have hroot := canonicalTreePath_root f parameter lay tree seed reference hreference
  have hfold' : merkleValue f parameter (fun height index => .node lay tree height index)
      leaf.val path value totalHeight =
      merkleValue f parameter (fun height index => .node lay tree height index)
        reference.val (canonicalTreePath f parameter lay tree seed reference)
        (Completeness.node f parameter lay tree seed 0 reference.val) totalHeight := by
    rw [hroot, merkleValue, merkleFold_treeFold]
    exact hfold
  rcases merkleFold_classification f parameter (fun height index => .node lay tree height index)
    leaf.val reference.val path (canonicalTreePath f parameter lay tree seed reference)
    value (Completeness.node f parameter lay tree seed 0 reference.val) totalHeight hparent hfold'
    with hgood | ⟨level, hlevel, hparent, hbit, hcross⟩ | hmatch
  · have heq : leaf = reference := Fin.ext hgood.1
    exact False.elim (houtside (heq ▸ hreference))
  · have hlower : subtreeHeight ≤ level := by
      by_contra hnot
      have hle : level + 1 ≤ subtreeHeight := by omega
      have hquot := quotient_eq_above hle hparent
      apply houtside
      exact hquot.trans hreference
    have hpositive : 0 < level := lt_of_lt_of_le hb hlower
    refine Or.inr ⟨level, hlevel, ⟨hlower, hpositive, ?_⟩, ?_⟩
    · rw [← merkleValue_succ, Nat.sub_add_cancel (by omega : 1 ≤ level), hcross,
        canonicalTreePath_surrogate f parameter lay tree seed reference level hlower hlevel]
    · rw [quotient_eq_sibling hparent hbit, boundaryIndex, spineIndex]
      apply congrArg (fun value : Nat => Nat.xor value 1)
      have hsplit : level = subtreeHeight + (level - subtreeHeight) :=
        (Nat.add_sub_of_le hlower).symm
      rw [hsplit, Completeness.landed_div parameter reference hreference]
      simp only [Nat.add_sub_cancel_left]
  · exact Or.inl hmatch

end LeanSphincs.Security
