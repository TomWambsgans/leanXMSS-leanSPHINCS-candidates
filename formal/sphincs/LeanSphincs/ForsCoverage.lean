import LeanSphincs.Uniform
import Mathlib.Data.BitVec

/-!
Exact FORS coverage for a fresh uniform 266-bit digest. These are probability identities for a
fixed disclosure table, not a bound on an adaptive SUF-CMA adversary. The latter must justify when
this fresh-digest law applies and bound the distribution of the disclosure table.
The bit-decomposition argument is adapted from leanVM b7a107256 for 24 unpinned trees.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000
set_option exponentiation.threshold 512

namespace LeanSphincs.Concrete

abbrev FullDigestView := Index × (IndexGroup → FtsLeaf)

def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, digestLeaves digest)

theorem fullDigestView_injective : Function.Injective fullDigestView := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hindex : position < totalHeight
  · have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin view.1) heq
    have hbit := congrArg (fun bits : BitVec totalHeight => bits.getLsbD position) hcomponent
    simpa [fullDigestView, digestIndex, BitVec.getLsbD_extractLsb', hindex] using hbit
  · let treeIndex := (position - totalHeight) / ftsTreeHeight
    have htreeIndex : treeIndex < ftsTrees := by
      have hposition' : position < 266 := by
        simpa [messageDigestBits, totalHeight, ftsTrees, ftsTreeHeight] using hposition
      have hindex' : 26 ≤ position := by
        simpa [totalHeight] using Nat.le_of_not_gt hindex
      simp only [treeIndex, ftsTrees, ftsTreeHeight, totalHeight]
      omega
    let tree : IndexGroup := ⟨treeIndex, htreeIndex⟩
    let within := (position - totalHeight) % ftsTreeHeight
    have hwithin : within < ftsTreeHeight := by
      simp only [within, ftsTreeHeight]
      omega
    have hoffset : totalHeight + ftsTreeHeight * tree.val + within = position := by
      have hindex' : totalHeight ≤ position := Nat.le_of_not_gt hindex
      simp only [tree, treeIndex, within]
      calc
        totalHeight + ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight) +
            (position - totalHeight) % ftsTreeHeight =
            totalHeight + ((position - totalHeight) % ftsTreeHeight +
              ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight)) := by omega
        _ = totalHeight + (position - totalHeight) := by rw [Nat.mod_add_div]
        _ = position := Nat.add_sub_of_le hindex'
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin (view.2 tree)) heq
    change left.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight =
      right.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight at hcomponent
    have hbit := congrArg (fun bits : BitVec ftsTreeHeight => bits.getLsbD within) hcomponent
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

/-- The leaves disclosed by signatures at each FORS instance. Sets count distinct openings. -/
abbrev Disclosures := Index → FtsTree → Finset FtsLeaf

def Covered (revealed : Disclosures) (view : FullDigestView) : Prop :=
  ∀ tree : FtsTree, view.2 tree ∈ revealed view.1 tree

instance (revealed : Disclosures) : DecidablePred (Covered revealed) :=
  fun view => inferInstanceAs (Decidable (∀ tree : FtsTree, view.2 tree ∈ revealed view.1 tree))

/-- Enumerating covered digests is choosing an index, then one disclosed leaf per tree. -/
def coveredEquiv (revealed : Disclosures) :
    (Σ index : Index, (tree : FtsTree) → {leaf : FtsLeaf // leaf ∈ revealed index tree}) ≃
      {view : FullDigestView // Covered revealed view} where
  toFun choice := ⟨(choice.1, fun tree => (choice.2 tree).val), fun tree => (choice.2 tree).property⟩
  invFun view := ⟨view.val.1, fun tree => ⟨view.val.2 tree, view.property tree⟩⟩
  left_inv := by rintro ⟨index, leaves⟩; rfl
  right_inv := by rintro ⟨⟨index, leaves⟩, h⟩; rfl

/-- Exact coverage numerator: sum over indices of the product of DISTINCT leaf counts. -/
theorem covered_card (revealed : Disclosures) :
    (Finset.univ.filter (Covered revealed)).card =
      ∑ index : Index, ∏ tree : FtsTree, (revealed index tree).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_congr (coveredEquiv revealed), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro index _
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro tree _
  simp

/-- For a fresh uniform digest, full FORS reuse has exactly this probability. -/
theorem fresh_fors_coverage (revealed : Disclosures) :
    Pr[fun digest => Covered revealed (fullDigestView digest) |
      ($ᵗ MessageDigest : ProbComp MessageDigest)] =
      ((∑ index : Index, ∏ tree : FtsTree, (revealed index tree).card : Nat) : ℝ≥0∞) /
        ((2 ^ 266 : Nat) : ℝ≥0∞) := by
  rw [show (fun digest => Covered revealed (fullDigestView digest)) =
    (Covered revealed) ∘ fullDigestView from rfl, ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_fullDigestView_uniform,
    probEvent_uniformSample, covered_card]
  have hcard : Fintype.card FullDigestView = 2 ^ 266 := by
    rw [← Fintype.card_congr (Equiv.ofBijective fullDigestView fullDigestView_bijective)]
    simp [messageDigestBits, totalHeight, ftsTrees, ftsTreeHeight]
  rw [hcard]

end LeanSphincs.Concrete
