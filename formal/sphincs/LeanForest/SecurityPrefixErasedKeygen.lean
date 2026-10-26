import LeanForest.SecurityPrefixCountedSign
import LeanForest.SecuritySeedCoupling

/-! The exact hash cost of key generation: the top layer's kept subtree and its surrogate spine,
`226 · 2^k + 2 (h_top - k)` calls with `k = keptHeight topLayer` (`226 · 2^b + 2 (h - b)` for one
layer, `226 · 2^h_top` for a layered key). -/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix

variable [Params]
open Concrete Completeness SeedModel

attribute [local irreducible] Seeded.treeNode Seeded.spineNode Seeded.treeRoot
  programCache
set_option backward.isDefEq.respectTransparency false


theorem hashCalls_spineNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (steps : Nat)
    (hsteps : steps ≤ layerHeight lay - keptHeight lay) :
    hashCalls f (Seeded.spineNode parameter lay tree seed steps : OracleComp HashSpec Digest) =
      (226 * 2 ^ keptHeight lay - 1) + 2 * steps := by
  induction steps with
  | zero => simp only [Seeded.spineNode, hashCalls_treeNode, Nat.mul_zero, Nat.add_zero]
  | succ steps ih =>
      have hkl := Completeness.keptHeight_le lay
      have hll := layerHeight_le lay
      have hlevel : keptHeight lay + steps < maxLayerHeight := by omega
      rw [Seeded.spineNode, hashCalls_bind, ih (by omega), hashCalls_bind]
      simp only [Seeded.surrogate, dif_pos hlevel, hashCalls_deriveKey]
      split <;> rw [hashCalls_tweakableHash] <;> omega

/-- The cost of a layer's tree root: its kept part and its spine. -/
theorem hashCalls_treeRoot (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) =
      (226 * 2 ^ keptHeight lay - 1) + 2 * (layerHeight lay - keptHeight lay) := by
  rw [Seeded.treeRoot, hashCalls_spineNode f _ _ _ seed _ (le_refl _)]

/-- The hash calls of key generation: the parameter, the top layer's kept subtree and its surrogate
spine. -/
def keygenHashCost : Nat := 226 * 2 ^ keptHeight topLayer + 2 * (layerHeight topLayer - keptHeight topLayer)

theorem hashCalls_keygenFromSeed (f : QueryImpl HashSpec Id) (seed : MasterSeed) :
    hashCalls f (Seeded.keygenFromSeed seed) = keygenHashCost := by
  unfold keygenHashCost
  simp only [Seeded.keygenFromSeed, hashCalls_bind, hashCalls_deriveKey, hashCalls_treeRoot,
    hashCalls_pure, Nat.add_zero]
  have := Nat.two_pow_pos (keptHeight topLayer)
  omega

end LeanForest.Security.Prefix
