import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.BoundaryHashEvaluation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk

def referenceEncodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) :
    Nat → Nat → Option (Counter × Encoding) × Nat
  | 0, _ => (none, 0)
  | attempts + 1, counter =>
      match evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | some word => (some (BitVec.ofNat counterBits counter, word), 1)
      | none =>
          let rest := referenceEncodingSearch parameter f lay tree leaf message attempts (counter + 1)
          (rest.1, 1 + rest.2)

theorem boundaryEval_encode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    boundaryEval parameter f (encodeAttempt parameter lay tree leaf message counter) =
      (evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter), FreeMonoid.of none) := by
  apply boundaryEval_eq_of_snd
  rw [encodeAttempt, boundaryEval_bind,
    boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields]), boundaryEval_pure, mul_one]

theorem boundaryEval_otsValues (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) (word : Encoding) :
    boundaryEval parameter f (sequenceFin fun chainIdx =>
      chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) =
      (fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)),
        (FreeMonoid.of none) ^ OtsCode.signingSteps word) := by
  have h := boundaryEval_sequenceFin parameter f
    (fun chainIdx => chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx))
    (fun chainIdx => (word chainIdx).val) (fun chainIdx => by
      apply congrArg Prod.snd (boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ ?_)
      have hdigit := (word chainIdx).isLt
      omega)
  simpa only [OtsCode.signingSteps] using h

theorem boundaryEval_otsSignFrom_frontier (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret frontier : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat)
    (hfrontier : ∀ c word,
      (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1 = some (c, word) →
      ∀ chainIdx, evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) = frontier chainIdx) :
    boundaryEval parameter f (otsSignFrom parameter lay tree leaf secret message attempts counter) =
      ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).1.map
          (fun result => (result.1, frontier)),
        (FreeMonoid.of none) ^ ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).2 +
          (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1.elim 0
            (fun result => OtsCode.signingSteps result.2))) := by
  induction attempts generalizing counter with
  | zero => simp [otsSignFrom, referenceEncodingSearch]
  | succ attempts ih =>
      rw [otsSignFrom, boundaryEval_bind, boundaryEval_encode]
      cases hencode : evalWithAnswerFn f
          (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | none =>
          have ht : ∀ c word,
              (referenceEncodingSearch parameter f lay tree leaf message attempts (counter + 1)).1 = some (c, word) →
              ∀ chainIdx, evalWithAnswerFn f
                (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) = frontier chainIdx := by
            intro c word hw
            apply hfrontier c word
            simpa only [referenceEncodingSearch, hencode] using hw
          rw [ih (counter + 1) ht]
          simp only [referenceEncodingSearch, hencode, Nat.add_assoc, pow_add, pow_one]
      | some word =>
          have hv : (fun chainIdx => evalWithAnswerFn f
              (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx))) = frontier := by
            funext chainIdx
            exact hfrontier (BitVec.ofNat counterBits counter) word
              (by simp only [referenceEncodingSearch, hencode]) chainIdx
          rw [boundaryEval_bind, boundaryEval_otsValues]
          simp only [boundaryEval_pure, evalWithAnswerFn_sequenceFin, hv, mul_one,
            referenceEncodingSearch, hencode, Option.map_some, Option.elim_some, pow_add, pow_one]

end SphincsSecurity.Concrete
