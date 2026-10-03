import LeanSphincs.SecurityReferenceSignature
import LeanSphincs.ForsCoverage

/-! The stopped hidden-row proof uses one hidden predecessor guess or one noncanonical
output match at a chain address. The older two-edge/contact extraction implies this simpler
event without a small-query assumption or an honest-signature premise. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Wots
open Concrete Chain

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
  (tree : TreeIndex) (leaf : LeafIndex) (reference : Encoding) (secret : ChainIndex → Digest)

def HiddenPredecessor (trace : List HashInput) : Prop :=
  ∃ (index : ChainIndex) (step : ChainStep), step.val < (reference index).val ∧
    tweakableHashInput parameter (.chain lay tree leaf index step)
      (bytesLE 16 (honestChain f parameter lay tree leaf index (secret index) step.val)) ∈ trace

def ChainOutputMatch (trace : List HashInput) : Prop :=
  ∃ (index : ChainIndex) (step : ChainStep) (payload : Digest),
    tweakableHashInput parameter (.chain lay tree leaf index step) (bytesLE 16 payload) ∈ trace ∧
    ChainHit f parameter lay tree leaf index (secret index) step.val step.isLt payload

theorem contact_hidden_or_output (trace : List HashInput) (index : ChainIndex)
    (h : Contact f parameter lay tree leaf index (reference index)
      (frontier f parameter lay tree leaf reference secret index) trace) :
    HiddenPredecessor f parameter lay tree leaf reference secret trace ∨
      ChainOutputMatch f parameter lay tree leaf secret trace := by
  obtain ⟨step, payload, hstep, htrace, hvalue⟩ := h
  by_cases heq : payload = honestChain f parameter lay tree leaf index (secret index) step.val
  · exact Or.inl ⟨index, step, by omega, heq ▸ htrace⟩
  · refine Or.inr ⟨index, step, payload, htrace, heq, ?_⟩
    simpa only [frontier, hstep] using hvalue

/-- Each old chain exceptional case exposes an actual hidden-input guess or a distinct-input
hit on the canonical next value. No probability estimate is used in this conversion. -/
theorem ChainException.hidden_or_output {trace : List HashInput}
    (h : ChainException f parameter lay tree leaf reference secret trace) :
    HiddenPredecessor f parameter lay tree leaf reference secret trace ∨
      ChainOutputMatch f parameter lay tree leaf secret trace := by
  rcases h with ⟨index, step, payload, _, htrace, hhit⟩ |
    ⟨index, first, second, payload, middle, _, hsecond, _, htrace, _, hvalue⟩ |
    ⟨left, right, _, hcontact, _⟩ | ⟨index, _, hcontact⟩
  · exact Or.inr ⟨index, step, payload, htrace, hhit⟩
  · exact contact_hidden_or_output f parameter lay tree leaf reference secret trace index
      ⟨second, middle, hsecond, htrace, hvalue⟩
  · exact contact_hidden_or_output f parameter lay tree leaf reference secret trace left hcontact
  · exact contact_hidden_or_output f parameter lay tree leaf reference secret trace index hcontact

end LeanSphincs.Security.Wots

namespace LeanSphincs.Security.Fors
open Concrete

def HiddenSecretQuery (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (revealed : Disclosures) (trace : List HashInput) : Prop :=
  ∃ (index : Index) (tree : FtsTree) (leaf : FtsLeaf), leaf ∉ revealed index tree ∧
    tweakableHashInput parameter (.ftsLeaf index tree leaf)
      (bytesLE 16 (Completeness.ftsSecret f parameter index tree leaf seed)) ∈ trace

/-- A canonical opening outside the disclosure coverage hashes an undisclosed canonical
secret during the actual verification. The disclosure table can depend on the whole past. -/
theorem Opening.covered_or_hidden (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (revealed : Disclosures) (trace : List HashInput)
    (hopening : Opening f parameter index seed leaves secrets paths)
    (hrun : ContainsRun f trace (ftsRecover parameter index leaves secrets paths)) :
    Covered revealed (index, leaves) ∨ HiddenSecretQuery f parameter seed revealed trace := by
  classical
  by_cases hcovered : Covered revealed (index, leaves)
  · exact Or.inl hcovered
  · have hmissing : ∃ tree, leaves tree ∉ revealed index tree := by
      simpa only [Covered, not_forall] using hcovered
    obtain ⟨tree, htree⟩ := hmissing
    exact Or.inr ⟨index, tree, leaves tree, htree, hrun _
      (Opening.trueSecretQuery f parameter index seed leaves secrets paths hopening tree)⟩

end LeanSphincs.Security.Fors

namespace LeanSphincs.Security.SignatureWitness
open Concrete
variable [Params]

/-- The unconditional signature classifier splits canonical forgeries into covered message
digests and actual queries of undisclosed FORS secrets. -/
theorem accepted_coverage_or_query (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (seed : MasterSeed) (message : Message) (signature : Signature) (revealed : Disclosures)
    (hb : 0 < subtreeHeight)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    (Landed pk.parameter (index f pk message signature) ∧
      Covered revealed (fullDigestView (verificationDigest f pk message signature))) ∨
    ChosenException f pk seed message signature ∨
    Fors.HiddenSecretQuery f pk.parameter seed revealed (trace f pk message signature) := by
  rcases accepted_chosen_classification f pk seed message signature hb hroot hverified with
    ⟨counter, _, hcanonical⟩ | hexception
  · rcases Fors.Opening.covered_or_hidden f pk.parameter (index f pk message signature) seed
        (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath
        revealed (trace f pk message signature) hcanonical.2.2.2.2
        (verification_fors_run f pk message signature) with hcovered | hhidden
    · exact Or.inl ⟨hcanonical.1, hcovered⟩
    · exact Or.inr (Or.inr hhidden)
  · exact Or.inr (Or.inl hexception)

end LeanSphincs.Security.SignatureWitness
