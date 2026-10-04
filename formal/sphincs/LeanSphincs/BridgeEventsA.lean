import LeanSphincs.BridgeExpose

/-! Events of the refined classification for small budgets. A cached answer that hits its target
is a first-order event unless its input is a root-tree chain step that is not at or above the
prepared word of a landed leaf, or a FORS leaf. Hits of those inputs become forgery events only
in pairs: a contact below the word together with an encoding marker or a second contact at the
same leaf, two consecutive edges into the frontier, a FORS leaf contact at a revealed leaf, a
contact completing a near cover of the forgery's digest, or two FORS contacts at one instance. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenBridge

open Concrete HiddenGraph

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section Events

variable (parameter : PublicParameter) (results : Index → Option (Counter × Encoding))
  (table : HiddenGraph.Table) (cache : QueryCache HashSpec)

/-- A root-tree chain input. -/
def chainInput (leaf : Index) (chain : ChainIndex) (step : ChainStep) (payload : Digest) : HashInput :=
  tweakableHashInput parameter (.chain topLayer rootTree leaf chain step) (bytesLE 16 payload)

/-- A FORS leaf input. -/
def forsLeafInput (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (secret : Digest) : HashInput :=
  tweakableHashInput parameter (.ftsLeaf index tree leaf) (bytesLE 16 secret)

/-- Inputs whose single hit is not a forgery event by itself: a root-tree chain step that is not
at or above the prepared word of a landed leaf, and a FORS leaf. -/
def SecondOrderInput (input : HashInput) : Prop :=
  (∃ leaf chain step payload, input = chainInput parameter leaf chain step payload ∧
    ¬(Landed parameter leaf ∧ (preparedWord results leaf chain).val ≤ step.val)) ∨
  ∃ index tree leaf secret, input = forsLeafInput parameter index tree leaf secret

/-- First-order targets. -/
noncomputable def targetsA (tab : TargetAssignment.Table) (input : HashInput) : Finset Digest :=
  if SecondOrderInput parameter results input then ∅ else TargetAssignment.targets parameter tab input

/-- The table value at a chain position. -/
def chainValue (leaf : Index) (chain : ChainIndex) (position : Digit) : Digest :=
  table (.chain topLayer rootTree leaf chain position)

/-- The table value at the prepared word: the frontier. -/
noncomputable def frontierValue (leaf : Index) (chain : ChainIndex) : Digest :=
  chainValue table leaf chain (preparedWord results leaf chain)

/-- A cached step just below the word, from a non-canonical payload, reaches the frontier. -/
def ContactAt (leaf : Index) (chain : ChainIndex) : Prop :=
  ∃ (step : ChainStep) (payload : Digest) (answer : HashOutput),
    step.val + 1 = (preparedWord results leaf chain).val ∧
    payload ≠ chainValue table leaf chain ⟨step.val, by have := step.isLt; omega⟩ ∧
    cache (chainInput parameter leaf chain step payload) = some answer ∧
    truncateHash answer = frontierValue results table leaf chain

/-- Two cached consecutive steps below the word reach the frontier. -/
def TwoEdgeAt (leaf : Index) (chain : ChainIndex) : Prop :=
  ∃ (first second : ChainStep) (payload : Digest) (answer answer' : HashOutput),
    first.val + 1 = second.val ∧ second.val + 1 = (preparedWord results leaf chain).val ∧
    cache (chainInput parameter leaf chain first payload) = some answer ∧
    cache (chainInput parameter leaf chain second (truncateHash answer)) = some answer' ∧
    truncateHash answer' = frontierValue results table leaf chain

/-- A cached encoding answer of the leaf decodes to a unit neighbour lowering the chain. -/
def MarkerAt (leaf : Index) (chain : ChainIndex) : Prop :=
  ∃ (message : Digest) (counter : Counter) (answer : HashOutput) (candidate : Encoding),
    cache (Wots.encodingInput parameter topLayer rootTree leaf message counter) = some answer ∧
    TargetSum.decodeDigest (truncateHash answer) = some candidate ∧
    EncodingCode.UnitNeighborAt (preparedWord results leaf) candidate chain

/-- The WOTS events of a landed leaf. -/
def WotsEventAt (leaf : Index) : Prop :=
  (∃ chain, TwoEdgeAt parameter results table cache leaf chain) ∨
  (∃ chain, ContactAt parameter results table cache leaf chain ∧ MarkerAt parameter results cache leaf chain) ∨
  ∃ chain chain', chain ≠ chain' ∧ ContactAt parameter results table cache leaf chain ∧
    ContactAt parameter results table cache leaf chain'

def WotsEvent : Prop := ∃ leaf, Landed parameter leaf ∧ WotsEventAt parameter results table cache leaf

/-- A cached FORS leaf answer from a non-canonical secret equals the canonical leaf value. -/
def FContactAt (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : Prop :=
  ∃ (secret : Digest) (answer : HashOutput), secret ≠ table (.ftsSecret index tree leaf) ∧
    cache (forsLeafInput parameter index tree leaf secret) = some answer ∧
    truncateHash answer = table (.ftsValue index tree leaf)

/-- A FORS contact at a revealed leaf. -/
def RevealedContact (reveals : List Coordinate) : Prop :=
  ∃ index tree leaf, leaf ∈ revealedSet reveals index tree ∧ FContactAt parameter table cache index tree leaf

/-- Two FORS contacts at different trees of one instance. -/
def TwoForsContacts : Prop :=
  ∃ index tree tree' leaf leaf', tree ≠ tree' ∧ FContactAt parameter table cache index tree leaf ∧
    FContactAt parameter table cache index tree' leaf'

/-- A cached, landed, unsigned forgery digest covered at every tree but one, whose leaf there is
contacted. -/
def ForsNear (root : Digest) (outcome : Outcome) (reveals : List Coordinate) : Prop :=
  SigningTranscript.Valid outcome.2.1 ∧
  ∃ digest, cachedDigest cache parameter root outcome.1.message outcome.1.signature.randomness = some digest ∧
    Landed parameter (digestIndex digest) ∧
    (∀ entry ∈ outcome.2.1, ∀ signature, entry.2 = some signature →
      ¬(entry.1 = outcome.1.message ∧ signature.randomness = outcome.1.signature.randomness)) ∧
    ∃ tree, FContactAt parameter table cache (digestIndex digest) tree (digestLeaves digest tree) ∧
      ∀ other, other ≠ tree → digestLeaves digest other ∈ revealedSet reveals (digestIndex digest) other

end Events

/-- The refined bad event of one table. -/
def badA (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (HiddenCost.Entry HashInput)) × QueryCache HashSpec) :
    Prop :=
  CacheMatch.Bad (targetsA (truncateHash parameterOutput) results
      (compTable parameterOutput fixed highs remaining table results)) v.2 ∨
    WotsEvent (truncateHash parameterOutput) results table v.2 ∨
    RevealedContact (truncateHash parameterOutput) table v.2 v.1.1.2 ∨
    TwoForsContacts (truncateHash parameterOutput) table v.2 ∨
    ∃ outcome, v.1.1.1 = some outcome ∧
      (ForsNear (truncateHash parameterOutput) table v.2 (sampleData parameterOutput fixed highs remaining).root
          outcome v.1.1.2 ∨
        ForsCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
          outcome v.1.1.2 v.2)

end LeanSphincs.Security.HiddenBridge
