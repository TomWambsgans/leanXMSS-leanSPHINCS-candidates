import LeanSphincs.Landing
import LeanSphincs.SecurityDigest

/-!
The exact conditional law of a fresh digest that lands in a pruned subtree. Conditioning on
the landing test leaves the local index and all 24 FORS selectors jointly uniform. This lemma
concerns a fresh digest trial; relating a whole grinding loop to these trials is separate.
-/

namespace LeanSphincs.Lifetime

set_option exponentiation.threshold 512

open OracleComp OracleSpec ENNReal Concrete

variable [Params]

abbrev KeptDigestView := Fin (2 ^ subtreeHeight) × (IndexGroup → FtsLeaf)

/-- The local index and the 24 FORS coordinates, defined even for a rejected global index. -/
def localFullView (view : FullDigestView) : KeptDigestView :=
  (⟨view.1.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, view.2)

def keptViewEquiv (parameter : PublicParameter) :
    KeptDigestView ≃ {view : FullDigestView // Landed parameter view.1} where
  toFun view := ⟨((keptLeafEquiv parameter view.1).val, view.2),
    (keptLeafEquiv parameter view.1).property⟩
  invFun view := localFullView view.val
  left_inv view := by
    apply Prod.ext
    · exact (keptLeafEquiv parameter).left_inv view.1
    · rfl
  right_inv view := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((keptLeafEquiv parameter).right_inv ⟨view.val.1, view.property⟩)
    · rfl

theorem local_keptView (parameter : PublicParameter) (view : KeptDigestView) :
    localFullView (keptViewEquiv parameter view).val = view :=
  (keptViewEquiv parameter).left_inv view

def keptFilteredEquiv (parameter : PublicParameter) (P : KeptDigestView → Prop) :
    {view : KeptDigestView // P view} ≃
      {view : FullDigestView // Landed parameter view.1 ∧ P (localFullView view)} where
  toFun view := ⟨(keptViewEquiv parameter view.val).val,
    (keptViewEquiv parameter view.val).property, by simpa only [local_keptView] using view.property⟩
  invFun view := ⟨localFullView view.val, view.property.2⟩
  left_inv view := by apply Subtype.ext; exact local_keptView parameter view.val
  right_inv view := by
    exact Subtype.ext (congrArg
      (fun v : {view : FullDigestView // Landed parameter view.1} => v.val)
      ((keptViewEquiv parameter).right_inv ⟨view.val, view.property.1⟩))

theorem fullDigestView_card_factor :
    Fintype.card FullDigestView = 2 ^ (totalHeight - subtreeHeight) *
      Fintype.card KeptDigestView := by
  simp only [FullDigestView, KeptDigestView, Fintype.card_prod, Fintype.card_fin,
    mul_assoc, ← subtree_size_mul]

def localDigestView (digest : MessageDigest) : KeptDigestView :=
  localFullView (fullDigestView digest)

/-- Joint event factorization: acceptance only costs the reciprocal number of subtrees. -/
theorem probEvent_landed_localDigest (parameter : PublicParameter)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[fun digest => Landed parameter (digestIndex digest) ∧ P (localDigestView digest) |
      ($ᵗ MessageDigest : ProbComp MessageDigest)] =
        ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
          Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  change Pr[(fun view : FullDigestView => Landed parameter view.1 ∧ P (localFullView view)) ∘
    fullDigestView | _] = _
  rw [← probEvent_map, probEvent_congr' (fun _ _ => Iff.rfl) evalDist_fullDigestView_uniform]
  rw [probEvent_uniformSample, probEvent_uniformSample, ← Fintype.card_subtype,
    ← Fintype.card_subtype, ← Fintype.card_congr (keptFilteredEquiv parameter P),
    fullDigestView_card_factor, Nat.cast_mul]
  simp only [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  ring

theorem probEvent_fullDigest_landed (parameter : PublicParameter) :
    Pr[fun digest => Landed parameter (digestIndex digest) |
      ($ᵗ MessageDigest : ProbComp MessageDigest)] =
        ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ := by
  simpa only [and_true, probEvent_True_eq_sub, probFailure_uniformSample, tsub_zero, mul_one]
    using probEvent_landed_localDigest parameter (fun _ => True)

/-- Conditional on acceptance, the kept index and all FORS coordinates have uniform product law. -/
theorem conditional_landed_digest_uniform (parameter : PublicParameter)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[fun digest => Landed parameter (digestIndex digest) ∧ P (localDigestView digest) |
      ($ᵗ MessageDigest : ProbComp MessageDigest)] /
        Pr[fun digest => Landed parameter (digestIndex digest) |
          ($ᵗ MessageDigest : ProbComp MessageDigest)] =
      Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  rw [probEvent_landed_localDigest, probEvent_fullDigest_landed]
  rw [div_eq_mul_inv, mul_comm _ (Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)]),
    mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

/-- The same joint law for the actual pair of fresh, separately tweaked hash calls. -/
theorem probEvent_messageDigest_landed_local (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec)
    (hfresh : Security.DigestFresh parameter root message randomness cache)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[fun result => Landed parameter (digestIndex result.1) ∧ P (localDigestView result.1) |
      (simulateQ randomOracle
        (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache] =
      ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  change Pr[(fun digest => Landed parameter (digestIndex digest) ∧ P (localDigestView digest)) ∘
    Prod.fst | _] = _
  rw [← probEvent_map, probEvent_congr' (fun _ _ => Iff.rfl)
    (Security.evalDist_messageDigest_fresh parameter root message randomness cache hfresh)]
  exact probEvent_landed_localDigest parameter P

end LeanSphincs.Lifetime
