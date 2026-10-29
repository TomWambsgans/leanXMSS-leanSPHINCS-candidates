import FORS.SWRoute.ContactStep
import FORS.SmallBudget.Contact.Signing

/-! **The contact potential through a signing call** (`goodK_sign`, the obligation `hsign` of
`goodK_advProg`). With one digest call per pair and `M = 1` every trial lands, so a call draws a
uniform start, reads the start's pair (fresh or cached) and runs the final assembly of that pair:
the WOTS searches (ordinary queries that neither query a FORS leaf input nor a fresh digest block),
the chain reveals and the FORS reveals. A kill of the call (a decided FORS contact becoming a
completed one) happens only

* at the read of a fresh pair whose view opens the contact's cell (chance at most `revRate`), or
* in the final reveal phase. There `weightB` keeps its mean exactly and the kill is decided by the
  revealed coordinate, so the kills of that phase are paid by `weightB` at the end of the call on the
  runs that end with a completed contact (`lk_bound`, `ro_bound`).

A run that opens the contact's cell (its pair selects the cell; chance at most `revRate` plus `cinv`
per cached pair of the message at the cell) is paid by the drop of `sigRiskF` and of the cell
count. Any other completed contact is a near completion at the cell by an unsigned cached pair, so
the own-cell forecast `PiC` after the call is at least one (`sgn_release`), and it is paid by
`min 1 PiC` through the weighted signing step of the generic potential with the weight `weightB`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Completed contacts and the state -/

section Transfer

variable (K : Ctx) (root : Digest)

/-- A FORS secret coordinate. -/
def IsSecretC (c : Coordinate) : Prop := ∃ i κ l, c = Coordinate.fors i κ l 0

/-- A completed contact needs a cached FORS leaf answer, a cached digest and known FORS secrets:
it transfers to a state with the same such entries. -/
theorem nc_of_agree {s s' : State}
    (hc : ∀ x, (HiddenBridge.IsFleafIn K.p x ∨ IsMsgInput x) → s'.cache x = s.cache x)
    (hk : ∀ i κ l, s'.known (Coordinate.fors i κ l 0) ≠ none → s.known (Coordinate.fors i κ l 0) ≠ none)
    (h : NearContact K root s') : NearContact K root s := by
  obtain ⟨f, ⟨u, ⟨hfu, hfi⟩, ht⟩, hor⟩ := h
  have hfc : FCk K s f := ⟨u, ⟨by rw [← hc _ (Or.inl ⟨f, rfl⟩)]; exact hfu, hfi⟩, ht⟩
  refine ⟨f, hfc, ?_⟩
  rcases hor with hkn | ⟨m', ρ', dg, hcd, hl, hi, hlf, hok⟩
  · exact Or.inl (hk _ _ _ hkn)
  · refine Or.inr ⟨m', ρ', dg, ?_, hl, hi, hlf, fun κ' hκ' => hk _ _ _ (hok κ' hκ')⟩
    have hsame : HiddenBridge.cachedDigest s'.cache K.p root m' ρ' = HiddenBridge.cachedDigest s.cache K.p root m' ρ' := by
      unfold HiddenBridge.cachedDigest
      congr 2
      funext call
      exact hc _ (Or.inr ⟨K.p, call, _, rfl⟩)
    rw [← hsame]
    exact hcd

/-- Whether an exposure completes a contact does not depend on the exposed value. -/
theorem nc_expose_iff (s : State) (c : Coordinate) (v v' : Digest) :
    NearContact K root (s.expose c v) ↔ NearContact K root (s.expose c v') := by
  have hk : ∀ (w w' : Digest) (y : Coordinate), (s.expose c w).known y ≠ none → (s.expose c w').known y ≠ none := by
    intro w w' y h
    by_cases hy : y = c
    · subst hy
      simp [DebtState.expose, QueryCache.cacheQuery]
    · simpa [DebtState.expose, QueryCache.cacheQuery, hy] using h
  exact ⟨nc_of_agree K root (fun _ _ => rfl) (fun i κ l => hk v v' _),
    nc_of_agree K root (fun _ _ => rfl) (fun i κ l => hk v' v _)⟩

/-- A FORS contact of the state after a step that queries no FORS leaf input was a contact before. -/
theorem fck_of_step {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (input : CostSpec.Domain) (s : State)
    (hin : ∀ x, input = .inl (.inr (.inl x)) → ¬HiddenBridge.IsFleafIn K.p x)
    (r : CostSpec.Range input × State) (hr : r ∈ support (costStep model input s)) (f : FIn)
    (h : FCk K r.2 f) : FCk K s f := by
  obtain ⟨u, ⟨hfu, hfi⟩, ht⟩ := h
  refine ⟨u, ⟨?_, hfi⟩, ht⟩
  rcases input with (draw | (bytes | coordinate)) | amount
  · change r ∈ support ((fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hr
    rw [support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact hfu
  · rw [costStep_ordinary] at hr
    rw [← ordinaryStep_cache_ne model bytes s r hr _ (fun heq => hin bytes rfl ⟨f, heq.symm⟩)]
    exact hfu
  · change r ∈ support (sampleCoordinate coordinate s) at hr
    rw [sampleCoordinate_expose _ s r hr] at hfu
    exact hfu
  · change r ∈ support (pure ((), s) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hfu
    exact hfu

end Transfer

/-! ### The kill account: vanishing cases -/

section Zero

variable (K : Ctx) (root : Digest) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- Once a contact is completed, nothing is killed any more. -/
theorem acct_payK_of_nc {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : State), NearContact K root s → acct model (payK K root) comp budget s = 0 := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s _; rfl
  | query_bind input next ih =>
      intro budget s hN
      rw [acct_query_bind]
      split_ifs
      · refine ENNReal.tsum_eq_zero.2 fun r => ?_
        by_cases hr : r ∈ support (costStep model input s)
        · have hN' := nearContact_mono (extends_costStep model input s r hr) hN
          rw [ih r.1 _ r.2 hN', add_zero]
          simp [payK, hN]
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
      · rfl

/-- With zero weight nothing is paid. -/
theorem acct_payK_of_weightA {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : State), weightA K root s = 0 → acct model (payK K root) comp budget s = 0 := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s _; rfl
  | query_bind input next ih =>
      intro budget s hw
      rw [acct_query_bind]
      split_ifs
      · have hstep := weightA_step_le K root model input s
        rw [hw, nonpos_iff_eq_zero, ENNReal.tsum_eq_zero] at hstep
        refine ENNReal.tsum_eq_zero.2 fun r => ?_
        by_cases hr : r ∈ support (costStep model input s)
        · have hpos : Pr[= r | costStep model input s] ≠ 0 := ((probOutput_pos_iff _ _).2 hr).ne'
          have hw' : weightA K root r.2 = 0 := (mul_eq_zero.1 (hstep r)).resolve_left hpos
          rw [ih r.1 _ r.2 hw', add_zero]
          have hp : payK K root s input r.2 = 0 := by
            unfold payK; split_ifs <;> simp [hw]
          rw [hp, mul_zero]
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
      · rfl

/-- Without a decided FORS contact, a run that queries no FORS leaf input kills nothing. -/
theorem acct_payK_of_noFC {α : Type} (comp : OracleComp CostSpec α)
    (hav : Avoids (HiddenBridge.IsFleafIn K.p) comp) :
    ∀ budget (s : State), (∀ f, ¬FCk K s f) → acct model (payK K root) comp budget s = 0 := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s _; rfl
  | query_bind input next ih =>
      intro budget s hno
      obtain ⟨hin, hnext⟩ := (avoids_query_bind _ input next).1 hav
      rw [acct_query_bind]
      split_ifs
      · refine ENNReal.tsum_eq_zero.2 fun r => ?_
        by_cases hr : r ∈ support (costStep model input s)
        · have hno' : ∀ f, ¬FCk K r.2 f := fun f hf =>
            hno f (fck_of_step K model input s hin r hr f hf)
          rw [ih r.1 (hnext r.1) _ r.2 hno', add_zero]
          have hp : payK K root s input r.2 = 0 := by
            unfold payK
            rw [if_neg]
            rintro ⟨-, ⟨f, hf, -⟩, -⟩
            exact hno' f hf
          rw [hp, mul_zero]
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
      · rfl

end Zero


/-! ### Reveal-only computations and computations that kill late -/

section Phases

/-- **Reveal-only computations**: every query is a reveal. -/
def RevealOnly {α : Type} (comp : OracleComp CostSpec α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next => (∃ c, input = .inl (.inr (.inr c))) ∧ ∀ value, next value) comp

theorem revealOnly_pure {α : Type} (value : α) : RevealOnly (pure value : OracleComp CostSpec α) := trivial

theorem revealOnly_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) :
    RevealOnly (liftM (CostSpec.query input) >>= next) ↔
      (∃ c, input = .inl (.inr (.inr c))) ∧ ∀ value, RevealOnly (next value) := Iff.rfl

theorem revealOnly_bind {α β : Type} {first : OracleComp CostSpec α} {next : α → OracleComp CostSpec β}
    (h1 : RevealOnly first) (h2 : ∀ value, RevealOnly (next value)) : RevealOnly (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using h2 value
  | query_bind input rest ih =>
      rw [bind_assoc, revealOnly_query_bind]
      obtain ⟨hin, hrest⟩ := (revealOnly_query_bind input rest).1 h1
      exact ⟨hin, fun value => ih value (hrest value)⟩

theorem revealOnly_reveal (c : Coordinate) :
    RevealOnly (HiddenCost.reveal (D := HashInput) (R := HashOutput) c) := by
  unfold HiddenCost.reveal
  rw [← bind_pure (liftM ((SourceCostSpec HashInput HashOutput Coordinate).query (.inl (.inr (.inr c)))))]
  exact (revealOnly_query_bind _ _).2 ⟨⟨c, rfl⟩, fun _ => trivial⟩

theorem revealOnly_sequenceFin {α : Type} : ∀ {n : ℕ} (comp : Fin n → OracleComp CostSpec α),
    (∀ i, RevealOnly (comp i)) → RevealOnly (Concrete.sequenceFin comp)
  | 0, _, _ => revealOnly_pure _
  | n + 1, comp, h => by
      unfold Concrete.sequenceFin
      exact revealOnly_bind (h 0) fun _ =>
        revealOnly_bind (revealOnly_sequenceFin (fun i : Fin n => comp i.succ) fun i => h i.succ)
          fun _ => revealOnly_pure _

theorem revealOnly_treeCostSource (data : PublicData) (index : Index) (κ : FTree) (leaf : FLeaf) :
    RevealOnly (treeCostSource data index κ leaf) := by
  unfold treeCostSource
  exact revealOnly_bind (revealOnly_sequenceFin _ fun _ => revealOnly_reveal _) fun _ => revealOnly_pure _

/-- **Computations that kill late**: a prefix that reveals no FORS secret, then a reveal-only
rest. -/
def LateKill {α : Type} (comp : OracleComp CostSpec α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input cont next => ((∀ c, input = .inl (.inr (.inr c)) → ¬IsSecretC c) ∧ ∀ value, next value) ∨
      ((∃ c, input = .inl (.inr (.inr c))) ∧ ∀ value, RevealOnly (cont value))) comp

theorem lateKill_pure {α : Type} (value : α) : LateKill (pure value : OracleComp CostSpec α) := trivial

theorem lateKill_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) :
    LateKill (liftM (CostSpec.query input) >>= next) ↔
      ((∀ c, input = .inl (.inr (.inr c)) → ¬IsSecretC c) ∧ ∀ value, LateKill (next value)) ∨
        ((∃ c, input = .inl (.inr (.inr c))) ∧ ∀ value, RevealOnly (next value)) := Iff.rfl

theorem lateKill_of_revealOnly {α : Type} {comp : OracleComp CostSpec α} (h : RevealOnly comp) : LateKill comp := by
  induction comp using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind input next ih =>
      obtain ⟨hin, hnext⟩ := (revealOnly_query_bind input next).1 h
      exact (lateKill_query_bind input next).2 (Or.inr ⟨hin, hnext⟩)

theorem lateKill_bind_nk {α β : Type} {first : OracleComp CostSpec α} {next : α → OracleComp CostSpec β}
    (h1 : RevealsIn (D := HashInput) (R := HashOutput) (fun c => ¬IsSecretC c) first)
    (h2 : ∀ value, LateKill (next value)) : LateKill (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using h2 value
  | query_bind input rest ih =>
      rw [bind_assoc, lateKill_query_bind]
      obtain ⟨hin, hrest⟩ := (revealsIn_query_bind _ input rest).1 h1
      exact Or.inl ⟨hin, fun value => ih value (hrest value)⟩

theorem revealsIn_read (allowed : Coordinate → Prop) (y : HashInput) :
    RevealsIn (D := HashInput) (R := HashOutput) allowed
      (liftM (CostSpec.query (.inl (.inr (.inl y)))) : OracleComp CostSpec HashOutput) := by
  rw [← bind_pure (liftM (CostSpec.query (.inl (.inr (.inl y)))) : OracleComp CostSpec HashOutput)]
  exact (revealsIn_query_bind allowed _ _).2 ⟨fun c h => (by cases h), fun _ => trivial⟩

/-- The final assembly after its digest kills late: its searches reveal nothing, then it only
reveals. -/
theorem lateKill_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    LateKill (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine lateKill_bind_nk (revealsIn_tick _ _) fun _ => ?_
  refine lateKill_bind_nk (revealsIn_sequenceDep _ fun lay => revealsIn_layerCostSearch _ _ _ _ lay)
    fun found => ?_
  rcases found with _ | found
  · exact lateKill_pure _
  · refine lateKill_of_revealOnly (revealOnly_bind (revealOnly_sequenceFin _ fun _ =>
      revealOnly_sequenceFin _ fun _ => revealOnly_reveal _) fun _ => ?_)
    exact revealOnly_bind (revealOnly_sequenceFin _ fun _ => revealOnly_treeCostSource _ _ _ _) fun _ =>
      revealOnly_pure _

theorem lateKill_finishCost (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) : LateKill (finishCostSource parameter data message randomness) := by
  rw [finishCostSource_eq]
  exact lateKill_bind_nk (revealsIn_sequenceFin _ _ fun _ => revealsIn_read _ _) fun _ =>
    lateKill_finishRest _ _ _ _ _

theorem avoids_or {avoid avoid' : HashInput → Prop} {α : Type} {comp : OracleComp CostSpec α}
    (h : Avoids avoid comp) (h' : Avoids avoid' comp) : Avoids (fun x => avoid x ∨ avoid' x) comp := by
  induction comp using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind input next ih =>
      obtain ⟨hin, hnext⟩ := (avoids_query_bind avoid input next).1 h
      obtain ⟨hin', hnext'⟩ := (avoids_query_bind avoid' input next).1 h'
      exact (avoids_query_bind _ input next).2
        ⟨fun bytes hb hor => hor.elim (hin bytes hb) (hin' bytes hb), fun v => ih v (hnext v) (hnext' v)⟩

end Phases

/-! ### Kills paid by the completed contacts at the end -/

section KillBound

variable (K : Ctx) (root : Digest) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The inputs whose query may complete a contact from a state extending `s1`: FORS leaf inputs
and digest blocks not cached in `s1`. -/
def KillIn (s1 : State) (x : HashInput) : Prop :=
  HiddenBridge.IsFleafIn K.p x ∨ (IsMsgInput x ∧ s1.cache x = none)

/-- **The weight of a completed contact**: `weightB` once a contact is completed. -/
noncomputable def psiN (s : State) : ℝ≥0∞ := if NearContact K root s then weightB K s else 0

/-- The expected weight of the completed contacts at the end of the completed runs. -/
noncomputable def endN {α : Type} (comp : OracleComp CostSpec α) (budget : ℕ) (s : State) : ℝ≥0∞ :=
  ∑' out, Pr[= out | interp K.tg K.initial model comp budget s] * out.1.1.elim 0 (fun _ => psiN K root out.2)

theorem psiN_le (s : State) : psiN K root s ≤ weightB K s := by
  unfold psiN
  split_ifs
  · exact le_rfl
  · exact zero_le

theorem endN_pure {α : Type} (value : α) (budget : ℕ) (s : State) :
    endN K root model (pure value : OracleComp CostSpec α) budget s = psiN K root s := by
  unfold endN
  rw [interp_pure, tsum_probOutput_pure_mul]
  rfl

theorem endN_query_bind {α : Type} (input : CostSpec.Domain) (next : CostSpec.Range input → OracleComp CostSpec α)
    (budget : ℕ) (s : State) (h : sourceCost input ≤ budget) :
    endN K root model (liftM (CostSpec.query input) >>= next) budget s =
      ∑' r, Pr[= r | costStep model input s] * endN K root model (next r.1) (budget - sourceCost input) r.2 := by
  unfold endN
  rw [interp_query_bind, if_pos h, tsum_probOutput_bind_mul]
  refine tsum_congr fun r => ?_
  rw [tsum_probOutput_map_mul]

/-- An ordinary query at a cached input keeps its entry. -/
theorem ordinaryStep_cache_cached (x : HashInput) (s : State) (hx : s.cache x ≠ none) :
    ∀ r ∈ support (ordinaryStep model x s.known s), r.2.cache x = s.cache x := by
  intro r hr
  have hread : ∀ s' : State, s'.cache = s.cache → ∀ r ∈ support (readOutside x s'), r.2.cache x = s.cache x := by
    intro s' hs' r hr
    rcases readOutside_support x s' r hr with h | ⟨h0, _⟩
    · rw [h, hs']
    · rw [hs'] at h0
      exact absurd h0 hx
  unfold ordinaryStep at hr
  split at hr
  · exact hread s rfl r hr
  · split at hr
    · exact hread (DebtState.record s _) rfl r hr
    · split at hr
      · rw [support_map] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        rw [sampleCoordinate_expose _ s r' hr']
        rfl
      · exact hread s rfl r hr

/-- **A reveal step**: the kill it pays is the completed weight it adds, exactly. -/
theorem reveal_step (c : Coordinate) (s : State) :
    ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] * payK K root s (.inl (.inr (.inr c))) r.2 +
        psiN K root s ≤
      ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] * psiN K root r.2 := by
  change ∑' r, Pr[= r | sampleCoordinate c s] * payK K root s (.inl (.inr (.inr c))) r.2 + psiN K root s ≤
      ∑' r, Pr[= r | sampleCoordinate c s] * psiN K root r.2
  have hnf : ¬IsFLQ K (.inl (.inr (.inr c)) : CostSpec.Domain) := by
    rintro ⟨f, hf⟩
    cases hf
  cases hc : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hc, tsum_probOutput_pure_mul, tsum_probOutput_pure_mul]
      have hp : payK K root s (.inl (.inr (.inr c))) s = 0 := by
        unfold payK
        rw [if_neg]
        rintro ⟨-, h1, h2⟩
        exact h2 h1
      rw [hp, zero_add]
  | none =>
      rw [sampleCoordinate_unknown c s hc, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
      by_cases hN : NearContact K root s
      · have hN' : ∀ v, NearContact K root (s.expose c v) := fun v =>
          nearContact_mono (extends_expose s c v hc) hN
        have hp : ∀ v, payK K root s (.inl (.inr (.inr c))) (s.expose c v) = 0 := fun v => by
          unfold payK
          rw [if_neg]
          rintro ⟨-, -, h2⟩
          exact h2 hN
        have hq : ∀ v, psiN K root (s.expose c v) = weightB K (s.expose c v) := fun v => by
          rw [psiN, if_pos (hN' v)]
        simp only [hp, hq, mul_zero, tsum_zero, zero_add]
        rw [psiN, if_pos hN]
        exact le_of_eq (weightB_expose_mean K s c hc).symm
      · by_cases hall : ∀ v, NearContact K root (s.expose c v)
        · have hp : ∀ v, payK K root s (.inl (.inr (.inr c))) (s.expose c v) = weightB K s := fun v => by
            rw [payK, if_pos ⟨hnf, hall v, hN⟩, weightA_eq_weightB, if_neg hN]
          have hq : ∀ v, psiN K root (s.expose c v) = weightB K (s.expose c v) := fun v => by
            rw [psiN, if_pos (hall v)]
          simp only [hp, hq]
          rw [psiN, if_neg hN, add_zero, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero,
            one_mul, weightB_expose_mean K s c hc]
        · push Not at hall
          obtain ⟨v0, hv0⟩ := hall
          have hno : ∀ v, ¬NearContact K root (s.expose c v) := fun v h =>
            hv0 ((nc_expose_iff K root s c v v0).1 h)
          have hp : ∀ v, payK K root s (.inl (.inr (.inr c))) (s.expose c v) = 0 := fun v => by
            unfold payK
            rw [if_neg]
            rintro ⟨-, h1, -⟩
            exact hno v h1
          simp only [hp, mul_zero, tsum_zero, zero_add]
          rw [psiN, if_neg hN]
          exact zero_le

/-- **A reveal-only run pays its kills by the completed weight it adds.** -/
theorem ro_bound {α : Type} (comp : OracleComp CostSpec α) (hro : RevealOnly comp) :
    ∀ budget (s : State), acct model (payK K root) comp budget s + psiN K root s ≤ endN K root model comp budget s := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s
      rw [acct_pure, zero_add, endN_pure]
  | query_bind input next ih =>
      intro budget s
      obtain ⟨⟨c, rfl⟩, hnext⟩ := (revealOnly_query_bind _ next).1 hro
      have hcost : sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inr c))) = 0 := rfl
      rw [acct_query_bind, if_pos (by rw [hcost]; exact Nat.zero_le _),
        endN_query_bind K root model _ next budget s (by rw [hcost]; exact Nat.zero_le _), hcost, Nat.sub_zero]
      have hstep := reveal_step K root model c s
      have e : ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] *
            (payK K root s (.inl (.inr (.inr c))) r.2 + acct model (payK K root) (next r.1) budget r.2) =
          ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] * payK K root s (.inl (.inr (.inr c))) r.2 +
            ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] * acct model (payK K root) (next r.1) budget r.2 := by
        simp only [mul_add, ENNReal.tsum_add]
      rw [e, add_right_comm]
      calc _ ≤ ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] * psiN K root r.2 +
            ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] * acct model (payK K root) (next r.1) budget r.2 :=
            add_le_add hstep le_rfl
        _ = ∑' r, Pr[= r | costStep model (.inl (.inr (.inr c))) s] *
              (acct model (payK K root) (next r.1) budget r.2 + psiN K root r.2) := by
            simp only [mul_add, ENNReal.tsum_add]
            ring
        _ ≤ _ := ENNReal.tsum_le_tsum fun r => mul_le_mul_right (ih r.1 (hnext r.1) _ r.2) _

variable (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
include hout

/-- **A step that queries no killing input and reveals no FORS secret completes no contact.** -/
theorem nc_step_nk (s1 : State) (input : CostSpec.Domain) (s : State) (hext : Extends s1 s)
    (hin : ∀ x, input = .inl (.inr (.inl x)) → ¬KillIn K s1 x)
    (hrev : ∀ c, input = .inl (.inr (.inr c)) → ¬IsSecretC c)
    (r : CostSpec.Range input × State) (hr : r ∈ support (costStep model input s))
    (h : NearContact K root r.2) : NearContact K root s := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · change r ∈ support ((fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hr
    rw [support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact h
  · rw [costStep_ordinary] at hr
    have hk := hin bytes rfl
    refine nc_of_agree K root (fun y hy => ?_) (fun i κ l hne => ?_) h
    · rcases eq_or_ne y bytes with rfl | hyx
      · have hc : s.cache y ≠ none := by
          rcases hy with hf | hm
          · exact absurd (Or.inl hf) hk
          · intro h0
            have h1 : s1.cache y = none := by
              cases h1 : s1.cache y with
              | none => rfl
              | some w => rw [hext.1 y w h1] at h0; cases h0
            exact hk (Or.inr ⟨hm, h1⟩)
        exact ordinaryStep_cache_cached model y s hc r hr
      · exact ordinaryStep_cache_ne model bytes s r hr y hyx
    · rcases known_ordinary model bytes s r hr _ hne with h' | ⟨a, ha⟩
      · exact h'
      · exact absurd ha.symm (hout a i κ l)
  · change r ∈ support (sampleCoordinate coordinate s) at hr
    have hr2 := sampleCoordinate_expose _ s r hr
    refine nc_of_agree K root (fun y _ => by rw [hr2]; rfl) (fun i κ l hne => ?_) h
    rw [hr2] at hne
    have hc : Coordinate.fors i κ l 0 ≠ coordinate := fun heq => hrev coordinate rfl ⟨i, κ, l, heq.symm⟩
    simpa [DebtState.expose, QueryCache.cacheQuery, hc] using hne
  · change r ∈ support (pure ((), s) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at h
    exact h

/-- **A run that kills late pays its kills by the completed weight at the end of its completed
runs**, from a state without a completed contact. -/
theorem lk_bound (s1 : State) {α : Type} (comp : OracleComp CostSpec α)
    (hav : Avoids (KillIn K s1) comp) (hlk : LateKill comp) :
    ∀ budget (s : State), Extends s1 s → ¬NearContact K root s →
      acct model (payK K root) comp budget s ≤ endN K root model comp budget s := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s _ _
      rw [acct_pure]
      exact zero_le
  | query_bind input next ih =>
      intro budget s hext hN
      obtain ⟨hin, hnext⟩ := (avoids_query_bind _ input next).1 hav
      rcases (lateKill_query_bind input next).1 hlk with ⟨hrev, hlk'⟩ | ⟨hc, hro⟩
      · rw [acct_query_bind]
        split_ifs with hcost
        · rw [endN_query_bind K root model input next budget s hcost]
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (costStep model input s)
          · have hN' : ¬NearContact K root r.2 := fun h =>
              hN (nc_step_nk K root model hout s1 input s hext hin hrev r hr h)
            have hp : payK K root s input r.2 = 0 := by
              unfold payK
              rw [if_neg]
              rintro ⟨-, h1, -⟩
              exact hN' h1
            rw [hp, zero_add]
            exact mul_le_mul_right (ih r.1 (hnext r.1) (hlk' r.1) _ r.2
              (hext.trans (extends_costStep model input s r hr)) hN') _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        · exact zero_le
      · have hro' : RevealOnly (liftM (CostSpec.query input) >>= next) :=
          (revealOnly_query_bind input next).2 ⟨hc, hro⟩
        have h := ro_bound K root model _ hro' budget s
        rw [psiN, if_neg hN, add_zero] at h
        exact h

end KillBound


/-! ### One signing call: the kills -/

section SignKill

/-- With one digest call, every call is the first. -/
theorem sgn_call_eq_first (hcalls : digestCalls = 1) (call : DigestCall) : call = firstCall :=
  Fin.ext (by have h := call.isLt; have h1 := hcalls; show call.val = 0; omega)

/-- With `M = 1` every index lands. -/
theorem sgn_landed_all (hHb : totalHeight = subtreeHeight) (parameter : PublicParameter) (i : Index) :
    Landed parameter i := by
  unfold Landed subtreePosition
  have h0 : totalHeight - subtreeHeight = 0 := by omega
  rw [h0, pow_zero, Nat.mod_one]
  have h : i.val < 2 ^ subtreeHeight := lt_of_lt_of_eq i.isLt (by rw [hHb])
  exact Nat.div_eq_of_lt h

/-- A view opens the cell of a FORS leaf query when its digest selects the query's leaf at its
index. -/
theorem opensC_of_digest {f : FIn} {u : DigestCall → HashOutput}
    (hi : digestIndex (truncateMessageDigest u) = f.index)
    (hl : digestLeaves (truncateMessageDigest u) f.κ = f.leaf) : OpensC (CellOf f) (viewOf u) := by
  refine ⟨?_, ?_⟩
  · show (Lifetime.localDigestView (truncateMessageDigest u)).1 = localIdx f.index
    rw [localDigestView_fst, hi]
  · show (Lifetime.localDigestView (truncateMessageDigest u)).2 f.κ = f.leaf
    rw [localDigestView_snd, hl]

/-- A fresh pair opens a given cell with chance at most `revRate`. -/
theorem fresh_open_le (hcalls : digestCalls = 1) (hHb : totalHeight = subtreeHeight) (parameter : PublicParameter)
    (x : DigestCall → HashInput) (st : State) (c : Cell) :
    ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if OpensC c (viewOf (fun _ : DigestCall => v)) then 1 else 0) ≤ revRate := by
  have hp := presample_one (D := HashInput) (ι := Coordinate) hcalls x firstCall st (fun v _ => if OpensC c (viewOf (fun _ : DigestCall => v)) then (1 : ℝ≥0∞) else 0)
  rw [hp]
  have hu : ∀ u : DigestCall → HashOutput, (fun _ : DigestCall => u firstCall) = u := fun u =>
    funext fun call => by rw [sgn_call_eq_first hcalls call]
  rw [Finset.sum_congr rfl fun u _ => by rw [hu u]]
  have hcard : (Fintype.card (DigestCall → HashOutput) : ℝ≥0∞) = (Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hpe : pairE (fun u => if OpensC c (viewOf u) then (1 : ℝ≥0∞) else 0) =
      ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u : DigestCall → HashOutput,
        (if OpensC c (viewOf u) then (1 : ℝ≥0∞) else 0) := by
    unfold pairE
    rw [tsum_uniform_eq, hcard]
  rw [← hpe]
  have hl : (fun u : DigestCall → HashOutput => if OpensC c (viewOf u) then (1 : ℝ≥0∞) else 0) =
      fun u => if Landed parameter (blockIndex (u firstCall)) then
        (fun v : View => if OpensC c v then (1 : ℝ≥0∞) else 0) (viewOf u) else 0 := by
    funext u
    rw [if_pos (sgn_landed_all hHb _ _)]
  rw [hl, pairE_landed parameter (fun v : View => if OpensC c v then (1 : ℝ≥0∞) else 0) 0,
    mul_zero, add_zero]
  exact le_trans (mul_le_of_le_one_left' ForsPrice.landing_le_one) (freshAvg_opensC c)

variable (K : Ctx) (data : PublicData) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The expected weight of the completed contacts at the end of the completed runs that do not
reveal the secret of the contact `f0`. -/
noncomputable def endG (f0 : FIn) {α : Type} (comp : OracleComp CostSpec α) (budget : ℕ) (s : State) : ℝ≥0∞ :=
  ∑' out, Pr[= out | interp K.tg K.initial model comp budget s] *
    (if f0.inC ∈ out.1.2.1 then 0 else out.1.1.elim 0 (fun _ => psiN K data.root out.2))

theorem endG_ordinary (f0 : FIn) {α : Type} (x : HashInput) (next : HashOutput → OracleComp CostSpec α)
    (budget : ℕ) (s : State) (hb : 1 ≤ budget) :
    endG K data model f0 (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] * endG K data model f0 (next r.1) (budget - 1) r.2 := by
  unfold endG
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  refine tsum_congr fun r => ?_
  rw [tsum_probOutput_map_mul]

theorem endG_liftProb_bind (f0 : FIn) {α β : Type} (sample : ProbComp α) (next : α → OracleComp CostSpec β)
    (budget : ℕ) (s : State) :
    endG K data model f0 ((liftM sample : OracleComp CostSpec α) >>= next) budget s =
      ∑' a, Pr[= a | sample] * endG K data model f0 (next a) budget s := by
  unfold endG
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]

/-- A draw step keeps the state. -/
theorem costStep_draw_tsum (q : ℕ) (s : State) (F : CostSpec.Range (.inl (.inl q)) × State → ℝ≥0∞) :
    ∑' r, Pr[= r | costStep model (.inl (.inl q)) s] * F r =
      ∑' v, Pr[= v | (liftM (unifSpec.query q) : ProbComp (Fin (q + 1)))] * F (v, s) := by
  change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query q) : ProbComp (Fin (q + 1)))] * F r = _
  rw [tsum_probOutput_map_mul]

/-- The account of a run after private randomness. -/
theorem acct_liftProb_bind (pay : State → CostSpec.Domain → State → ℝ≥0∞)
    (hpay : ∀ s n, pay s (.inl (.inl n)) s = 0) {α β : Type} (sample : ProbComp α)
    (next : α → OracleComp CostSpec β) (budget : ℕ) (s : State) :
    acct model pay ((liftM sample : OracleComp CostSpec α) >>= next) budget s =
      ∑' a, Pr[= a | sample] * acct model pay (next a) budget s := by
  induction sample using OracleComp.inductionOn with
  | pure value =>
      rw [liftM_pure, pure_bind, tsum_probOutput_pure_mul]
  | query_bind q rest ih =>
      have hc0 : sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inl q)) = 0 := rfl
      rw [liftM_bind, bind_assoc]
      change acct model pay (liftM (CostSpec.query (.inl (.inl q))) >>= fun v =>
        (liftM (rest v) : OracleComp CostSpec α) >>= next) budget s = _
      rw [acct_query_bind, if_pos (by rw [hc0]; exact Nat.zero_le _), costStep_draw_tsum,
        tsum_probOutput_bind_mul]
      refine tsum_congr fun v => ?_
      dsimp only
      rw [hpay, zero_add, hc0, Nat.sub_zero, ih v]

theorem avoids_finishCost_kill (msg : Message) (ρ : Randomness) (s1 : State)
    (hc : ∀ call, s1.cache (pblk K.p data (msg, ρ) call) ≠ none) :
    Avoids (KillIn K s1) (finishCostSource K.p data msg ρ) := by
  rw [finishCostSource_eq]
  refine avoids_bind _ (avoids_sequenceFin _ _ fun call => avoids_read _ _ ?_) fun outs => ?_
  · rintro (⟨f, hf⟩ | ⟨_, h0⟩)
    · exact PotentialA.msg_ne_fleaf (msgInput_digestInput K.p data.root msg ρ call) hf
    · exact hc call h0
  · refine avoids_mono (fun x hx => ?_) (avoids_or (avoids_finishRest_fleaf K.p K.p data msg ρ _)
      (avoids_finishRest K.p data msg ρ _))
    rcases hx with hf | ⟨hm, _⟩
    · exact Or.inl hf
    · exact Or.inr hm

/-- The chance that the pair of a randomizer opens a cell: one at a cached pair whose view opens
it, the reveal rate at a fresh pair. -/
noncomputable def openShare (c : Cell) (msg : Message) (s : State) (ρ : Randomness) : ℝ≥0∞ :=
  (pcache K.p data msg s ρ).elim revRate (fun u => if OpensC c (viewOf u) then 1 else 0)

/-- **A kill at the read of a fresh pair** needs the pair to open the contact's cell. -/
theorem opens_of_store_kill (hcalls : digestCalls = 1) (f0 : FIn) (s : State)
    (hf0 : ∀ g, FCk K s g → g = f0) (hN : ¬NearContact K data.root s) (msg : Message) (ρ : Randomness)
    (v : HashOutput) (hkill : NearContact K data.root (s.store (pblk K.p data (msg, ρ) firstCall) v)) :
    OpensC (CellOf f0) (viewOf (fun _ : DigestCall => v)) := by
  obtain ⟨g, ⟨w, ⟨hgw, hgi⟩, hgt⟩, hor⟩ := hkill
  have hxg : pblk K.p data (msg, ρ) firstCall ≠ g.input K.p :=
    PotentialA.msg_ne_fleaf (msgInput_digestInput K.p data.root msg ρ firstCall)
  have hg : FCk K s g :=
    ⟨w, ⟨by rw [← store_cache_ne s _ _ (Ne.symm hxg) v]; exact hgw, hgi⟩, hgt⟩
  have hgf := hf0 g hg
  subst hgf
  rcases hor with hk | ⟨m', ρ', dg, hcd, hl, hi, hlf, hok⟩
  · exact absurd ⟨g, hg, Or.inl hk⟩ hN
  · have hpb : HiddenBridge.cachedDigest (s.store (pblk K.p data (msg, ρ) firstCall) v).cache K.p data.root m' ρ' =
        (pcache K.p data (m', ρ').1 (s.store (pblk K.p data (msg, ρ) firstCall) v) (m', ρ').2).map
          truncateMessageDigest := rfl
    by_cases hq : (m', ρ') = (msg, ρ)
    · have hpc : pcache K.p data (m', ρ').1 (s.store (pblk K.p data (msg, ρ) firstCall) v) (m', ρ').2 =
          some (fun _ => v) := by
        refine pcache_of_cached K.p data (p := (m', ρ')) fun call => ?_
        rw [hq, sgn_call_eq_first hcalls call]
        simp [DebtState.store]
      rw [hpb, hpc] at hcd
      have hdg : truncateMessageDigest (fun _ : DigestCall => v) = dg := by simpa using hcd
      subst hdg
      exact opensC_of_digest hi hlf
    · have hsame : pcache K.p data (m', ρ').1 (s.store (pblk K.p data (msg, ρ) firstCall) v) (m', ρ').2 =
          pcache K.p data (m', ρ').1 s (m', ρ').2 :=
        pcache_congr K.p data fun call => store_cache_ne s _ _ (pblk_ne_of_ne K.p data hq call firstCall) v
      rw [hpb, hsame] at hcd
      exact absurd ⟨g, hg, Or.inr ⟨m', ρ', dg, hcd, hl, hi, hlf, hok⟩⟩ hN

variable (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
  (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
  (hwB : WtSpec model (weightB K) IsMsgInput)

include hout hparse hwB in
/-- **The final assembly from a cached pair**: its kills are paid by the weight if the pair opens
the contact's cell, and otherwise by the completed contacts at the end of the completed runs, none
of which reveals the contact's secret. -/
theorem fin_bound (f0 : FIn) (msg : Message) (ρ : Randomness) (s1 : State) (u : DigestCall → HashOutput)
    (hc : ∀ call, s1.cache (pblk K.p data (msg, ρ) call) = some (u call))
    (hN : ¬NearContact K data.root s1) (b : ℕ) :
    acct model (payK K data.root) (finishCostSource K.p data msg ρ) b s1 ≤
      weightB K s1 * (if OpensC (CellOf f0) (viewOf u) then 1 else 0) +
        endG K data model f0 (finishCostSource K.p data msg ρ) b s1 := by
  have h1 := lk_bound K data.root model hout s1 _
    (avoids_finishCost_kill K data msg ρ s1 fun call => by rw [hc call]; exact Option.some_ne_none _)
    (lateKill_finishCost K.p data msg ρ) b s1 (Extends.refl s1) hN
  refine h1.trans ?_
  unfold endN endG
  by_cases ho : OpensC (CellOf f0) (viewOf u)
  · rw [if_pos ho, mul_one]
    refine le_add_right ?_
    calc _ ≤ ∑' out, Pr[= out | interp K.tg K.initial model (finishCostSource K.p data msg ρ) b s1] *
          weightB K out.2 := by
          refine ENNReal.tsum_le_tsum fun out => mul_le_mul_right ?_ _
          rcases out with ⟨⟨_ | _, _⟩, st⟩
          · exact zero_le
          · exact psiN_le K data.root st
      _ ≤ _ := interp_wt_le K.tg K.initial hwB _ b s1
  · rw [if_neg ho, mul_zero, zero_add]
    refine ENNReal.tsum_le_tsum fun out => ?_
    by_cases hout' : out ∈ support (interp K.tg K.initial model (finishCostSource K.p data msg ρ) b s1)
    · have hnot : f0.inC ∉ out.1.2.1 := by
        intro hmem
        have hok := finish_reveals_ok K.tg K.initial model K.p data msg ρ b s1 u (fun call => hparse (msg, ρ) call)
          hc out hout' _ hmem f0.index f0.κ f0.leaf 0 rfl
        exact ho (opensC_of_digest hok.1.symm hok.2.symm)
      rw [if_neg hnot]
    · rw [probOutput_eq_zero_of_not_mem_support hout', zero_mul, zero_mul]

include hout hparse hwB in
/-- **One trial of the scan** (every trial lands): the read of the start's pair, then its final
assembly. -/
theorem loop_bound (hcalls : digestCalls = 1) (hHb : totalHeight = subtreeHeight) (f0 : FIn) (s : State)
    (hf0 : ∀ g, FCk K s g → g = f0) (hN : ¬NearContact K data.root s) (msg : Message) (attempts : ℕ)
    (ρ : Randomness) (b : ℕ) :
    acct model (payK K data.root) (signCostSourceLoop K.p data msg (data.step msg) (attempts + 1) ρ) b s ≤
      weightA K data.root s * openShare K data (CellOf f0) msg s ρ +
        endG K data model f0 (signCostSourceLoop K.p data msg (data.step msg) (attempts + 1) ρ) b s := by
  rw [signCostSourceLoop_succ]
  simp only [sgn_landed_all hHb K.p, if_true]
  have hwAB : weightA K data.root s = weightB K s := by rw [weightA_eq_weightB, if_neg hN]
  rw [acct_query_bind]
  split_ifs with hb
  · rw [endG_ordinary K data model f0 _ _ b s hb, costStep_ordinary]
    have hpx : model.parse (pblk K.p data (msg, ρ) firstCall) = none := hparse (msg, ρ) firstCall
    have hord : ordinaryStep model (pblk K.p data (msg, ρ) firstCall) s.known s =
        readOutside (pblk K.p data (msg, ρ) firstCall) s := by
      unfold ordinaryStep
      rw [hpx]
    change ∑' r, Pr[= r | ordinaryStep model (pblk K.p data (msg, ρ) firstCall) s.known s] *
        (payK K data.root s (.inl (.inr (.inl (pblk K.p data (msg, ρ) firstCall)))) r.2 +
          acct model (payK K data.root) (finishCostSource K.p data msg ρ) (b - 1) r.2) ≤
      weightA K data.root s * openShare K data (CellOf f0) msg s ρ +
        ∑' r, Pr[= r | ordinaryStep model (pblk K.p data (msg, ρ) firstCall) s.known s] *
          endG K data model f0 (finishCostSource K.p data msg ρ) (b - 1) r.2
    rw [hord]
    cases hc : s.cache (pblk K.p data (msg, ρ) firstCall) with
    | some u0 =>
        rw [readOutside_cached _ s u0 hc, tsum_probOutput_pure_mul, tsum_probOutput_pure_mul]
        dsimp only
        have hfull : ∀ call, s.cache (pblk K.p data (msg, ρ) call) = some ((fun _ : DigestCall => u0) call) :=
          fun call => by rw [sgn_call_eq_first hcalls call]; exact hc
        have hp : payK K data.root s (.inl (.inr (.inl (pblk K.p data (msg, ρ) firstCall)))) s = 0 := by
          unfold payK
          rw [if_neg]
          rintro ⟨-, h1, h2⟩
          exact h2 h1
        have hop : openShare K data (CellOf f0) msg s ρ =
            if OpensC (CellOf f0) (viewOf (fun _ : DigestCall => u0)) then 1 else 0 := by
          unfold openShare
          rw [pcache_of_cached K.p data (p := (msg, ρ)) hfull]
          rfl
        rw [hp, zero_add, hop, hwAB]
        exact fin_bound K data model hout hparse hwB f0 msg ρ s _ hfull hN (b - 1)
    | none =>
        rw [readOutside_fresh _ s hc, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
        dsimp only
        have hop : openShare K data (CellOf f0) msg s ρ = revRate := by
          unfold openShare
          rw [pcache_of_uncached K.p data (p := (msg, ρ)) (call := firstCall) hc]
          rfl
        rw [hop]
        have hpt : ∀ v : HashOutput,
            payK K data.root s (.inl (.inr (.inl (pblk K.p data (msg, ρ) firstCall))))
                (s.store (pblk K.p data (msg, ρ) firstCall) v) +
              acct model (payK K data.root) (finishCostSource K.p data msg ρ) (b - 1)
                (s.store (pblk K.p data (msg, ρ) firstCall) v) ≤
            weightA K data.root s * (if OpensC (CellOf f0) (viewOf (fun _ : DigestCall => v)) then 1 else 0) +
              endG K data model f0 (finishCostSource K.p data msg ρ) (b - 1)
                (s.store (pblk K.p data (msg, ρ) firstCall) v) := by
          intro v
          by_cases hk : NearContact K data.root (s.store (pblk K.p data (msg, ρ) firstCall) v)
          · rw [acct_payK_of_nc K data.root model _ _ _ hk, add_zero,
              if_pos (opens_of_store_kill K data hcalls f0 s hf0 hN msg ρ v hk), mul_one]
            refine le_add_right ?_
            unfold payK
            split_ifs
            · exact le_rfl
            · exact zero_le
          · have hp : payK K data.root s (.inl (.inr (.inl (pblk K.p data (msg, ρ) firstCall))))
                (s.store (pblk K.p data (msg, ρ) firstCall) v) = 0 := by
              unfold payK
              rw [if_neg]
              rintro ⟨-, h1, -⟩
              exact hk h1
            have hfull : ∀ call, (s.store (pblk K.p data (msg, ρ) firstCall) v).cache (pblk K.p data (msg, ρ) call) =
                some ((fun _ : DigestCall => v) call) := fun call => by
              rw [sgn_call_eq_first hcalls call]
              simp [DebtState.store]
            rw [hp, zero_add]
            refine (fin_bound K data model hout hparse hwB f0 msg ρ _ _ hfull hk (b - 1)).trans
              (add_le_add (mul_le_mul' ?_ le_rfl) le_rfl)
            rw [hwAB]
            exact hwB.store_le s _ v (msgInput_digestInput K.p data.root msg ρ firstCall) hc
        calc _ ≤ ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (weightA K data.root s * (if OpensC (CellOf f0) (viewOf (fun _ : DigestCall => v)) then 1 else 0) +
                endG K data model f0 (finishCostSource K.p data msg ρ) (b - 1)
                  (s.store (pblk K.p data (msg, ρ) firstCall) v)) :=
              ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpt v) _
          _ = weightA K data.root s * ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (if OpensC (CellOf f0) (viewOf (fun _ : DigestCall => v)) then 1 else 0) +
              ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
                endG K data model f0 (finishCostSource K.p data msg ρ) (b - 1)
                  (s.store (pblk K.p data (msg, ρ) firstCall) v) := by
              rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
              exact tsum_congr fun v => by ring
          _ ≤ _ := add_le_add (mul_le_mul' le_rfl (fresh_open_le hcalls hHb K.p (pblk K.p data (msg, ρ)) s _)) le_rfl
  · exact zero_le

/-- The cached pairs of a message whose view opens a cell. -/
noncomputable def cntS (c : Cell) (msg : Message) (s : State) : ℕ :=
  (Finset.univ.filter fun ρ : Randomness => ∃ u, pcache K.p data msg s ρ = some u ∧ OpensC c (viewOf u)).card

include hout hparse hwB in
/-- **The kills of a signing call**: at most the weight times the chance that the signed pair opens
the contact's cell, plus the completed contacts at the end of the completed runs that do not reveal
the contact's secret. -/
theorem sign_kill_bound (hcalls : digestCalls = 1) (hHb : totalHeight = subtreeHeight) (f0 : FIn) (s : State)
    (hf0 : ∀ g, FCk K s g → g = f0) (hN : ¬NearContact K data.root s) (msg : Message) (b : ℕ) :
    WK model K data.root (signCostSource K.p data msg) b s ≤
      weightA K data.root s * (revRate + cinv * cntS K data (CellOf f0) msg s) +
        endG K data model f0 (signCostSource K.p data msg) b s := by
  change acct model (payK K data.root) (signCostSource K.p data msg) b s ≤ _
  unfold signCostSource
  obtain ⟨A0, hA⟩ : ∃ A0, digestAttemptLimit = A0 + 1 := ⟨digestAttemptLimit - 1, by unfold digestAttemptLimit; norm_num⟩
  rw [hA, acct_liftProb_bind model (payK K data.root) (fun s n => by
      unfold payK; rw [if_neg]; rintro ⟨-, h1, h2⟩; exact h2 h1),
    endG_liftProb_bind]
  have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = cinv := fun ρ => by
    rw [probOutput_uniformSample]
    rfl
  calc _ ≤ ∑' ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] *
        (weightA K data.root s * openShare K data (CellOf f0) msg s ρ +
          endG K data model f0 (signCostSourceLoop K.p data msg (data.step msg) (A0 + 1) ρ) b s) :=
        ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right
          (loop_bound K data model hout hparse hwB hcalls hHb f0 s hf0 hN msg A0 ρ b) _
    _ = weightA K data.root s * ∑' ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] *
          openShare K data (CellOf f0) msg s ρ +
        ∑' ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] *
          endG K data model f0 (signCostSourceLoop K.p data msg (data.step msg) (A0 + 1) ρ) b s := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        exact tsum_congr fun ρ => by ring
    _ ≤ _ := by
        refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
        simp only [hpr]
        rw [ENNReal.tsum_mul_left, tsum_fintype]
        have hpt : ∀ ρ, openShare K data (CellOf f0) msg s ρ ≤
            revRate + (if ∃ u, pcache K.p data msg s ρ = some u ∧ OpensC (CellOf f0) (viewOf u) then 1 else 0) := by
          intro ρ
          unfold openShare
          cases hpc : pcache K.p data msg s ρ with
          | none => exact le_self_add
          | some u =>
              simp only [Option.elim]
              by_cases ho : OpensC (CellOf f0) (viewOf u)
              · rw [if_pos ho, if_pos ⟨u, rfl, ho⟩]
                exact le_add_self
              · rw [if_neg ho]
                exact zero_le
        have hcard : cinv * (Fintype.card Randomness : ℝ≥0∞) = 1 :=
          ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
        calc cinv * ∑ ρ, openShare K data (CellOf f0) msg s ρ
            ≤ cinv * ∑ ρ : Randomness, (revRate +
                (if ∃ u, pcache K.p data msg s ρ = some u ∧ OpensC (CellOf f0) (viewOf u) then 1 else 0)) :=
              mul_le_mul' le_rfl (Finset.sum_le_sum fun ρ _ => hpt ρ)
          _ = revRate + cinv * cntS K data (CellOf f0) msg s := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add, ← mul_assoc,
                hcard, one_mul, Finset.sum_boole]
              rfl

end SignKill


/-! ### Cell counts and contacts after a signing call -/

section After

variable (K : Ctx) (data : PublicData)

/-- The live landed pairs at a cell. -/
noncomputable def cellPairs (c : Cell) (s : State) (P : List Pair) (L : QueryLog SigningSpec) : List Pair :=
  (livePairs L P).filter fun q => decide (OpensC c (pview K.p data s q))

theorem ncell_eq_cellPairs (c : Cell) (s : State) (P : List Pair) (L : QueryLog SigningSpec) :
    ncell K.p data c s P L = (cellPairs K data c s P L).length := rfl

/-- The cached pairs of the signed message at a cell are live landed pairs of the message there. -/
theorem cntS_le (hHb : totalHeight = subtreeHeight) (c : Cell) (msg : Message) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (hP : PInv K.p data s P) (hm : MsgLive L msg) :
    cntS K data c msg s ≤ ((cellPairs K data c s P L).filter fun q => decide (q.1 = msg)).length := by
  have hnd : ((cellPairs K data c s P L).filter fun q => decide (q.1 = msg)).Nodup :=
    ((hP.nodup.filter _).filter _).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card_of_injOn (fun ρ => (msg, ρ)) ?_ ?_
  · intro ρ hρ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hρ
    obtain ⟨u, hu, ho⟩ := hρ
    have hland : LandedIn K.p data s (msg, ρ) :=
      ⟨u firstCall, first_of_pcache K.p data hu, sgn_landed_all hHb K.p _⟩
    have hqP : (msg, ρ) ∈ P := (hP.mem _).2 hland
    have hv : pview K.p data s (msg, ρ) = viewOf u := pview_of_pcache (q := (msg, ρ)) hu
    show (msg, ρ) ∈ (((cellPairs K data c s P L).filter fun q => decide (q.1 = msg)).toFinset : Set Pair)
    rw [Finset.mem_coe, List.mem_toFinset]
    unfold cellPairs livePairs
    exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_filter.2 ⟨hqP, decide_eq_true hm⟩,
      decide_eq_true (by rw [hv]; exact ho)⟩, decide_eq_true rfl⟩
  · intro a _ b _ hab
    exact (Prod.mk.inj hab).2

/-- **The live landed pairs at a cell after a signing call**: the old ones of the other messages. -/
theorem cellPairs_sign (c : Cell) (msg : Message) (s s' : State) (P : List Pair) (L : QueryLog SigningSpec)
    (r : Option Signature) (hview : ∀ q ∈ P, pview K.p data s' q = pview K.p data s q) :
    cellPairs K data c s' (newPairs K.p data msg s s' ++ P) (L ++ [⟨msg, r⟩]) =
      (cellPairs K data c s P L).filter fun q => !decide (q.1 = msg) := by
  unfold cellPairs livePairs
  rw [List.filter_append]
  have hnew : (newPairs K.p data msg s s').filter (fun q => decide (MsgLive (L ++ [⟨msg, r⟩]) q.1)) = [] := by
    refine List.filter_eq_nil_iff.2 fun q hq => ?_
    obtain ⟨hqm, _, _⟩ := (mem_newPairs K.p data msg s).1 hq
    simp only [decide_eq_true_eq, msgLive_append, not_and, not_not]
    exact fun _ => hqm
  rw [hnew, List.nil_append, List.filter_filter, List.filter_filter, List.filter_filter]
  refine List.filter_congr fun q hq => ?_
  rw [hview q hq]
  simp only [msgLive_append, Bool.decide_and, ne_eq, Bool.not_eq_true']
  cases decide (OpensC c (pview K.p data s q)) <;> cases decide (MsgLive L q.1) <;> cases h : decide (q.1 = msg) <;>
    simp_all

/-- **The cell count after a signing call** drops by the live landed pairs of the signed message. -/
theorem ncell_sign (c : Cell) (msg : Message) (s s' : State) (P : List Pair) (L : QueryLog SigningSpec)
    (r : Option Signature) (hview : ∀ q ∈ P, pview K.p data s' q = pview K.p data s q) :
    ncell K.p data c s' (newPairs K.p data msg s s' ++ P) (L ++ [⟨msg, r⟩]) +
        ((cellPairs K data c s P L).filter fun q => decide (q.1 = msg)).length = ncell K.p data c s P L := by
  rw [ncell_eq_cellPairs, ncell_eq_cellPairs, cellPairs_sign K data c msg s s' P L r hview,
    List.length_eq_length_filter_add (l := cellPairs K data c s P L) (fun q => decide (q.1 = msg))]
  ring

/-- A signing call decides no FORS contact. -/
theorem fck_sign {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (msg : Message)
    (budget : ℕ) (s : State) (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp K.tg K.initial model (signCostSource K.p data msg) budget s)) (f : FIn) :
    FCk K o1.2 f ↔ FCk K s f := by
  have hc := interp_avoids_cache K.tg K.initial model _ _ (avoids_source_fleaf K.p K.p data msg) budget s o1 ho1
    (f.input K.p) ⟨f, rfl⟩
  unfold FCk Ctx.Fr
  rw [hc]

end After

/-! ### The signing step of the contact potential -/

section Main

/-- A weighted capped expectation is at most the cap of the weighted expectations. -/
theorem tsum_wmin_le {α : Type} (mx : ProbComp α) (w X : α → ℝ≥0∞) :
    ∑' a, Pr[= a | mx] * (w a * min 1 (X a)) ≤ min (∑' a, Pr[= a | mx] * w a) (∑' a, Pr[= a | mx] * (w a * X a)) :=
  le_min (ENNReal.tsum_le_tsum fun a => mul_le_mul_right (mul_le_of_le_one_right' (min_le_left _ _)) _)
    (ENNReal.tsum_le_tsum fun a => mul_le_mul_right (mul_le_mul' le_rfl (min_le_right _ _)) _)

theorem min_mul_one (a x : ℝ≥0∞) : min a (a * x) = a * min 1 x := by
  rcases le_total 1 x with h | h
  · rw [min_eq_left h, mul_one, min_eq_left (le_mul_of_one_le_right' h)]
  · rw [min_eq_right h, min_eq_right (mul_le_of_le_one_right' h)]

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax T : ℕ)
  {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (cU m : ℝ≥0∞) (Qtot : ℕ)

/-- **The signing step of the contact potential A4'** (the obligation `hsign` of `goodK_advProg`):
one signing call on a message never signed before, while fewer than `N` signatures were asked. -/
theorem goodK_sign (hcalls : digestCalls = 1) (hHb : totalHeight = subtreeHeight)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0) (hw : wbar ≤ 1)
    (L : QueryLog SigningSpec) (msg : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (hm : MsgLive L msg) (hlt : L.length < signatureLimit)
    (h : ∀ r, GoodK K data wbar Fail Lmax T model cU m Qtot (next r) (L ++ [⟨msg, r⟩])) :
    GoodK K data wbar Fail Lmax T model cU m Qtot (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= next) L := by
  intro budget s P Ms d R hI
  have hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none := fun p call =>
    hmsg _ (msgInput_digestInput K.p data.root p.1 p.2 call)
  have hwA : WtSpec model (weightA K data.root) IsMsgInput :=
    ⟨weightA_le_one K data.root, weightA_step_le K data.root model,
      fun s x u hd hx => weightA_store_digest_le K data.root hmsg s x u hx hd⟩
  have hwB : WtSpec model (weightB K) IsMsgInput :=
    ⟨weightB_le_one K, weightB_step_le K model, fun s x u hd hx => weightB_store_digest_le K hmsg s x u hx hd⟩
  rw [advProg_sign, XS_sign]
  set sign := signCostSource K.p data msg with hsign
  set cont : Option Signature → OracleComp CostSpec HiddenBridge.Outcome :=
    fun r => advProg K.p data (next r) (L ++ [⟨msg, r⟩]) with hcont
  set run := interp K.tg K.initial model sign budget s with hrun
  -- the ghosts after the call
  set Pp : Run HashInput Coordinate (Option Signature) × State → List Pair :=
    fun o1 => newPairs K.p data msg s o1.2 ++ P with hPp
  set Dp : Run HashInput Coordinate (Option Signature) × State → Multiset View :=
    fun o1 => discAfter K.p data msg s d o1 with hDp
  set bp : Run HashInput Coordinate (Option Signature) × State → ℕ :=
    fun o1 => budget - traceCost o1.1.2.2.1 with hbp
  set psiPost : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 (fun r => weightA K data.root o1.2 *
      psiK K data wbar Fail Lmax T o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1)) with hpsiPost
  have hWK : WK model K data.root (sign >>= cont) budget s =
      WK model K data.root sign budget s + ∑' o1, Pr[= o1 | run] *
        o1.1.1.elim 0 (fun r => WK model K data.root (cont r) (bp o1) o1.2) :=
    acct_bind model K.tg K.initial (payK K data.root) sign cont budget s
  have hWC : WC model K data.root (sign >>= cont) budget s =
      WC model K data.root sign budget s + ∑' o1, Pr[= o1 | run] *
        o1.1.1.elim 0 (fun r => WC model K data.root (cont r) (bp o1) o1.2) :=
    acct_bind model K.tg K.initial (fun s i _ => payC K data.root s i) sign cont budget s
  -- the facts after one completed call
  have hpostInv : ∀ o1 ∈ support run, ∀ r, o1.1.1 = some r →
      InvK K data Qtot (bp o1) o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (R ++ o1.1.2.1) ∧
        (∀ q ∈ P, pview K.p data o1.2 q = pview K.p data s q) := by
    intro o1 ho1 r hres
    obtain ⟨hprep', hP', hM', hD', hC', hview⟩ := sign_paramsS K.tg K.initial model Fail Qtot hparse (hfail msg)
      budget s P Ms d R hI.prep hI.pinv hI.minv hI.dinv hI.count o1 ho1 r hres
    refine ⟨⟨hprep', hP', hM', hD', hC',
      jInv_sign K.p data K.tg K.initial model hout hparse budget s L R msg o1 r ho1 hres hI.jinv, ?_⟩, hview⟩
    simp only [List.length_append, List.length_singleton]
    omega
  -- the induction hypothesis at every outcome
  have hstep : ∀ o1 ∈ support run,
      o1.1.1.elim 0 (fun r => WK model K data.root (cont r) (bp o1) o1.2) ≤
        psiPost o1 + cU * o1.1.1.elim 0 (fun r => WC model K data.root (cont r) (bp o1) o1.2) +
          ν * o1.1.1.elim 0 (fun r => XS K data.root data wbar Fail model m (next r) (L ++ [⟨msg, r⟩]) (bp o1) o1.2
            (Pp o1) (addMsg Ms msg) (Dp o1)) := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => simp
    | some r =>
        simp only [Option.elim, hpsiPost, hres]
        exact h r (bp o1) o1.2 (Pp o1) (addMsg Ms msg) (Dp o1) (R ++ o1.1.2.1) (hpostInv o1 ho1 r hres).1
  -- the main inequality: kills of the call plus the weighted potential after it
  have hmain : WK model K data.root sign budget s + ∑' o1, Pr[= o1 | run] * psiPost o1 ≤
      weightA K data.root s * psiK K data wbar Fail Lmax T s P Ms L d budget := by
    by_cases hw0 : weightA K data.root s = 0
    · have hz : ∀ o1, Pr[= o1 | run] * weightA K data.root o1.2 = 0 := by
        have hle := interp_wt_le K.tg K.initial hwA sign budget s
        rw [hw0, nonpos_iff_eq_zero, ENNReal.tsum_eq_zero] at hle
        exact hle
      have h1 : WK model K data.root sign budget s = 0 := acct_payK_of_weightA K data.root model sign budget s hw0
      have h2 : ∑' o1, Pr[= o1 | run] * psiPost o1 = 0 := by
        refine ENNReal.tsum_eq_zero.2 fun o1 => ?_
        simp only [hpsiPost]
        cases o1.1.1 with
        | none => simp
        | some r =>
            simp only [Option.elim]
            rw [← mul_assoc, hz o1, zero_mul]
      rw [h1, h2, zero_add]
      exact zero_le
    have hnb : ¬BadP K data.root s := fun hb => hw0 (weightA_of_badP K data.root hb)
    have hN : ¬NearContact K data.root s := fun hn => hnb (Or.inr (Or.inr (Or.inr hn)))
    have hnD : ¬Dead K s := fun hd => hnb (Or.inr (Or.inr (Or.inl hd)))
    have hwAB : weightA K data.root s = weightB K s := by rw [weightA_eq_weightB, if_neg hN]
    -- the non-contact terms do not grow
    set N0 : ℝ≥0∞ := coinPotK T budget + capC K.p data T budget s P L + lam Lmax (livePairs L P).length budget
      with hN0
    set Csum : State → List Pair → List Message → QueryLog SigningSpec → Multiset View → ℕ → ℝ≥0∞ :=
      fun s' P' Ms' L' d' k => ∑ f : FIn, if FCk K s f then coefK K data wbar Fail (CellOf f) s' P' Ms' L' d' k else 0
      with hCsumDef
    have hpsi : ∀ o1 ∈ support run, ∀ r, o1.1.1 = some r →
        psiK K data wbar Fail Lmax T o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1) ≤
          Csum o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1) + N0 := by
      intro o1 ho1 r hres
      have hview := (hpostInv o1 ho1 r hres).2
      have hb' : bp o1 ≤ budget := Nat.sub_le _ _
      have hsum : (∑ f : FIn, if FCk K o1.2 f then coefK K data wbar Fail (CellOf f) o1.2 (Pp o1) (addMsg Ms msg)
          (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1) else 0) =
          Csum o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1) := by
        simp only [hCsumDef]
        refine Finset.sum_congr rfl fun f _ => ?_
        by_cases hf : FCk K s f
        · rw [if_pos ((fck_sign K data model msg budget s o1 ho1 f).2 hf), if_pos hf]
        · rw [if_neg (fun h' => hf ((fck_sign K data model msg budget s o1 ho1 f).1 h')), if_neg hf]
      have hcoin : coinPotK T (bp o1) ≤ coinPotK T budget := by
        unfold coinPotK
        have hc : ((Nat.choose (bp o1) 2 : ℕ) : ℝ≥0∞) ≤ ((Nat.choose budget 2 : ℕ) : ℝ≥0∞) := by
          exact_mod_cast Nat.choose_le_choose 2 hb'
        gcongr
      have hcap : capC K.p data T (bp o1) o1.2 (Pp o1) (L ++ [⟨msg, r⟩]) ≤ capC K.p data T budget s P L := by
        refine capC_mono K.p data T hb' fun c => ?_
        rw [← ncell_sign K data c msg s o1.2 P L r hview]
        exact le_self_add
      have hlam : lam Lmax (livePairs (L ++ [⟨msg, r⟩]) (Pp o1)).length (bp o1) ≤
          lam Lmax (livePairs L P).length budget := by
        refine lam_mono ?_ hb'
        show (livePairs (L ++ [⟨msg, r⟩]) (newPairs K.p data msg s o1.2 ++ P)).length ≤ (livePairs L P).length
        unfold livePairs
        rw [List.filter_append]
        have hnew : (newPairs K.p data msg s o1.2).filter
            (fun q => decide (MsgLive (L ++ [⟨msg, r⟩]) q.1)) = [] := by
          refine List.filter_eq_nil_iff.2 fun q hq => ?_
          obtain ⟨hqm, _, _⟩ := (mem_newPairs K.p data msg s).1 hq
          simp only [decide_eq_true_eq, msgLive_append, not_and, not_not]
          exact fun _ => hqm
        rw [hnew, List.nil_append]
        refine (List.Sublist.length_le ?_)
        refine List.monotone_filter_right _ fun q hq => ?_
        simp only [decide_eq_true_eq, msgLive_append] at hq ⊢
        exact hq.1
      unfold psiK
      rw [hsum, hN0]
      exact le_trans (add_le_add (add_le_add (add_le_add le_rfl hcoin) hcap) hlam) (le_of_eq (by ring))
    have hN0E : ∑' o1, Pr[= o1 | run] * (weightA K data.root o1.2 * N0) ≤ weightA K data.root s * N0 :=
      interp_wt_const K.tg K.initial hwA sign budget s N0
    have hpre : psiK K data wbar Fail Lmax T s P Ms L d budget = Csum s P Ms L d budget + N0 := by
      unfold psiK
      simp only [hCsumDef, hN0]
      ring
    by_cases hfc : ∃ f0, FCk K s f0
    · obtain ⟨f0, hf0c⟩ := hfc
      have hf0 : ∀ g, FCk K s g → g = f0 := fun g hg => by
        by_contra hne
        exact hnD (Or.inr (Or.inl ⟨g, f0, hne, hg, hf0c⟩))
      set c0 : Cell := CellOf f0 with hc0
      have hCsum : ∀ s' P' Ms' L' d' k, Csum s' P' Ms' L' d' k = coefK K data wbar Fail c0 s' P' Ms' L' d' k := by
        intro s' P' Ms' L' d' k
        simp only [hCsumDef]
        rw [Finset.sum_eq_single f0 (fun g _ hg => if_neg fun h' => hg (hf0 g h')) (fun h' => absurd (Finset.mem_univ f0) h'),
          if_pos hf0c]
      have hmiss0 : s.known f0.inC = none := by
        by_contra hk
        exact hN ⟨f0, hf0c, Or.inl hk⟩
      set npre : ℕ := ncell K.p data c0 s P L with hnpre
      set cnt : ℕ := cntS K data c0 msg s with hcnt
      have hcnt_le : cnt ≤ npre := by
        refine (cntS_le K data hHb c0 msg s P L hI.pinv hm).trans ?_
        rw [hnpre, ncell_eq_cellPairs]
        exact List.length_filter_le _ _
      set n0 : ℕ := npre - cnt with hn0
      set Cst : ℝ≥0∞ := ((signatureLimit - (L.length + 1) : ℕ) : ℝ≥0∞) * revRate + cinv * (n0 + budget * revRate)
        with hCst
      set canon : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ :=
        fun o1 => canonL K.p data (ownW c0) wbar 0 Fail msg s P Ms L d (fun _ => False) budget o1 with hcanon
      set G : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ :=
        fun o1 => if f0.inC ∈ o1.1.2.1 then 0 else o1.1.1.elim 0 (fun _ => psiN K data.root o1.2) with hG
      -- the kills of the call
      have hkill : WK model K data.root sign budget s ≤
          weightA K data.root s * (revRate + cinv * cnt) + ∑' o1, Pr[= o1 | run] * G o1 :=
        sign_kill_bound K data model hout hparse hwB hcalls hHb f0 s hf0 hN msg budget
      -- the pointwise bound after the call
      have hpt : ∀ o1 ∈ support run,
          G o1 + o1.1.1.elim 0 (fun r => weightA K data.root o1.2 *
            coefK K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1)) ≤
            weightB K o1.2 * Cst + weightB K o1.2 * min 1 (canon o1) := by
        intro o1 ho1
        cases hres : o1.1.1 with
        | none =>
            simp only [hG, hres, Option.elim, ite_self, zero_add]
            exact zero_le
        | some r =>
            simp only [Option.elim]
            obtain ⟨hI', hview⟩ := hpostInv o1 ho1 r hres
            have hpot : PiC K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1) ≤
                canon o1 :=
              sign_pointG_level K.tg K.initial model K.p data wbar 0 Fail Qtot msg (ownW_props c0)
                (gate := fun _ => False) (fun _ _ _ h' => h') hparse (hfail msg) hw ENNReal.zero_ne_top budget s P Ms
                L d R hI.prep hI.pinv hI.minv hI.dinv hI.count o1 ho1 r hres (Nat.sub_le budget _)
            have hcoef : coefK K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1) ≤
                Cst + min 1 (canon o1) := by
              unfold coefK sigRiskF
              have hlen : signatureLimit - (L ++ [(⟨msg, r⟩ : (_ : Message) × Option Signature)]).length =
                  signatureLimit - (L.length + 1) := by simp
              rw [hlen, hCst]
              refine add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add ?_ ?_))) (min_le_min le_rfl hpot)
              · have hns := ncell_sign K data c0 msg s o1.2 P L r hview
                have hcl := cntS_le K data hHb c0 msg s P L hI.pinv hm
                have hle : ncell K.p data c0 o1.2 (newPairs K.p data msg s o1.2 ++ P) (L ++ [⟨msg, r⟩]) ≤ n0 := by
                  rw [hn0, hnpre, hcnt]
                  omega
                exact_mod_cast hle
              · exact mul_le_mul' (by exact_mod_cast (Nat.sub_le budget _ : bp o1 ≤ budget)) le_rfl
            by_cases hNo : NearContact K data.root o1.2
            · have hwA0 : weightA K data.root o1.2 = 0 := by rw [weightA_eq_weightB, if_pos hNo]
              rw [hwA0, zero_mul, add_zero]
              simp only [hG]
              split_ifs with hrev
              · exact zero_le
              · simp only [hres, Option.elim]
                rw [psiN, if_pos hNo]
                have hmiss : o1.2.known f0.inC = none := by
                  by_contra hk
                  rcases known_interp K.tg K.initial model sign budget s o1 ho1 _ hk with h' | h' | ⟨a, ha⟩
                  · exact h' hmiss0
                  · exact hrev h'
                  · exact hout a f0.index f0.κ f0.leaf ha.symm
                have hnl : NearLeaf K data.root o1.2 f0.index f0.κ f0.leaf := by
                  obtain ⟨g, hg, hor⟩ := hNo
                  have hgf := hf0 g ((fck_sign K data model msg budget s o1 ho1 g).1 hg)
                  rw [hgf] at hor
                  rcases hor with hk | hnl
                  · exact absurd hmiss hk
                  · exact hnl
                have hrel := release_ownW K data wbar Fail hw (Ms := addMsg Ms msg) (bp o1) f0 hI'.pinv hI'.dinv hI'.jinv
                  hI'.len hnl hmiss
                have h1 : min 1 (canon o1) = 1 := min_eq_left (hrel.trans hpot)
                rw [h1, mul_one]
                exact le_add_self
            · have hwAB' : weightA K data.root o1.2 = weightB K o1.2 := by rw [weightA_eq_weightB, if_neg hNo]
              have hG0 : G o1 = 0 := by
                simp only [hG, hres, Option.elim]
                rw [psiN, if_neg hNo, ite_self]
              rw [hG0, zero_add, hwAB', ← mul_add]
              exact mul_le_mul' le_rfl hcoef
      -- the expectation after the call
      have hE : ∑' o1, Pr[= o1 | run] * (weightB K o1.2 * Cst + weightB K o1.2 * min 1 (canon o1)) ≤
          weightB K s * Cst + weightB K s * min 1 (PiC K data wbar Fail c0 s P Ms L d budget) := by
        simp only [mul_add, ENNReal.tsum_add]
        refine add_le_add (interp_wt_const K.tg K.initial hwB sign budget s Cst) ?_
        refine (tsum_wmin_le run (fun o1 => weightB K o1.2) canon).trans ?_
        rw [← min_mul_one]
        exact min_le_min (interp_wt_le K.tg K.initial hwB sign budget s)
          (sign_expectGA K.tg K.initial model hwB hcalls K.p data wbar 0 Fail msg (ownW_props c0) (fun _ => False)
            hparse hkind ENNReal.zero_ne_top budget budget s P Ms L hm d hI.pinv hI.minv)
      -- the contact part
      have hcontact : WK model K data.root sign budget s + ∑' o1, Pr[= o1 | run] *
          o1.1.1.elim 0 (fun r => weightA K data.root o1.2 *
            coefK K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1)) ≤
          weightA K data.root s * coefK K data wbar Fail c0 s P Ms L d budget := by
        calc _ ≤ weightA K data.root s * (revRate + cinv * cnt) + (∑' o1, Pr[= o1 | run] * G o1 +
              ∑' o1, Pr[= o1 | run] * o1.1.1.elim 0 (fun r => weightA K data.root o1.2 *
                coefK K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1))) := by
              rw [← add_assoc]
              exact add_le_add hkill le_rfl
          _ ≤ weightA K data.root s * (revRate + cinv * cnt) +
              (weightB K s * Cst + weightB K s * min 1 (PiC K data wbar Fail c0 s P Ms L d budget)) := by
              refine add_le_add le_rfl ?_
              calc _ = ∑' o1, Pr[= o1 | run] * (G o1 + o1.1.1.elim 0 (fun r => weightA K data.root o1.2 *
                    coefK K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1))) := by
                    rw [← ENNReal.tsum_add]
                    exact tsum_congr fun o1 => by ring
                _ ≤ ∑' o1, Pr[= o1 | run] * (weightB K o1.2 * Cst + weightB K o1.2 * min 1 (canon o1)) := by
                    refine ENNReal.tsum_le_tsum fun o1 => ?_
                    by_cases ho1 : o1 ∈ support run
                    · exact mul_le_mul_right (hpt o1 ho1) _
                    · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
                _ ≤ _ := hE
          _ = weightA K data.root s * coefK K data wbar Fail c0 s P Ms L d budget := by
              rw [← hwAB]
              unfold coefK sigRiskF
              have hsl : ((signatureLimit - L.length : ℕ) : ℝ≥0∞) =
                  ((signatureLimit - (L.length + 1) : ℕ) : ℝ≥0∞) + 1 := by
                rw [show signatureLimit - L.length = (signatureLimit - (L.length + 1)) + 1 by omega, Nat.cast_add,
                  Nat.cast_one]
              have hnc : ((npre : ℕ) : ℝ≥0∞) = (n0 : ℝ≥0∞) + (cnt : ℝ≥0∞) := by
                rw [hn0, ← Nat.cast_add, Nat.sub_add_cancel hcnt_le]
              rw [hsl, ← hnpre, hnc, hCst]
              ring
      calc _ ≤ WK model K data.root sign budget s + (∑' o1, Pr[= o1 | run] *
              o1.1.1.elim 0 (fun r => weightA K data.root o1.2 *
                coefK K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1)) +
            ∑' o1, Pr[= o1 | run] * (weightA K data.root o1.2 * N0)) := by
            refine add_le_add le_rfl ?_
            calc _ ≤ ∑' o1, Pr[= o1 | run] * (o1.1.1.elim 0 (fun r => weightA K data.root o1.2 *
                    coefK K data wbar Fail c0 o1.2 (Pp o1) (addMsg Ms msg) (L ++ [⟨msg, r⟩]) (Dp o1) (bp o1)) +
                    weightA K data.root o1.2 * N0) := by
                  refine ENNReal.tsum_le_tsum fun o1 => ?_
                  by_cases ho1 : o1 ∈ support run
                  · refine mul_le_mul_right ?_ _
                    simp only [hpsiPost]
                    cases hres : o1.1.1 with
                    | none => simp
                    | some r =>
                        simp only [Option.elim]
                        rw [← mul_add, ← hCsum]
                        exact mul_le_mul' le_rfl (hpsi o1 ho1 r hres)
                  · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
              _ = _ := by simp only [mul_add, ENNReal.tsum_add]
        _ ≤ weightA K data.root s * coefK K data wbar Fail c0 s P Ms L d budget + weightA K data.root s * N0 := by
            rw [← add_assoc]
            exact add_le_add hcontact hN0E
        _ = _ := by
            rw [hpre, hCsum]; ring
    · -- no contact: nothing is killed, the contact terms vanish
      push Not at hfc
      have h1 : WK model K data.root sign budget s = 0 :=
        acct_payK_of_noFC K data.root model sign (avoids_source_fleaf K.p K.p data msg) budget s hfc
      have hCz : ∀ s' P' Ms' L' d' k, Csum s' P' Ms' L' d' k = 0 := by
        intro s' P' Ms' L' d' k
        simp only [hCsumDef]
        exact Finset.sum_eq_zero fun f _ => if_neg (hfc f)
      rw [h1, zero_add, hpre, hCz, zero_add]
      refine le_trans (ENNReal.tsum_le_tsum fun o1 => ?_) hN0E
      by_cases ho1 : o1 ∈ support run
      · refine mul_le_mul_right ?_ _
        simp only [hpsiPost]
        cases hres : o1.1.1 with
        | none => simp
        | some r =>
            simp only [Option.elim]
            refine mul_le_mul' le_rfl ((hpsi o1 ho1 r hres).trans ?_)
            rw [hCz, zero_add]
      · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
  -- assembling
  rw [hWK]
  calc _ ≤ WK model K data.root sign budget s + ∑' o1, Pr[= o1 | run] *
        (psiPost o1 + cU * o1.1.1.elim 0 (fun r => WC model K data.root (cont r) (bp o1) o1.2) +
          ν * o1.1.1.elim 0 (fun r => XS K data.root data wbar Fail model m (next r) (L ++ [⟨msg, r⟩]) (bp o1) o1.2
            (Pp o1) (addMsg Ms msg) (Dp o1))) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun o1 => ?_)
        by_cases ho1 : o1 ∈ support run
        · exact mul_le_mul_right (hstep o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = (WK model K data.root sign budget s + ∑' o1, Pr[= o1 | run] * psiPost o1) +
          cU * ∑' o1, Pr[= o1 | run] * o1.1.1.elim 0 (fun r => WC model K data.root (cont r) (bp o1) o1.2) +
          ν * ∑' o1, Pr[= o1 | run] * o1.1.1.elim 0 (fun r => XS K data.root data wbar Fail model m (next r)
            (L ++ [⟨msg, r⟩]) (bp o1) o1.2 (Pp o1) (addMsg Ms msg) (Dp o1)) := by
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ cU, mul_left_comm _ ν, ENNReal.tsum_mul_left]
        ring
    _ ≤ _ := by
        refine add_le_add (add_le_add hmain (mul_le_mul' le_rfl ?_)) le_rfl
        rw [hWC]
        exact le_add_self

end Main

end FORS.Security.SWRoute
