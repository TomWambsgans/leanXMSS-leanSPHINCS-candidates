import FORS.SWRoute.Interface
import FORS.SmallBudget.SampleEvents

/-! **The SW route: its state.** The route runs on the small route's comparison (`PotentialA.Ctx`,
the targeting `tgA` under which second-order inputs are untargeted). This file fixes

* the bad set `BadP` (a decided hit, a WOTS event, two contacts, or a FORS contact at a revealed or
  near cell) and the weight `weightA` (zero on `BadP`, the
  survival weight otherwise);
* the near cells: `NearLeaf` (a cached landed pair selects the cell and every other tree's leaf
  secret is known) and `NearMiss` (also the cell's own secret is unknown);
* the near flag, a sticky ghost set at a FORS leaf query at a near-missing cell (`nextFlag`), the
  armed status `ArmedS` and the exponent `expo` (`ρ` unarmed, `2` armed, `+ 64` after a WOTS
  contact, `+ 1` after a FORS contact), the pending two-edge credit `pendA`;
* the ghost accounts of the route, at the granularity of the interpreted cost steps: `WF` (weight
  at digest queries), `WC` (weight at FORS leaf queries whose contact would survive), `WA`
  (weight at the arming moments of the near flag) and `WK` (weight at the steps other than FORS leaf
  queries at which a FORS contact becomes a near or revealed contact). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### State predicates -/

section Preds

variable (K : Ctx) (root : Digest)

/-- A WOTS contact at a retained key. -/
def WContact (s : St) : Prop := ∃ l i, Retained K.p l ∧ (K.ContactB s l i).Nonempty

/-- A retained key with a marker or a WOTS contact (the small route's `Armed` without its
`¬BadLeaf`, so that it is monotone). -/
def ArmedW (s : St) : Prop :=
  ∃ l, Retained K.p l ∧ ((∃ i, K.Marker s l i) ∨ ∃ i, (K.ContactB s l i).Nonempty)

/-- **A FORS contact**: a fresh FORS leaf answer equal to the leaf value it writes (a known
coordinate, fixed in `K.F`). Unlike `Ctx.FC` it reads the leaf value from `K.F`, so it depends on the
cache only. -/
def FCk (s : St) (f : FIn) : Prop := ∃ u, K.Fr s (f.input K.p) u ∧ truncateHash u = K.F f.outC

/-- A FORS contact exists. -/
def FContact (s : St) : Prop := ∃ f, FCk K s f

/-- **A near cell**: a cached landed pair selects leaf `leaf` of tree `κ` at `index`, and the leaf
secret it selects in every other tree is known. -/
def NearLeaf (s : St) (index : Index) (κ : FTree) (leaf : FLeaf) : Prop :=
  ∃ (message : Message) (randomness : Randomness) (digest : MessageDigest),
    cachedDigest s.cache K.p root message randomness = some digest ∧ Landed K.p (digestIndex digest) ∧
      digestIndex digest = index ∧ digestLeaves digest κ = leaf ∧
      ∀ κ', κ' ≠ κ → s.known (.fors index κ' (digestLeaves digest κ') 0) ≠ none

/-- **A near-missing cell** of a FORS leaf query: a near cell whose own secret is unknown. A signed
pair has every secret known, so it never makes a near-missing cell. -/
def NearMiss (s : St) (f : FIn) : Prop :=
  NearLeaf K root s f.index f.κ f.leaf ∧ s.known f.inC = none

/-- **A completed FORS contact**: a decided contact at a cell whose secret is known (revealed) or
which is a near cell. Monotone along the run. -/
def NearContact (s : St) : Prop :=
  ∃ f, FCk K s f ∧ (s.known f.inC ≠ none ∨ NearLeaf K root s f.index f.κ f.leaf)

/-- **Dead states**: two distinct WOTS contacts, two distinct decided FORS contacts, or a WOTS
contact together with a FORS contact. At most one contact survives with positive weight. -/
def Dead (s : St) : Prop :=
  (∃ (l : OtsKey) (i : ChainIndex) (v : Digest) (l' : OtsKey) (i' : ChainIndex) (v' : Digest),
      Retained K.p l ∧ Retained K.p l' ∧ v ∈ K.ContactB s l i ∧ v' ∈ K.ContactB s l' i' ∧
        (l, i, v) ≠ (l', i', v')) ∨
    (∃ f g, f ≠ g ∧ FCk K s f ∧ FCk K s g) ∨ (WContact K s ∧ FContact K s)

/-- **The bad set of the route**: a decided first-order hit, a WOTS event, a dead state, or a
completed FORS contact. (A FORS contact without guess record has its secret known, and two related
FORS contacts are a dead state, so the FORS payoff events are in the bad set.) Monotone along the
run. -/
def BadP (s : St) : Prop :=
  Realized K.tg K.initial s ∨ K.WotsBad s ∨ Dead K s ∨ NearContact K root s

/-- **The weight of the route**: zero on the bad set, the survival weight otherwise. -/
noncomputable def weightA (s : St) : ℝ≥0∞ :=
  if BadP K root s then 0 else survival K.tg K.initial s

/-- The bad set without the completed FORS contacts (it depends on the exposed coordinates only
through the decided hits). -/
def BadQ (s : St) : Prop := Realized K.tg K.initial s ∨ K.WotsBad s ∨ Dead K s

/-- **The weight before the completed contacts**: `weightA = if NearContact then 0 else weightB`
(`weightA_eq_weightB`). It keeps its mean exactly at every exposure. -/
noncomputable def weightB (s : St) : ℝ≥0∞ :=
  if BadQ K s then 0 else survival K.tg K.initial s

/-- **The armed status**: the near flag, a marker or WOTS contact at a retained key, or a decided
FORS contact. -/
def ArmedS (flag : Bool) (s : St) : Prop := flag = true ∨ ArmedW K s ∨ FContact K s

/-- **The exponent of the budget**: `ρ` unarmed, `2` armed, plus `64` after a WOTS contact and `1`
after a FORS contact. Reachable values with positive weight: `ρ, 2, 3, 66, 67`. -/
noncomputable def expo (ρ : ℝ) (flag : Bool) (s : St) : ℝ :=
  (if ArmedS K flag s then 2 else ρ) + (if WContact K s then 64 else 0) + (if FContact K s then 1 else 0)

/-- **The pending two-edge credit**: half a unit per input two steps below the word whose answer is
no payload one step below; none once a WOTS contact exists (then any further contact kills). -/
noncomputable def pendA (s : St) : ℝ≥0∞ := if WContact K s then 0 else ν / 2 * ((K.UAset s).encard : ℝ≥0∞)

/-! ### Steps -/

/-- A FORS leaf query step. -/
def IsFLQ (input : CostSpec.Domain) : Prop := ∃ f : FIn, input = .inl (.inr (.inl (f.input K.p)))

/-- **The arming trigger**: a FORS leaf query at a near-missing cell. -/
def ArmsAt (s : St) (input : CostSpec.Domain) : Prop :=
  ∃ f : FIn, input = .inl (.inr (.inl (f.input K.p))) ∧ NearMiss K root s f

/-- **The near flag after the pre-update of a step** (sticky). -/
noncomputable def nextFlag (flag : Bool) (s : St) (input : CostSpec.Domain) : Bool :=
  flag || decide (ArmsAt K root s input)

/-- Payment of a digest query: the weight. -/
noncomputable def payF (s : St) : CostSpec.Domain → ℝ≥0∞
  | .inl (.inr (.inl x)) => if K.tg.digest x then weightA K root s else 0
  | _ => 0

/-- **A FORS leaf query whose contact would survive**: its secret is unknown (so the query carries
its guess record), its cell is not a near cell, and no contact exists yet. Otherwise a contact
kills the weight. -/
def SurvivesAt (s : St) (f : FIn) : Prop :=
  s.known f.inC = none ∧ ¬NearLeaf K root s f.index f.κ f.leaf ∧ ¬FContact K s ∧ ¬WContact K s

/-- Payment of a FORS leaf query whose contact would survive: the weight. -/
noncomputable def payC (s : St) (input : CostSpec.Domain) : ℝ≥0∞ :=
  if ∃ f : FIn, input = .inl (.inr (.inl (f.input K.p))) ∧ SurvivesAt K root s f then weightA K root s else 0

/-- Booking of an arming moment: the weight. -/
noncomputable def payA (flag : Bool) (s : St) (input : CostSpec.Domain) : ℝ≥0∞ :=
  if flag = false ∧ ArmsAt K root s input then weightA K root s else 0

/-- Booking of a kill at a step other than a FORS leaf query: the weight before the step. -/
noncomputable def payK (s : St) (input : CostSpec.Domain) (s' : St) : ℝ≥0∞ :=
  if ¬IsFLQ K input ∧ NearContact K root s' ∧ ¬NearContact K root s then weightA K root s else 0

end Preds

/-! ### Accounts -/

section Accounts

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **A flag-free account** of an interpreted run: the expected sum, over the steps within the
budget, of a payment of the state before, the input and the state after. -/
noncomputable def acct (pay : St → CostSpec.Domain → St → ℝ≥0∞) {α : Type} (comp : OracleComp CostSpec α) :
    ℕ → St → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℕ → St → ℝ≥0∞) (fun _ _ _ => 0)
    (fun input _ next budget state =>
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input state] *
          (pay state input result.2 + next result.1 (budget - sourceCost input) result.2)
      else 0) comp

theorem acct_pure (pay : St → CostSpec.Domain → St → ℝ≥0∞) {α : Type} (value : α) (budget : ℕ) (s : St) :
    acct model pay (pure value : OracleComp CostSpec α) budget s = 0 := rfl

theorem acct_query_bind (pay : St → CostSpec.Domain → St → ℝ≥0∞) {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) (budget : ℕ) (s : St) :
    acct model pay (liftM (CostSpec.query input) >>= next) budget s =
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input s] *
          (pay s input result.2 + acct model pay (next result.1) (budget - sourceCost input) result.2)
      else 0 := rfl

variable (K : Ctx) (root : Digest)

/-- **The arming account** with the near flag as a ghost. -/
noncomputable def acctA {α : Type} (comp : OracleComp CostSpec α) : ℕ → St → Bool → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℕ → St → Bool → ℝ≥0∞) (fun _ _ _ _ => 0)
    (fun input _ next budget state flag =>
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input state] *
          (payA K root flag state input +
            next result.1 (budget - sourceCost input) result.2 (nextFlag K root flag state input))
      else 0) comp

theorem acctA_pure {α : Type} (value : α) (budget : ℕ) (s : St) (flag : Bool) :
    acctA model K root (pure value : OracleComp CostSpec α) budget s flag = 0 := rfl

theorem acctA_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) (budget : ℕ) (s : St) (flag : Bool) :
    acctA model K root (liftM (CostSpec.query input) >>= next) budget s flag =
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input s] *
          (payA K root flag s input +
            acctA model K root (next result.1) (budget - sourceCost input) result.2 (nextFlag K root flag s input))
      else 0 := rfl

/-- **WF**: the expected weight at the digest queries. -/
noncomputable def WF {α : Type} (comp : OracleComp CostSpec α) : ℕ → St → ℝ≥0∞ :=
  acct model (fun s input _ => payF K root s input) comp

/-- **WC**: the expected weight at the FORS leaf queries whose contact would survive. -/
noncomputable def WC {α : Type} (comp : OracleComp CostSpec α) : ℕ → St → ℝ≥0∞ :=
  acct model (fun s input _ => payC K root s input) comp

/-- **WK**: the expected weight at the steps other than FORS leaf queries that complete a FORS
contact (a kill). -/
noncomputable def WK {α : Type} (comp : OracleComp CostSpec α) : ℕ → St → ℝ≥0∞ :=
  acct model (payK K root) comp

/-- **WA**: the expected weight at the arming moments of the near flag. -/
noncomputable def WA {α : Type} (comp : OracleComp CostSpec α) : ℕ → St → Bool → ℝ≥0∞ :=
  acctA model K root comp

/-- The expected final weight of an interpreted run. -/
noncomputable def endW {α : Type} (comp : OracleComp CostSpec α) (budget : ℕ) (s : St) : ℝ≥0∞ :=
  ∑' out, Pr[= out | interp K.tg K.initial model comp budget s] * weightA K root out.2

end Accounts

end FORS.Security.SWRoute
