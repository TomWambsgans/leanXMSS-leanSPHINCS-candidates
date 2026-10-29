import FORS.SWRoute.PPart

/-! **The contact potential's near coefficient and its excess account.** A FORS contact at a cell
`c = (index, κ, leaf)` is completed by a near cover at its own cell: a cached landed pair whose view
selects the cell and whose other trees are all disclosed at the index. Its forecast is the generic
one-coin potential with the own-cell witness `ownW c` at baseline zero (`PiC`). A new contact made at
a FORS leaf query costs `ν · min(1, PiC)`; the route charges `ν · m` of it per query (in `cU`), and the
rest goes to the **excess account** `XS m`: the expected sum, over the FORS leaf queries whose
contact would survive (`SurvivesAt`), of the weight times `(min(1, PiC) − m)^+` at the queried cell.
It is defined over the adversary program with the potentials' ghosts (cached landed pairs, touched
messages, signing log, disclosed views), updated as in `GoodN`. Its bound `ν · XS m ≤ x · Pbad` is
WP-F's (see `notes/CORE-P.md`, WP-F CONTRACT). -/

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

/-! ### The own-cell witness -/

/-- The cell of a FORS leaf query. -/
abbrev CellOf (f : FIn) : Index × FTree × FLeaf := (f.index, f.κ, f.leaf)

/-- **The own-cell near witness** of a cell: the target selects the cell and every other tree of the
target is covered. -/
noncomputable def ownW (c : Index × FTree × FLeaf) (v : View) (D : Multiset View) : ℝ≥0∞ :=
  if v.1 = localIdx c.1 ∧ v.2 c.2.1 = c.2.2 ∧ NearSub v c.2.1 D then 1 else 0

theorem ownW_props (c : Index × FTree × FLeaf) : WitnessProps (ownW c) := by
  intro v
  refine ⟨fun small large hle => ?_, fun D => ?_⟩
  · unfold ownW
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, h1.2.1, nearSub_mono hle h1.2.2⟩ h2
    · exact zero_le
    · exact le_rfl
  · unfold ownW
    split_ifs <;> simp

theorem ownW_le_near (c : Index × FTree × FLeaf) (v : View) (D : Multiset View) :
    ownW c v D ≤ witnessNear v D := by
  unfold ownW witnessNear
  split_ifs with h
  · exact le_trans (by rw [if_pos h.2.2]) (Finset.single_le_sum (f := fun κ =>
      if NearSub v κ D then (1 : ℝ≥0∞) else 0) (fun _ _ => zero_le) (Finset.mem_univ c.2.1))
  · exact zero_le

/-! ### The forecast and the excess payment -/

section Defs

variable (K : Ctx) (root : Digest) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- **The own-cell near forecast** of a cell at a ghost state: the one-coin potential of `ownW c` at
baseline zero, without gate. -/
noncomputable def PiC (c : Index × FTree × FLeaf) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  potG K.p data (ownW c) wbar 0 Fail (fun _ => False) s P Ms L d k

/-- The excess payment of an ordinary query: at a FORS leaf query whose contact would survive, the
weight times the part of the capped forecast above `m`. -/
noncomputable def excPay (m : ℝ≥0∞) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) (x : HashInput) : ℝ≥0∞ :=
  if h : ∃ f : FIn, x = f.input K.p ∧ SurvivesAt K root s f then
    weightA K root s * (min 1 (PiC K data wbar Fail (CellOf (Classical.choose h)) s P Ms L d k) - m)
  else 0

/-- The ghosts after an ordinary query: a new pair joins the cached landed pairs if it lands, and its
message joins the touched messages. -/
noncomputable def ghostP (s s' : State) (x : HashInput) (P : List Pair) : List Pair :=
  if h : ∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none then
    (if LandedIn K.p data s' (Classical.choose h) then Classical.choose h :: P else P)
  else P

noncomputable def ghostMs (s : State) (x : HashInput) (Ms : List Message) : List Message :=
  if h : ∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none then
    addMsg Ms (Classical.choose h).1
  else Ms

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (m : ℝ≥0∞)

/-- The excess account of a hash computation (the verification of the forgery). -/
noncomputable def xsHash {β : Type} (comp : OracleComp HashSpec β) (L : QueryLog SigningSpec) (d : Multiset View) :
    ℕ → State → List Pair → List Message → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℕ → State → List Pair → List Message → ℝ≥0∞) (fun _ _ _ _ _ => 0)
    (fun x _ next budget s P Ms =>
      if 1 ≤ budget then
        ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (excPay K root data wbar Fail m s P Ms L d budget x +
            next r.1 (budget - 1) r.2 (ghostP K data s r.2 x P) (ghostMs K data s x Ms))
      else 0) comp

/-- **The excess account `XS m`** of the rest of the game of an adversary program, from a ghost
state (signing log, budget, state, cached landed pairs, touched messages, disclosed views). -/
noncomputable def XS (M : OracleComp (OracleWorld + SigningSpec) Forgery) :
    QueryLog SigningSpec → ℕ → State → List Pair → List Message → Multiset View → ℝ≥0∞ :=
  OracleComp.construct
    (C := fun _ => QueryLog SigningSpec → ℕ → State → List Pair → List Message → Multiset View → ℝ≥0∞)
    (fun forgery L budget s P Ms d =>
      xsHash K root data wbar Fail model m
        (Concrete.verify (⟨data.root, K.p⟩ : PublicKey) forgery.message forgery.signature : OracleComp HashSpec Bool)
        L d budget s P Ms)
    (fun input _ rec L budget s P Ms d => match input with
      | .inl (.inl draw) => ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
          rec v L budget s P Ms d
      | .inl (.inr x) =>
          if 1 ≤ budget then
            ∑' r, Pr[= r | ordinaryStep model x s.known s] *
              (excPay K root data wbar Fail m s P Ms L d budget x +
                rec r.1 L (budget - 1) r.2 (ghostP K data s r.2 x P) (ghostMs K data s x Ms) d)
          else 0
      | .inr msg => ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data msg) budget s] *
          o1.1.1.elim 0 (fun r => rec r (L ++ [⟨msg, r⟩]) (budget - traceCost o1.1.2.2.1) o1.2
            (newPairs K.p data msg s o1.2 ++ P) (addMsg Ms msg) (discAfter K.p data msg s d o1))) M

theorem XS_pure (forgery : Forgery) (L : QueryLog SigningSpec) (budget : ℕ) (s : State) (P : List Pair)
    (Ms : List Message) (d : Multiset View) :
    XS K root data wbar Fail model m (pure forgery) L budget s P Ms d =
      xsHash K root data wbar Fail model m
        (Concrete.verify (⟨data.root, K.p⟩ : PublicKey) forgery.message forgery.signature : OracleComp HashSpec Bool)
        L d budget s P Ms := rfl

theorem XS_hash (x : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) :
    XS K root data wbar Fail model m (liftM ((OracleWorld + SigningSpec).query (.inl (.inr x))) >>= next)
        L budget s P Ms d =
      if 1 ≤ budget then
        ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (excPay K root data wbar Fail m s P Ms L d budget x +
            XS K root data wbar Fail model m (next r.1) L (budget - 1) r.2 (ghostP K data s r.2 x P)
              (ghostMs K data s x Ms) d)
      else 0 := rfl

theorem XS_sign (msg : Message) (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) :
    XS K root data wbar Fail model m (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= next)
        L budget s P Ms d =
      ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data msg) budget s] *
        o1.1.1.elim 0 (fun r => XS K root data wbar Fail model m (next r) (L ++ [⟨msg, r⟩])
          (budget - traceCost o1.1.2.2.1) o1.2 (newPairs K.p data msg s o1.2 ++ P) (addMsg Ms msg)
          (discAfter K.p data msg s d o1)) := rfl

theorem XS_draw (draw : ℕ) (next : Fin (draw + 1) → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) :
    XS K root data wbar Fail model m (liftM ((OracleWorld + SigningSpec).query (.inl (.inl draw))) >>= next)
        L budget s P Ms d =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        XS K root data wbar Fail model m (next v) L budget s P Ms d := rfl

end Defs

end FORS.Security.SWRoute
