import LeanSphincs.BridgeContactGame
import LeanSphincs.BridgeFleafLinear

/-! A generic potential argument through an adversary that never requests a signature on the same
message twice, with a payment: an ordinary query whose input lies in a class `IsF` may raise the
potential by a fixed amount `pay`. If a potential (as in `BridgeContactGame`) pays new pairs
(message-digest inputs, outside the class), these ordinary queries, signing calls and the end of
the game, the final value of the whole run is at most the start potential plus `pay` times the
expected number of queries of the class in the run's trace. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

section Defs

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (IsF : HashInput → Prop) (pay : ℝ≥0∞)

/-- The expected number of queries of the class in the trace of an interpreted run. -/
noncomputable def expectedF {α : Type} (prog : OracleComp CostSpec α) (budget : ℕ) (s : State) : ℝ≥0∞ :=
  ∑' out, Pr[= out | interp tg initial model prog budget s] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)

/-- A program whose final value is paid by the potential and `pay` per query of the class. -/
def GoodXP (Φ : Potential) (G : FinalFn) (L : QueryLog SigningSpec)
    (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    BInv parameter data Qtot initial model s P d R budget →
      ∑' out, Pr[= out | interp tg initial model prog budget s] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
        Φ s P L d R budget + pay * expectedF tg initial model IsF prog budget s

/-- Any other ordinary query is paid, up to `pay` for a query of the class. -/
def OrdinaryPaysP (Φ : Potential) : Prop :=
  ∀ budget (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate),
    1 ≤ budget → BInv parameter data Qtot initial model s P d R budget → ∀ x : HashInput,
      ¬(∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none) →
        ∑' r, Pr[= r | ordinaryStep model x s.known s] * Φ r.2 P L d R (budget - 1) ≤
          Φ s P L d R budget + pay * (if IsF x then 1 else 0)

end Defs

/-! ### The steps -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (IsF : HashInput → Prop) (pay : ℝ≥0∞)
  {Φ : Potential} {G : FinalFn}

omit [Params] in
theorem tsum_bound_pay {α : Type} (mx : ProbComp α) (X : ℝ≥0∞) (Y : α → ℝ≥0∞) :
    ∑' a, Pr[= a | mx] * (X + pay * Y a) ≤ X + pay * ∑' a, Pr[= a | mx] * Y a := by
  calc ∑' a, Pr[= a | mx] * (X + pay * Y a)
      = (∑' a, Pr[= a | mx]) * X + pay * ∑' a, Pr[= a | mx] * Y a := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        exact tsum_congr fun a => by ring
    _ ≤ 1 * X + pay * ∑' a, Pr[= a | mx] * Y a := add_le_add (mul_le_mul' tsum_probOutput_le_one le_rfl) le_rfl
    _ = _ := by rw [one_mul]

theorem goodXP_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodXP parameter data Qtot tg initial model IsF pay Φ G L (next v)) :
    GoodXP parameter data Qtot tg initial model IsF pay Φ G L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P d R hB
  unfold expectedF
  rw [interp_draw, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (Φ s P L d R budget + pay * expectedF tg initial model IsF (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P d R hB) _
    _ ≤ _ := tsum_bound_pay pay _ _ _

/-- The sibling of a new pair, presampled after the first read, with the payments. -/
theorem new_pair_boundXP (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (L : QueryLog SigningSpec) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodXP parameter data Qtot tg initial model IsF pay Φ G L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hB : BInv parameter data Qtot initial model s P d R budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) (hp1 : s.cache (pblk parameter data p 1) = none)
    (call : Fin 2) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p call) u)] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
      pairE (fun u0 u1 => Φ (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d R (budget - 1)) +
        pay * ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          expectedF tg initial model IsF (next u) (budget - 1) (s.store (pblk parameter data p call) u) := by
  set y := pblk parameter data p (if call = 0 then 1 else 0) with hy
  have hstate : ∀ u u', (s.store (pblk parameter data p call) u).store y u' =
      if call = 0 then withPair parameter data s p u u' else withPair parameter data s p u' u := by
    intro u u'
    fin_cases call
    · rfl
    · simp only [hy, Fin.mk_one, one_ne_zero, if_false, withPair]
      exact store_comm s _ _ (Ne.symm (pblk_ne_call parameter data p)) u u'
  have hsib : ∀ u, (s.store (pblk parameter data p call) u).cache y = none := by
    intro u
    have hne : y ≠ pblk parameter data p call := by
      fin_cases call
      · exact Ne.symm (pblk_ne_call parameter data p)
      · exact pblk_ne_call parameter data p
    rw [store_cache_ne s _ _ hne]
    fin_cases call
    · exact hp1
    · exact hp0
  set Φp : HashOutput → HashOutput → ℝ≥0∞ := fun u u' =>
    if call = 0 then Φ (withPair parameter data s p u u') (addPair parameter P p u) L d R (budget - 1)
      else Φ (withPair parameter data s p u' u) (addPair parameter P p u') L d R (budget - 1) with hΦp
  have hkey : ∀ u u', ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        ((s.store (pblk parameter data p call) u).store y u')] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
      Φp u u' + pay * expectedF tg initial model IsF (next u) (budget - 1)
        ((s.store (pblk parameter data p call) u).store y u') := by
    intro u u'
    rw [hstate u u']
    simp only [hΦp]
    split_ifs with hc
    · exact h u (budget - 1) _ _ d R (binv_withPair hparse hb hB hp0 u u')
    · exact h u (budget - 1) _ _ d R (binv_withPair hparse hb hB hp0 u' u)
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        (s.store (pblk parameter data p call) u)] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
      ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] * Φp u u' +
        pay * expectedF tg initial model IsF (next u) (budget - 1) (s.store (pblk parameter data p call) u) := by
    intro u
    have hpres := interp_presample_eq tg initial model y (hkind _ _) (next u) (budget - 1)
      (s.store (pblk parameter data p call) u) (fun o => (fleafCount IsF o.2.2.1 : ℝ≥0∞))
    rw [presample_fresh y _ (hsib u), tsum_probOutput_map_mul] at hpres
    refine le_trans (interp_presample_le tg initial model y (hkind _ _) (next u) (budget - 1) _
      (fun out => G out.1.1 (R ++ out.1.2.1) out.2) (fun out s' hs' => ?_)) ?_
    · cases hc : out.2.cache y with
      | some v =>
          rw [presample_cached y out.2 v hc, support_pure, Set.mem_singleton_iff] at hs'
          rw [hs']
      | none =>
          rw [presample_fresh y out.2 hc, support_map] at hs'
          obtain ⟨u', _, rfl⟩ := hs'
          exact hGstore _ _ _ _ _ hc
    · rw [presample_fresh y _ (hsib u), tsum_probOutput_map_mul]
      calc ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
            ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
              ((s.store (pblk parameter data p call) u).store y u')] * G out.1.1 (R ++ out.1.2.1) out.2
          ≤ ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (Φp u u' + pay * expectedF tg initial model IsF (next u) (budget - 1)
                ((s.store (pblk parameter data p call) u).store y u')) :=
            ENNReal.tsum_le_tsum fun u' => mul_le_mul_right (hkey u u') _
        _ = ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] * Φp u u' +
              pay * ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
                expectedF tg initial model IsF (next u) (budget - 1)
                  ((s.store (pblk parameter data p call) u).store y u') := by
            simp only [mul_add, ENNReal.tsum_add]
            rw [← ENNReal.tsum_mul_left]
            congr 1
            exact tsum_congr fun a => by ring
        _ = _ := by
            congr 2
  calc ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p call) u)] * G out.1.1 (R ++ out.1.2.1) out.2
      ≤ ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] * Φp u u' +
            pay * expectedF tg initial model IsF (next u) (budget - 1) (s.store (pblk parameter data p call) u)) :=
        ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hone u) _
    _ = ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] * Φp u u' +
        pay * ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          expectedF tg initial model IsF (next u) (budget - 1) (s.store (pblk parameter data p call) u) := by
        simp only [mul_add, ENNReal.tsum_add]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        exact tsum_congr fun a => by ring
    _ = _ := by
        congr 1
        unfold pairE
        simp only [hΦp]
        split_ifs with hc
        · rfl
        · exact tsum_swap2 _
            (fun a b => Φ (withPair parameter data s p a b) (addPair parameter P p a) L d R (budget - 1))

/-- **One ordinary query**, with the payment. -/
theorem goodXP_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (hFp : ∀ p call, ¬IsF (pblk parameter data p call))
    (hG0 : ∀ R s, G none R s = 0) (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data Qtot initial model Φ)
    (hord : OrdinaryPaysP parameter data Qtot initial model IsF pay Φ)
    (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodXP parameter data Qtot tg initial model IsF pay Φ G L (next v)) :
    GoodXP parameter data Qtot tg initial model IsF pay Φ G L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P d R hB
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinary, if_neg hb, tsum_probOutput_pure_mul]
    simp only [hG0, zero_le]
  have hexp : expectedF tg initial model IsF (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ((if IsF x then 1 else 0) + expectedF tg initial model IsF (next r.1) (budget - 1) r.2) := by
    unfold expectedF
    rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
    refine tsum_congr fun r => ?_
    rw [tsum_probOutput_map_mul]
    congr 1
    simp only [fleafCount_cons_inl, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, interp_mass, one_mul]
  rw [hexp, interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  by_cases hnew : ∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none
  · obtain ⟨p, call, rfl, hp0⟩ := hnew
    have hp1 := hB.pinv.first p hp0
    have hfresh : s.cache (pblk parameter data p call) = none := by
      fin_cases call
      · exact hp0
      · exact hp1
    simp only [if_neg (hFp p call), zero_add]
    rw [ordinaryStep, hparse p call]
    simp only
    rw [readOutside_fresh _ s hfresh, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    exact le_trans (new_pair_boundXP parameter data Qtot tg initial model IsF pay hkind hparse hGstore L next h
      budget hb s P d R hB p hp0 hp1 call) (add_le_add (hnewp budget s P L d R hb hB p hp0) le_rfl)
  · calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (Φ r.2 P L d R (budget - 1) + pay * expectedF tg initial model IsF (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · exact mul_le_mul_right (h r.1 (budget - 1) r.2 P d R (binv_ordinary hrows hb hB x hnew r hr)) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ = ∑' r, Pr[= r | ordinaryStep model x s.known s] * Φ r.2 P L d R (budget - 1) +
          pay * ∑' r, Pr[= r | ordinaryStep model x s.known s] *
            expectedF tg initial model IsF (next r.1) (budget - 1) r.2 := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [← ENNReal.tsum_mul_left]
          congr 1
          exact tsum_congr fun a => by ring
      _ ≤ (Φ s P L d R budget + pay * (if IsF x then 1 else 0)) +
          pay * ∑' r, Pr[= r | ordinaryStep model x s.known s] *
            expectedF tg initial model IsF (next r.1) (budget - 1) r.2 :=
          add_le_add (hord budget s P L d R hb hB x hnew) le_rfl
      _ = Φ s P L d R budget + pay * ∑' r, Pr[= r | ordinaryStep model x s.known s] *
            ((if IsF x then 1 else 0) + expectedF tg initial model IsF (next r.1) (budget - 1) r.2) := by
          have hmass : ∑' r, Pr[= r | ordinaryStep model x s.known s] = 1 := by simp
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          ring

theorem goodXP_pure (hfin : FinalPays parameter data Qtot initial model Φ G) (L : QueryLog SigningSpec)
    (forgery : Forgery) (verified : Bool) :
    GoodXP parameter data Qtot tg initial model IsF pay Φ G L (pure (forgery, L, verified)) := by
  intro budget s P d R hB
  rw [interp_pure, tsum_probOutput_pure_mul]
  simp only [List.append_nil]
  exact le_trans (hfin budget s P L d R hB forgery verified) le_self_add

theorem goodXP_liftHash (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (hFp : ∀ p call, ¬IsF (pblk parameter data p call))
    (hG0 : ∀ R s, G none R s = 0) (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data Qtot initial model Φ)
    (hord : OrdinaryPaysP parameter data Qtot initial model IsF pay Φ)
    (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodXP parameter data Qtot tg initial model IsF pay Φ G L (next a)) :
    GoodXP parameter data Qtot tg initial model IsF pay Φ G L ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodXP_ordinary parameter data Qtot tg initial model IsF pay hparse hkind hrows hFp hG0 hGstore hnewp hord
        L query _ ih

/-- **One signing call** on a message that was never signed before, with the payments. -/
theorem goodXP_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model) (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hG0 : ∀ R s, G none R s = 0) (hsign : SignPays parameter data Qtot tg initial model Φ)
    (L : QueryLog SigningSpec) (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodXP parameter data Qtot tg initial model IsF pay Φ G (L ++ [⟨m, r⟩]) (next r)) :
    GoodXP parameter data Qtot tg initial model IsF pay Φ G L (signCostSource parameter data m >>= next) := by
  intro budget s P d R hB
  set loop := signCostSourceLoop parameter data m digestAttemptLimit with hloop
  set E1 : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 (fun r => expectedF tg initial model IsF (next r) (budget - traceCost o1.1.2.2.1) o1.2) with hE1
  have hpt : ∀ o1 ∈ support (interp tg initial model loop budget s),
      ∑' out, Pr[= out | interpThen tg initial model next budget o1] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
        o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
          (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) + pay * E1 o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        rw [interpThen_none tg initial model next budget o1 hres, tsum_probOutput_pure_mul]
        simp only [hG0, zero_le]
    | some r =>
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        simp only [Option.elim, hE1, hres]
        have hB' := binv_sign hparse hrows Fail (hfail m) digestAttemptLimit budget hB o1 ho1 r hres
        refine le_trans (le_of_eq (tsum_congr fun o2 => ?_)) (h r _ o1.2 _ _ _ hB')
        simp only [List.append_assoc]
  have hE1le : ∀ o1, E1 o1 ≤ ∑' out, Pr[= out | interpThen tg initial model next budget o1] *
      (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) := by
    intro o1
    cases hres : o1.1.1 with
    | none => simp only [hE1, hres, Option.elim, zero_le]
    | some r =>
        simp only [hE1, hres, Option.elim]
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        unfold expectedF
        refine ENNReal.tsum_le_tsum fun o2 => mul_le_mul_right ?_ _
        simp only [fleafCount_append, Nat.cast_add]
        exact le_add_self
  unfold signCostSource
  rw [← hloop, interp_bind, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model loop budget s] *
        (o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
          (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) + pay * E1 o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model loop budget s)
        · exact mul_le_mul_right (hpt o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model loop budget s] *
          o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
            (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) +
        pay * ∑' o1, Pr[= o1 | interp tg initial model loop budget s] * E1 o1 := by
        simp only [mul_add, ENNReal.tsum_add]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        exact tsum_congr fun a => by ring
    _ ≤ Φ s P L d R budget + pay * expectedF tg initial model IsF (loop >>= next) budget s := by
        refine add_le_add (hsign budget s P L d R hB m hm) (mul_le_mul_right ?_ _)
        unfold expectedF
        rw [interp_bind, tsum_probOutput_bind_mul]
        exact ENNReal.tsum_le_tsum fun o1 => mul_le_mul_right (hE1le o1) _

end Steps

section Induction

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (IsF : HashInput → Prop) (pay : ℝ≥0∞)
  {Φ : Potential} {G : FinalFn}

/-- **A paid potential through any adversary that never repeats a message**, with the payments. -/
theorem goodXP_advProg (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (hFp : ∀ p call, ¬IsF (pblk parameter data p call))
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hG0 : ∀ R s, G none R s = 0) (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data Qtot initial model Φ)
    (hord : OrdinaryPaysP parameter data Qtot initial model IsF pay Φ)
    (hsign : SignPays parameter data Qtot tg initial model Φ)
    (hfin : FinalPays parameter data Qtot initial model Φ G) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodXP parameter data Qtot tg initial model IsF pay Φ G L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      unfold finishGame
      exact goodXP_liftHash parameter data Qtot tg initial model IsF pay hparse hkind hrows hFp hG0 hGstore hnewp
        hord L _ _ fun v => goodXP_pure parameter data Qtot tg initial model IsF pay hfin L forgery v
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodXP_draw parameter data Qtot tg initial model IsF pay L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodXP_ordinary parameter data Qtot tg initial model IsF pay hparse hkind hrows hFp hG0 hGstore hnewp
          hord L bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : ∀ entry ∈ L, entry.1 ≠ message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodXP_sign parameter data Qtot tg initial model IsF pay hparse hrows Fail hfail hG0 hsign L message
          hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

/-- **The final value of the whole run** is at most the start potential plus `pay` times the
expected number of queries of the class. -/
theorem final_le_startP (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (hFp : ∀ p call, ¬IsF (pblk parameter data p call))
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (hG0 : ∀ R s, G none R s = 0)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data total initial model Φ)
    (hord : OrdinaryPaysP parameter data total initial model IsF pay Φ)
    (hsign : SignPays parameter data total tg initial model Φ)
    (hfin : FinalPays parameter data total initial model Φ G)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total (DebtState.start initial known)] *
        G out.1.1 out.1.2.1 out.2 ≤
      Φ (DebtState.start initial known) [] [] 0 [] total +
        pay * expectedF tg initial model IsF (advProg parameter data M []) total (DebtState.start initial known) := by
  have h := goodXP_advProg parameter data total tg initial model IsF pay hparse hkind hrows hFp Fail hfail hG0 hGstore
    hnewp hord hsign hfin M [] hnr total (DebtState.start initial known) [] 0 []
    (binv_start hclean hcleanF known total)
  simpa only [List.nil_append] using h

end Induction

end LeanSphincs.Security.ForsPotential
