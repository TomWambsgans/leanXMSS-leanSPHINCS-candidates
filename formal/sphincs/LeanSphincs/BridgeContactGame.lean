import LeanSphincs.BridgeContact

/-! The setting of a generic potential argument through an adversary that never requests a
signature on the same message twice, for final values that may read the contacts, the reveals and
the cache: potentials of the lazy run, final values, what it means for a potential to pay a query
touching a new message-randomizer pair, a signing call on a fresh message and the end of the game,
and the invariants of the run (items, disclosures, counts, contacts, exposed reveals) with their
preservation. The argument itself is in `BridgeFleafGame`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section Defs

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **The invariants of the lazy run.** -/
structure BInv (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate) (budget : ℕ) : Prop where
  prep : Prepared initial s
  pinv : PInv parameter data s P
  dinv : DInv R d
  count : CountInv parameter data Qtot s budget
  cinv : CInv parameter model s
  rinv : ∀ c ∈ R, s.known c ≠ none

/-- A potential of the lazy run: of the state, the items, the log, the disclosures, the reveals and
the remaining budget. -/
abbrev Potential := State → List Pair → QueryLog SigningSpec → Multiset View → List Coordinate → ℕ → ℝ≥0∞

/-- A final value: of the result, of all reveals and of the final state. -/
abbrev FinalFn := Option HiddenBridge.Outcome → List Coordinate → State → ℝ≥0∞

/-- A query touching a new pair is paid. -/
def NewPairPays (Φ : Potential) : Prop :=
  ∀ budget (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate),
    1 ≤ budget → BInv parameter data Qtot initial model s P d R budget →
      ∀ p : Pair, s.cache (pblk parameter data p 0) = none →
        pairE (fun u0 u1 => Φ (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d R (budget - 1)) ≤
          Φ s P L d R budget

/-- A signing call on a fresh message is paid. -/
def SignPays (Φ : Potential) : Prop :=
  ∀ budget (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate),
    BInv parameter data Qtot initial model s P d R budget → ∀ m : Message, (∀ entry ∈ L, entry.1 ≠ m) →
      ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] *
          o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
            (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
        Φ s P L d R budget

/-- The end of the game is paid. -/
def FinalPays (Φ : Potential) (G : FinalFn) : Prop :=
  ∀ budget (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate),
    BInv parameter data Qtot initial model s P d R budget → ∀ (forgery : Forgery) (verified : Bool),
      G (some (forgery, L, verified)) R s ≤ Φ s P L d R budget

end Defs

/-! ### The invariants along the run -/

section Inv

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {A : Type}
  {tg : Targeting HashInput HashOutput Coordinate} {initial : HiddenOutside.Cache HashInput HashOutput}
  {model : HiddenRows.Model HashInput HashOutput A Coordinate}

omit [Params] in
theorem cinv_store {s : State} (h : CInv parameter model s) {x : HashInput} (hx : s.cache x = none)
    (hpx : model.parse x = none) (u : HashOutput) : CInv parameter model (s.store x u) := by
  refine ⟨fun i t l v hv => cache_ne_of_extends (extends_store s x u hx) (h.guessed i t l v hv),
    fun x' a v i t l hp hi hc hk => ?_⟩
  by_cases hxx : x' = x
  · subst hxx
    rw [hpx] at hp
    cases hp
  · rw [store_cache_ne s x x' hxx u] at hc
    exact h.cached x' a v i t l hp hi hc hk

/-- After a new pair. -/
theorem binv_withPair (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {budget : ℕ} (hb : 1 ≤ budget) {s : State} {P : List Pair} {d : Multiset View} {R : List Coordinate}
    (hB : BInv parameter data Qtot initial model s P d R budget) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (a b : HashOutput) :
    BInv parameter data Qtot initial model (withPair parameter data s p a b) (addPair parameter P p a) d R
      (budget - 1) := by
  have hp1 := hB.pinv.first p hp0
  have hp1' : (s.store (pblk parameter data p 0) a).cache (pblk parameter data p 1) = none := by
    rw [store_cache_ne s _ _ (Ne.symm (pblk_ne_call parameter data p))]; exact hp1
  refine ⟨?_, pinv_withPair hB.pinv hp0 a b, hB.dinv, fun m => ?_, ?_, hB.rinv⟩
  · unfold withPair
    exact prepared_store initial _ (prepared_store initial s hB.prep _ a hp0) _ b hp1'
  · have h1 := count_withPair (parameter := parameter) (data := data) m s p a b
    have h2 := hB.count m
    omega
  · unfold withPair
    exact cinv_store (cinv_store hB.cinv hp0 (hparse p 0) a) hp1' (hparse p 1) b

/-- After an ordinary query touching no new pair. -/
theorem binv_ordinary (hrows : FtsRows parameter model) {budget : ℕ} (hb : 1 ≤ budget) {s : State} {P : List Pair}
    {d : Multiset View} {R : List Coordinate} (hB : BInv parameter data Qtot initial model s P d R budget)
    (x : HashInput) (hnew : ¬∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none)
    (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) :
    BInv parameter data Qtot initial model r.2 P d R (budget - 1) := by
  have hext := ordinaryStep_extends model x s r hr
  obtain ⟨hP', _⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hB.pinv
  refine ⟨fun i o hi => hext.1 i o (hB.prep i o hi), hP', hB.dinv, fun m => ?_,
    (ordinary_contacts (K := fun _ => none) hrows x s hB.cinv r hr).1, fun c hc => ?_⟩
  · have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
      rw [cachedCount_eq, cachedCount_eq]
      exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
    have h2 := hB.count m
    omega
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hB.rinv c hc)
    rw [hext.2.1 c v hv]
    exact Option.some_ne_none _

/-- After a signing call. -/
theorem binv_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model) (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (attempts budget : ℕ) {s : State} {P : List Pair} {d : Multiset View} {R : List Coordinate}
    (hB : BInv parameter data Qtot initial model s P d R budget)
    (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : o1.1.1 = some r) :
    BInv parameter data Qtot initial model o1.2 (newPairs parameter data m s o1.2 ++ P)
      (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1) := by
  obtain ⟨hprep', hP', hD', hC', _⟩ := sign_params tg initial model Fail Qtot hparse hfail attempts budget
    s P d R hB.prep hB.pinv hB.dinv hB.count o1 ho1 r hr
  have hext := interp_extends tg initial model _ budget s o1 ho1
  refine ⟨hprep', hP', hD', hC',
    (interp_contacts_avoid (K := fun _ => none) tg initial hrows _ (avoids_loopF parameter data m attempts)
      budget s hB.cinv o1 ho1).1, fun c hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hB.rinv c hc)
    rw [hext.2.1 c v hv]
    exact Option.some_ne_none _
  · exact interp_reveals_known tg initial _ budget s o1 ho1 c hc

/-- At the start of the run. -/
theorem binv_start (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (known : Knowledge Coordinate) (total : ℕ) :
    BInv parameter data total initial model (DebtState.start initial known) [] 0 [] total :=
  ⟨start_prepared initial known, start_pinv parameter data initial hclean known, (fun i t l h => by cases h),
    start_count parameter data initial hclean known total,
    ⟨(fun i t l v h => by cases h), fun x a v i t l hp hi hc _ => absurd (hcleanF x a v i t l hp hi) hc⟩,
    (fun c h => by cases h)⟩

end Inv

end LeanSphincs.Security.ForsPotential
