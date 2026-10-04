import LeanSphincs.BridgeContact

/-! A generic potential argument through an adversary that never requests a signature on the same
message twice, for final values that may read the contacts, the reveals and the cache. A potential
of the lazy run pays the game's final value once it pays four kinds of steps: a query touching a
new message-randomizer pair, any other ordinary query, a signing call on a fresh message, and the
end of the game. The run keeps the item, disclosure, count and contact invariants, and every
revealed coordinate is exposed. -/

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

/-- A program whose final value is paid by the potential. -/
def GoodX (Φ : Potential) (G : FinalFn) (L : QueryLog SigningSpec)
    (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    BInv parameter data Qtot initial model s P d R budget →
      ∑' out, Pr[= out | interp tg initial model prog budget s] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
        Φ s P L d R budget

/-- A query touching a new pair is paid. -/
def NewPairPays (Φ : Potential) : Prop :=
  ∀ budget (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate),
    1 ≤ budget → BInv parameter data Qtot initial model s P d R budget →
      ∀ p : Pair, s.cache (pblk parameter data p 0) = none →
        pairE (fun u0 u1 => Φ (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d R (budget - 1)) ≤
          Φ s P L d R budget

/-- Any other ordinary query is paid. -/
def OrdinaryPays (Φ : Potential) : Prop :=
  ∀ budget (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate),
    1 ≤ budget → BInv parameter data Qtot initial model s P d R budget → ∀ x : HashInput,
      ¬(∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none) →
        ∑' r, Pr[= r | ordinaryStep model x s.known s] * Φ r.2 P L d R (budget - 1) ≤ Φ s P L d R budget

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

/-! ### The steps -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) {Φ : Potential} {G : FinalFn}

theorem goodX_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodX parameter data Qtot tg initial model Φ G L (next v)) :
    GoodX parameter data Qtot tg initial model Φ G L (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P d R hB
  rw [interp_draw, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] * Φ s P L d R budget :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_left' (h v budget s P d R hB) _
    _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- The sibling of a new pair, presampled after the first read. -/
theorem new_pair_boundX (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (L : QueryLog SigningSpec) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodX parameter data Qtot tg initial model Φ G L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hB : BInv parameter data Qtot initial model s P d R budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) (hp1 : s.cache (pblk parameter data p 1) = none)
    (call : Fin 2) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p call) u)] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
      pairE (fun u0 u1 => Φ (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d R (budget - 1)) := by
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
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        (s.store (pblk parameter data p call) u)] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
      ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if call = 0 then Φ (withPair parameter data s p u u') (addPair parameter P p u) L d R (budget - 1)
          else Φ (withPair parameter data s p u' u) (addPair parameter P p u') L d R (budget - 1)) := by
    intro u
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
      refine ENNReal.tsum_le_tsum fun u' => mul_le_mul_left' ?_ _
      rw [hstate u u']
      split_ifs with hc
      · exact h u (budget - 1) _ _ d R (binv_withPair hparse hb hB hp0 u u')
      · exact h u (budget - 1) _ _ d R (binv_withPair hparse hb hB hp0 u' u)
  refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_left' (hone u) _) (le_of_eq ?_)
  unfold pairE
  split_ifs with hc
  · rfl
  · exact tsum_swap2 _ (fun a b => Φ (withPair parameter data s p a b) (addPair parameter P p a) L d R (budget - 1))

/-- **One ordinary query.** -/
theorem goodX_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (hG0 : ∀ R s, G none R s = 0) (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data Qtot initial model Φ)
    (hord : OrdinaryPays parameter data Qtot initial model Φ)
    (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodX parameter data Qtot tg initial model Φ G L (next v)) :
    GoodX parameter data Qtot tg initial model Φ G L (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P d R hB
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinary, if_neg hb, tsum_probOutput_pure_mul]
    simp only [hG0, zero_le]
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  by_cases hnew : ∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none
  · obtain ⟨p, call, rfl, hp0⟩ := hnew
    have hp1 := hB.pinv.first p hp0
    have hfresh : s.cache (pblk parameter data p call) = none := by
      fin_cases call
      · exact hp0
      · exact hp1
    rw [ordinaryStep, hparse p call]
    simp only
    rw [readOutside_fresh _ s hfresh, tsum_probOutput_map_mul]
    exact le_trans (new_pair_boundX parameter data Qtot tg initial model hkind hparse hGstore L next h budget hb
      s P d R hB p hp0 hp1 call) (hnewp budget s P L d R hb hB p hp0)
  · calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] * Φ r.2 P L d R (budget - 1) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · exact mul_le_mul_left' (h r.1 (budget - 1) r.2 P d R (binv_ordinary hrows hb hB x hnew r hr)) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := hord budget s P L d R hb hB x hnew

theorem goodX_pure (hfin : FinalPays parameter data Qtot initial model Φ G) (L : QueryLog SigningSpec)
    (forgery : Forgery) (verified : Bool) :
    GoodX parameter data Qtot tg initial model Φ G L (pure (forgery, L, verified)) := by
  intro budget s P d R hB
  rw [interp_pure, tsum_probOutput_pure_mul]
  simp only [List.append_nil]
  exact hfin budget s P L d R hB forgery verified

theorem goodX_liftHash (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (hG0 : ∀ R s, G none R s = 0) (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data Qtot initial model Φ)
    (hord : OrdinaryPays parameter data Qtot initial model Φ)
    (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodX parameter data Qtot tg initial model Φ G L (next a)) :
    GoodX parameter data Qtot tg initial model Φ G L ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodX_ordinary parameter data Qtot tg initial model hparse hkind hrows hG0 hGstore hnewp hord L query _ ih

/-- **One signing call** on a message that was never signed before. -/
theorem goodX_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model) (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hG0 : ∀ R s, G none R s = 0) (hsign : SignPays parameter data Qtot tg initial model Φ)
    (L : QueryLog SigningSpec) (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodX parameter data Qtot tg initial model Φ G (L ++ [⟨m, r⟩]) (next r)) :
    GoodX parameter data Qtot tg initial model Φ G L (signCostSource parameter data m >>= next) := by
  intro budget s P d R hB
  unfold signCostSource
  rw [interp_bind, tsum_probOutput_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum fun o1 => ?_) (hsign budget s P L d R hB m hm)
  by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s)
  · refine mul_le_mul_left' ?_ _
    cases hres : o1.1.1 with
    | none =>
        rw [interpThen_none tg initial model next budget o1 hres, tsum_probOutput_pure_mul]
        simp only [hG0, zero_le]
    | some r =>
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have hB' := binv_sign hparse hrows Fail (hfail m) digestAttemptLimit budget hB o1 ho1 r hres
        refine le_trans (le_of_eq (tsum_congr fun o2 => ?_)) (h r _ o1.2 _ _ _ hB')
        simp only [List.append_assoc]
  · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]

end Steps

section Induction

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) {Φ : Potential} {G : FinalFn}

/-- **A paid potential through any adversary that never repeats a message.** -/
theorem goodX_advProg (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hG0 : ∀ R s, G none R s = 0) (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data Qtot initial model Φ)
    (hord : OrdinaryPays parameter data Qtot initial model Φ)
    (hsign : SignPays parameter data Qtot tg initial model Φ)
    (hfin : FinalPays parameter data Qtot initial model Φ G) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) → GoodX parameter data Qtot tg initial model Φ G L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      unfold finishGame
      exact goodX_liftHash parameter data Qtot tg initial model hparse hkind hrows hG0 hGstore hnewp hord L _ _
        fun v => goodX_pure parameter data Qtot tg initial model hfin L forgery v
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodX_draw parameter data Qtot tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodX_ordinary parameter data Qtot tg initial model hparse hkind hrows hG0 hGstore hnewp hord L
          bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : ∀ entry ∈ L, entry.1 ≠ message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodX_sign parameter data Qtot tg initial model hparse hrows Fail hfail hG0 hsign L message hm _
          fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

/-- **The final value of the whole run** is at most the start potential. -/
theorem final_le_start (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none) (hrows : FtsRows parameter model)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (hG0 : ∀ R s, G none R s = 0)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPays parameter data total initial model Φ)
    (hord : OrdinaryPays parameter data total initial model Φ)
    (hsign : SignPays parameter data total tg initial model Φ)
    (hfin : FinalPays parameter data total initial model Φ G)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total (DebtState.start initial known)] *
        G out.1.1 out.1.2.1 out.2 ≤ Φ (DebtState.start initial known) [] [] 0 [] total := by
  have h := goodX_advProg parameter data total tg initial model hparse hkind hrows Fail hfail hG0 hGstore hnewp hord
    hsign hfin M [] hnr total (DebtState.start initial known) [] 0 []
    (binv_start hclean hcleanF known total)
  simpa only [List.nil_append] using h

end Induction

end LeanSphincs.Security.ForsPotential
