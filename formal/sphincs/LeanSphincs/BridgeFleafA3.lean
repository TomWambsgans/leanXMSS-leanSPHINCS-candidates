import LeanSphincs.BridgePotentialA8
import LeanSphincs.BridgeFleafLinear

/-! The linear potential of the small-budget route pays, besides the digest baseline, a fixed
amount at every FORS leaf query. A FORS leaf query costs the potential at most
`(1 + Y + K_F) 2^-128` (a guess, a recorded contact at the remaining budget `Y`, and a contact pair
paid by the pair term), while the rate decreases by at least `(ρ + K_F) 2^-128`; every other answer
of a FORS leaf input (canonical, cached, or at a known secret) costs at most `(1 + Y) 2^-128`. So
each FORS leaf query, fresh or cached, leaves `(ρ - 1 - x) 2^-128`, `x = total / 2^128`, which the
potential pays out. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenBridge

variable [Params]

/-- The FORS leaf inputs of a public parameter. -/
def IsFleafIn (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ index tree leaf secret, input = forsLeafInput parameter index tree leaf secret

end LeanSphincs.Security.HiddenBridge

namespace LeanSphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- The slack of one FORS leaf query: `1 + Y + (ρ - 1 - x) ≤ ρ` for `Y ≤ x`. -/
theorem arith_fleaf {ρ x : ℝ} (hN : Numeric ρ x) (hx : 0 ≤ x) {Y : ℝ≥0∞} (hY : Y ≤ ENNReal.ofReal x) :
    1 + Y + ENNReal.ofReal (ρ - 1 - x) ≤ ENNReal.ofReal ρ := by
  have hd : 0 ≤ ρ - 1 - x := by linarith [hN.contact]
  calc 1 + Y + ENNReal.ofReal (ρ - 1 - x)
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal x + ENNReal.ofReal (ρ - 1 - x) :=
        add_le_add (add_le_add (by rw [ENNReal.ofReal_one]) hY) le_rfl
    _ = ENNReal.ofReal (1 + x + (ρ - 1 - x)) := by
        rw [ENNReal.ofReal_add (by linarith) hd, ENNReal.ofReal_add (by norm_num) hx]
    _ = ENNReal.ofReal ρ := by
        congr 1
        ring

variable [Params]

namespace Ctx

variable (K : Ctx)

section Arith

variable {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) {Y : ℝ≥0∞} (hY : Y ≤ ENNReal.ofReal xr)
include hN hxr

theorem one_add_slack_le_rate (s : St) : 1 + ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.rate s :=
  calc 1 + ENNReal.ofReal (K.ρ - 1 - xr) = 1 + 0 + ENNReal.ofReal (K.ρ - 1 - xr) := by rw [add_zero]
    _ ≤ ENNReal.ofReal K.ρ := arith_fleaf hN hxr (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal xr)
    _ ≤ _ := K.rate_ge_rho hN s

include hY in
/-- **A fresh FORS leaf answer leaves the slack.** -/
theorem arithForsF (s : St) {index : Index} {tree : FtsTree} {leaf : FtsLeaf} {secret : Digest} {g : ℝ≥0∞}
    (hg : g ≤ 1) (hrec : g = 0 ∨ (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses) :
    g + ((if ¬K.Bad s ∧ ((Coordinate.ftsSecret index tree leaf, secret) ∉ s.guesses ∨
          ∃ tree' leaf' secret', tree' ≠ tree ∧ K.FContact s index tree' leaf' secret') then 1 else 0) +
        Y * (if (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses then 1 else 0)) +
      ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.rate s := by
  have hbase : 1 + Y + ENNReal.ofReal (K.ρ - 1 - xr) ≤ ENNReal.ofReal K.ρ := arith_fleaf hN hxr hY
  set d := ENNReal.ofReal (K.ρ - 1 - xr) with hd
  by_cases hr : (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses
  · rw [if_pos hr, mul_one]
    by_cases hp : ¬K.Bad s ∧ ∃ tree' leaf' secret', tree' ≠ tree ∧ K.FContact s index tree' leaf' secret'
    · obtain ⟨hb, tree', leaf', secret', htree, hc⟩ := hp
      rw [if_pos ⟨hb, Or.inr ⟨tree', leaf', secret', htree, hc⟩⟩]
      calc g + (1 + Y) + d ≤ 1 + (1 + Y) + d := add_le_add (add_le_add hg le_rfl) le_rfl
        _ = (1 + Y + d) + 1 := by ring
        _ ≤ ENNReal.ofReal K.ρ + ((K.KFset s).encard : ℝ≥0∞) := add_le_add hbase (K.one_le_kf hb hc)
        _ ≤ K.vrate s + ((K.KFset s).encard : ℝ≥0∞) := add_le_add (K.vrate_ge hN.high s) le_rfl
        _ ≤ _ := K.rate_ge_kf s
    · rw [if_neg (fun h => hp ⟨h.1, h.2.resolve_left (fun h' => h' hr)⟩), zero_add]
      calc g + Y + d ≤ 1 + Y + d := add_le_add (add_le_add hg le_rfl) le_rfl
        _ ≤ ENNReal.ofReal K.ρ := hbase
        _ ≤ _ := K.rate_ge_rho hN s
  · have hg0 : g = 0 := hrec.resolve_right hr
    rw [hg0, if_neg hr, mul_zero, add_zero, zero_add]
    have hite : (if ¬K.Bad s ∧ ((Coordinate.ftsSecret index tree leaf, secret) ∉ s.guesses ∨
        ∃ tree' leaf' secret', tree' ≠ tree ∧ K.FContact s index tree' leaf' secret') then (1 : ℝ≥0∞) else 0)
          ≤ 1 + Y := le_trans (by split_ifs <;> simp) le_self_add
    calc _ ≤ 1 + Y + d := add_le_add hite le_rfl
      _ ≤ ENNReal.ofReal K.ρ := hbase
      _ ≤ _ := K.rate_ge_rho hN s

end Arith

/-! ### FORS leaf queries leave the slack -/

section Fresh

variable {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) {y' : ℕ} (hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal xr)
  (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)

include hN hxr hY in
/-- A fresh FORS leaf answer pays its guess and the slack. -/
theorem fresh_forsF {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) {index : Index}
    {tree : FtsTree} {leaf : FtsLeaf} {secret : Digest} (hxF : x = forsLeafInput K.p index tree leaf secret)
    (hk : K.tg.kind x = .none) {g : ℝ≥0∞} (hg : g ≤ 1)
    (hrec : g = 0 ∨ (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g + ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤
      K.pot (y' + 1) s := by
  have hi := initial_none_of_fresh K.initial s hinv.prepared x hx
  have h := K.step_fors y' hx hi hxF hk
  have ha := K.arithForsF hN hxr hY s hg hrec
  set A : ℝ≥0∞ := (if ¬K.Bad s ∧ ((Coordinate.ftsSecret index tree leaf, secret) ∉ s.guesses ∨
      ∃ tree' leaf' secret', tree' ≠ tree ∧ K.FContact s index tree' leaf' secret') then 1 else 0) +
    ((y' : ℝ≥0∞) * ν) * (if (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses then 1 else 0) with hA
  rw [K.pot_succ]
  calc ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g + ν * ENNReal.ofReal (K.ρ - 1 - xr)
      ≤ K.pot y' s + ν * A + ν * g + ν * ENNReal.ofReal (K.ρ - 1 - xr) :=
        add_le_add (add_le_add h le_rfl) le_rfl
    _ = K.pot y' s + ν * (g + A + ENNReal.ofReal (K.ρ - 1 - xr)) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left ha bot_le)

include hN hxr hY hsec in
/-- **A guess at a fresh FORS leaf input** pays the guess, the answer and the slack. -/
theorem guess_freshF {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) (q : Address × Digest)
    (hp : HiddenGraph.parse K.p (candidateActive K.p) x = some q) (hk : s.known q.1.inputCoordinate = none)
    (hF : IsFleafIn K.p x) :
    ∑' r, Pr[= r | readOutside x (s.record (q.1.inputCoordinate, q.2))] * K.pot y' r.2 +
      ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.pot (y' + 1) s := by
  obtain ⟨rfl, -⟩ := (parse_some_iff _ _ x q).1 hp
  obtain ⟨addr, v⟩ := q
  obtain ⟨index₀, tree₀, leaf₀, secret₀, hxF⟩ := hF
  have hinv₁ := hinv.record (addr.inputCoordinate, v)
  have hx₁ : (s.record (addr.inputCoordinate, v)).cache (HiddenGraph.input K.p (addr, v)) = none := hx
  cases addr with
  | chain lay tree leaf chain step =>
      exfalso
      have hd := (domain_eq_of_input hxF trivial trivial).1
      cases hd
  | ftsLeaf index tree leaf =>
      have hKF : K.KFset (s.record ((Address.ftsLeaf index tree leaf).inputCoordinate, v)) = K.KFset s :=
        K.kfSet_record s _ fun index' tree' leaf' secret hg hc => by
          exfalso
          simp only [Address.inputCoordinate, Prod.mk.injEq, Coordinate.ftsSecret.injEq] at hg
          obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hg
          obtain ⟨w, hfr, -⟩ := hc
          have h1 := hfr.1
          change s.cache (HiddenGraph.input K.p (Address.ftsLeaf _ _ _, _)) = some w at h1
          rw [hx] at h1
          cases h1
      have hkind := hsec _ (Or.inr ⟨index, tree, leaf, v, rfl⟩)
      rw [input_fors] at hx₁ ⊢
      have main := K.fresh_forsF hN hxr hY hinv₁ hx₁ rfl hkind le_rfl (Or.inr List.mem_cons_self)
      have hrec := K.pot_record (y' + 1) s ((Address.ftsLeaf index tree leaf).inputCoordinate, v) hk hKF
      rw [mul_one] at main
      refine (ENNReal.add_le_add_iff_right ν_ne_top).1 ?_
      calc ∑' r, Pr[= r | readOutside (forsLeafInput K.p index tree leaf v)
              (s.record ((Address.ftsLeaf index tree leaf).inputCoordinate, v))] * K.pot y' r.2 +
            ν * ENNReal.ofReal (K.ρ - 1 - xr) + ν
          = ∑' r, Pr[= r | readOutside (forsLeafInput K.p index tree leaf v)
              (s.record ((Address.ftsLeaf index tree leaf).inputCoordinate, v))] * K.pot y' r.2 + ν +
            ν * ENNReal.ofReal (K.ρ - 1 - xr) := by ring
        _ ≤ K.pot (y' + 1) (s.record ((Address.ftsLeaf index tree leaf).inputCoordinate, v)) := main
        _ ≤ _ := hrec

end Fresh

/-- **A guess at a cached FORS leaf input** pays the guess and the slack. -/
theorem guess_cachedF {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) (y' : ℕ) {s : St} (hinv : K.Inv s)
    {x : HashInput} {u : HashOutput} (hc : s.cache x = some u) (q : Address × Digest)
    (hp : HiddenGraph.parse K.p (candidateActive K.p) x = some q) (hk : s.known q.1.inputCoordinate = none) :
    K.pot y' (s.record (q.1.inputCoordinate, q.2)) + ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.pot (y' + 1) s := by
  obtain ⟨rfl, -⟩ := (parse_some_iff _ _ x q).1 hp
  have hKF : K.KFset (s.record (q.1.inputCoordinate, q.2)) = K.KFset s := by
    refine K.kfSet_record s _ fun index tree leaf secret hg hfc => ?_
    obtain ⟨addr, v⟩ := q
    cases addr with
    | chain lay tree' leaf' chain step =>
        have := congrArg Prod.fst hg
        cases this
    | ftsLeaf index' tree' leaf' =>
        simp only [Address.inputCoordinate, Prod.mk.injEq, Coordinate.ftsSecret.injEq] at hg
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hg
        obtain ⟨w, hfr, -⟩ := hfc
        exact hinv.guessed _ w _ hfr hp hk
  calc K.pot y' (s.record (q.1.inputCoordinate, q.2)) + ν * ENNReal.ofReal (K.ρ - 1 - xr)
      ≤ K.pot y' s + ν + ν * ENNReal.ofReal (K.ρ - 1 - xr) := add_le_add (K.pot_record y' s _ hk hKF) le_rfl
    _ = K.pot y' s + ν * (1 + ENNReal.ofReal (K.ρ - 1 - xr)) := by ring
    _ ≤ K.pot y' s + ν * K.rate s :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (K.one_add_slack_le_rate hN hxr s) bot_le)
    _ = _ := (K.pot_succ y' s).symm

/-- A step that keeps the state pays the slack from the rate. -/
theorem pot_same_slack {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) (y' : ℕ) (s : St) :
    K.pot y' s + ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.pot (y' + 1) s := by
  rw [K.pot_succ]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ bot_le)
  exact le_trans le_add_self (K.one_add_slack_le_rate hN hxr s)

/-! ### One step -/

section Model

variable (M : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : M.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : M.incoming = Address.inputCoordinate) (hMo : M.outgoing = Address.outputCoordinate)

include hMp hMi in
/-- **A FORS leaf query** pays the slack `(ρ - 1 - x) 2^-128`, fresh or cached, at a known or an
unknown secret. -/
theorem stepFors {total : ℕ} (hN : Numeric K.ρ ((total : ℝ) / 2 ^ 128))
    (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)
    (bytes : HashInput) (hF : IsFleafIn K.p bytes) (budget : ℕ) (s : St) (hinv : K.Inv s) (hcost : 1 ≤ budget) :
    ∑' r, Pr[= r | costStep M (.inl (.inr (.inl bytes))) s] * K.potCap total (budget - 1) r.2 +
      ν * ENNReal.ofReal (K.ρ - 1 - (total : ℝ) / 2 ^ 128) ≤ K.potCap total budget s := by
  unfold potCap
  by_cases hb : budget ≤ total
  swap
  · rw [if_neg hb]
    exact le_top
  rw [if_pos hb]
  have hpot : ∀ r : HashOutput × St,
      (if budget - 1 ≤ total then K.pot (budget - 1) r.2 else ⊤) = K.pot (budget - 1) r.2 :=
    fun r => if_pos ((Nat.sub_le _ _).trans hb)
  simp only [hpot]
  have hxr : (0 : ℝ) ≤ (total : ℝ) / 2 ^ 128 := by positivity
  obtain ⟨y', rfl⟩ : ∃ y', budget = y' + 1 := ⟨budget - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal ((total : ℝ) / 2 ^ 128) := budget_le_x (by omega)
  have hsame := K.pot_same_slack hN hxr y' s
  obtain ⟨index, tree, leaf, secret, hxF⟩ := hF
  have hkF : K.tg.kind bytes = .none := hsec _ (Or.inr ⟨_, _, _, _, hxF⟩)
  rw [costStep_inl]
  cases hp : M.parse bytes with
  | none =>
      rw [lazyStep_unparsed M bytes s hp]
      cases hc : s.cache bytes with
      | some u =>
          rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
          exact hsame
      | none =>
          have h := K.fresh_forsF hN hxr hY hinv hc hxF hkF (g := 0) bot_le (Or.inl rfl)
          rw [mul_zero, add_zero] at h
          exact h
  | some q =>
      have hq : HiddenGraph.parse K.p (candidateActive K.p) bytes = some q := by rw [← hMp, hp]
      cases hk : s.known (M.incoming q.1) with
      | none =>
          rw [lazyStep_guess M bytes s q hp hk, hMi]
          rw [hMi] at hk
          cases hc : s.cache bytes with
          | some u =>
              have hc' : (s.record (q.1.inputCoordinate, q.2)).cache bytes = some u := hc
              rw [readOutside_cached bytes _ u hc', tsum_probOutput_pure_mul]
              exact K.guess_cachedF hN hxr y' hinv hc q hq hk
          | none => exact K.guess_freshF hN hxr hY hsec hinv hc q hq hk ⟨index, tree, leaf, secret, hxF⟩
      | some canonical =>
          by_cases heq : q.2 = canonical
          · rw [lazyStep_canonical M bytes s q hp canonical hk heq, tsum_probOutput_map_mul]
            calc ∑' r, Pr[= r | sampleCoordinate (M.outgoing q.1) s] * K.pot y' r.2 +
                  ν * ENNReal.ofReal (K.ρ - 1 - (total : ℝ) / 2 ^ 128)
                ≤ K.pot y' s + ν * ENNReal.ofReal (K.ρ - 1 - (total : ℝ) / 2 ^ 128) :=
                  add_le_add (K.sample_mean y' s _) le_rfl
              _ ≤ _ := hsame
          · rw [lazyStep_other M bytes s q hp canonical hk heq]
            cases hc : s.cache bytes with
            | some u =>
                rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
                exact hsame
            | none =>
                have h := K.fresh_forsF hN hxr hY hinv hc hxF hkF (g := 0) bot_le (Or.inl rfl)
                rw [mul_zero, add_zero] at h
                exact h

theorem digestCount_fleaf (tg' : Targeting HashInput HashOutput Coordinate)
    (hdig : tg'.digest = ForsSigner.IsMsgInput) (bytes : HashInput) (hF : IsFleafIn K.p bytes) :
    digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes)))) =
      0 := by
  have hnm : ¬ForsSigner.IsMsgInput bytes := by
    obtain ⟨index, tree, leaf, secret, rfl⟩ := hF
    exact fun hd => msg_ne_fors hd rfl
  have h := digestCount_bytes tg' bytes
  rw [hdig, if_neg hnm] at h
  exact_mod_cast h

include hMp hMi hMo in
/-- **One step with both payments.** -/
theorem stepF (tg' : Targeting HashInput HashOutput Coordinate) (hdig : tg'.digest = ForsSigner.IsMsgInput)
    {total : ℕ} (hN : Numeric K.ρ ((total : ℝ) / 2 ^ 128))
    (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)
    (hmsg : ∀ x, ForsSigner.IsMsgInput x → K.tg.kind x = .none)
    (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (budget : ℕ) (s : St) (hinv : K.Inv s)
    (hcost : sourceCost input ≤ budget) :
    ∑' r, Pr[= r | costStep M input s] * K.potCap total (budget - sourceCost input) r.2 +
      ENNReal.ofReal (K.ρ / 2 ^ 128) * digestCount tg' (recorded input) +
      ENNReal.ofReal ((K.ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) * fleafCount (IsFleafIn K.p) (recorded input) ≤
        K.potCap total budget s := by
  by_cases hF : ∃ bytes, input = .inl (.inr (.inl bytes)) ∧ IsFleafIn K.p bytes
  · obtain ⟨bytes, rfl, hF⟩ := hF
    have hc1 : sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes))) = 1 :=
      rfl
    rw [hc1] at hcost ⊢
    rw [K.digestCount_fleaf tg' hdig bytes hF, Nat.cast_zero, mul_zero, add_zero, fleafCount_recorded_inl,
      if_pos hF, mul_one, payment_eq]
    exact K.stepFors M hMp hMi hN hsec bytes hF budget s hinv hcost
  · have hfc : fleafCount (IsFleafIn K.p) (recorded input) = 0 :=
      fleafCount_recorded_eq_zero _ input fun bytes h hb => hF ⟨bytes, h, hb⟩
    rw [hfc, Nat.cast_zero, mul_zero, add_zero]
    exact K.step M hMp hMi hMo tg' hdig hN hsec hmsg input budget s hinv hcost

end Model

end Ctx

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

/-- **Linear potential on the small-budget route, paying every FORS leaf query.** Besides the
digest baseline `ρ / 2^128`, every FORS leaf query of the trace (fresh or cached) is paid
`(ρ - 1 - x) / 2^128`, `x = total / 2^128`. -/
theorem smallRoute_potentialF
    (hknown : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (tg : Targeting HashInput HashOutput Coordinate) (hdigest : tg.digest = ForsSigner.IsMsgInput)
    (total : ℕ) (hN : Numeric ρ ((total : ℝ) / 2 ^ 128))
    {α : Type} (comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α) :
    ∑' out, Pr[= out | interp tg prepared.2 (sampleModel parameterOutput highs) comp total
        (DebtState.start prepared.2 known)] *
      (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
        ENNReal.ofReal (ρ / 2 ^ 128) * digestCount tg out.1.2.2.1 +
        ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
          fleafCount (IsFleafIn (truncateHash parameterOutput)) out.1.2.2.1) ≤
      ENNReal.ofReal (ρ * total / 2 ^ 128) := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  have hMp : (sampleModel parameterOutput highs).parse = HiddenGraph.parse K.p (candidateActive K.p) :=
    sampleModel_parse parameterOutput highs
  have hMi := sampleModel_incoming parameterOutput highs
  have hMo := sampleModel_outgoing parameterOutput highs
  have h := interp_potential2 tg prepared.2 (sampleModel parameterOutput highs) (IsFleafIn K.p) K.Inv
    (K.potCap total) K.payoff (ENNReal.ofReal (K.ρ / 2 ^ 128))
    (ENNReal.ofReal ((K.ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128))
    (fun budget state _ => K.endValue_le_cap total budget state)
    (fun input budget state hinv hcost => K.stepF (sampleModel parameterOutput highs) hMp hMi hMo tg hdigest hN
      (ctxA_sec parameterOutput fixed highs remaining prepared known ρ)
      (ctxA_msg parameterOutput fixed highs remaining prepared known ρ) input budget state hinv hcost)
    (fun input state hinv => K.inv_step (sampleModel parameterOutput highs) hMp hMi input state hinv)
    comp total (DebtState.start prepared.2 known)
    (inv_start parameterOutput fixed highs remaining prepared known ρ hknown)
  refine h.trans (le_of_eq ?_)
  unfold Ctx.potCap
  rw [if_pos le_rfl]
  exact pot_start K known (show (0 : ℝ) ≤ ρ by linarith [hN.low]) total

end Sample

end LeanSphincs.Security.PotentialA
