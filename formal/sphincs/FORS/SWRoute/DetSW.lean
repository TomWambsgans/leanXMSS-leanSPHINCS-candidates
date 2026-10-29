import FORS.SWRoute.Route
import FORS.SWRoute.PPartClosed
import FORS.SWRoute.CoinBound
import FORS.SWRoute.ForecastXS
import FORS.SWRoute.Interface

/-! **The SW route from the tail bound of the excess account.** `detSW_of` proves the route's
statement `DetSW` from the closed P-part (`ppart_closed`)
and `HTail`: the tail bound `ν · XS m ≤ ofReal (x · Pb)` under `ForecastTail m q' Pb` with no failing
index (WP-F's `xs_bound` with its domination discharged).

Everything else is done here: the facts of a sample, the coin (`coinPotK_le`, `capC_start_le` at
`T = ⌈3/2 · revRate · q'⌉ + 2^12`), the cap term `lam`, the excess account at a sample with a
failing index (charged to the failing mass), and the slack arithmetic. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential HiddenReveal
  Domination ForsPrice ForsSigner FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The facts of a sample and the tail obligation -/

/-- **The facts of a sample** used by the P-part. -/
structure SampleFacts (K : Ctx) (data : PublicData) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) : Prop where
  hyp : StepHyp K model
  parse : ∀ p call, model.parse (pblk K.p data p call) = none
  kind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none
  digest : ∀ p call, K.tg.digest (pblk K.p data p call)
  clean : ∀ p call, K.initial (pblk K.p data p call) = none
  msg : ∀ x, IsMsgInput x → K.tg.kind x = .none
  fail : ∀ msg r digest budget (s1 : State), Prepared K.initial s1 →
    ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data msg r digest) budget s1),
      out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail
  out : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0

/-- **The tail bound of the excess account** (the conclusion of WP-F's `xs_bound` under its
hypotheses, the domination `hexc` discharged). -/
def HTail : Prop :=
  ∀ (K : Ctx) (data : PublicData) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
    (wbar : ℝ≥0∞) (m Pb : ℝ) (q' : ℕ), ForecastTail m q' Pb → wbar = H0.wbarOf q' →
    totalHeight = subtreeHeight → digestCalls = 1 →
    (∀ p call, model.parse (pblk K.p data p call) = none) →
    (∀ p call, K.tg.kind (pblk K.p data p call) = .none) →
    (∀ p call, K.initial (pblk K.p data p call) = none) →
    (∀ msg r digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data msg r digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight)))) →
    (∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0) →
    ∀ (Cmax Lmax : ℕ), FairS wbar Cmax Lmax → q' ≤ Cmax → lam Lmax 0 q' ≤ (2 : ℝ≥0∞)⁻¹ ^ 101 →
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery), NoRepeat M [] → SignBound M signatureLimit →
    ∀ (known : HiddenReveal.Knowledge Coordinate), (∀ i κ l, known (Coordinate.fors i κ l 0) = none) →
      ν * XS K data.root data wbar ∅ model (ENNReal.ofReal m) M [] q' (DebtState.start K.initial known) [] [] 0 ≤
        ENNReal.ofReal ((q' : ℝ) / 2 ^ 128 * Pb)

/-- `HTail` is `xs_bound` with its domination hypothesis (WP-F-A's `excPay_le_psi`). -/
theorem hTail_of_exc
    (hexc : ∀ (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (tp : TailPar) (s : State) (P : List Pair)
      (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) (x : HashInput),
      totalHeight = subtreeHeight → wbar ≤ 1 → PInv K.p data s P → MInv K.p data s Ms →
      L.length ≤ signatureLimit → k ≤ tp.q → (∀ D, 0 ≤ tp.θ D) → 1 ≤ tp.n0 →
      (signatureLimit : ℝ) / 2 ^ subtreeHeight + (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight ≤ tp.μ →
      CoinCond subtreeHeight forsTrees forsHeight capFloor tp.q (tp.μ : ℝ) tp.n0 →
      KnownInvB s d →
      excPay K data.root data wbar ∅ (ENNReal.ofReal tp.m) s P Ms L d k x ≤
        ENNReal.ofReal (1 - tp.m) * psi K.p data wbar tp s P Ms L d k) : HTail :=
  fun K data model wbar m Pb q' hFT hw hH hc hp hk hcl hf ho _ _ hfair hQ hlam M hnr hsb known hkn =>
    xs_bound K data model wbar m Pb q' hFT hw hH hc hp hk hcl hf ho hfair hQ hlam M hnr hsb known hkn
      (fun tp s P Ms L d k x => hexc K data wbar tp s P Ms L d k x)

/-! ### Arithmetic -/

/-- The arming side condition holds at `δ = 1/4` (so `δ` may be capped there). -/
theorem SWNumeric.delta_lhs_le {ρ β δ x cU : ℝ} (h : SWNumeric ρ β δ x cU) :
    (1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2) * (2 - ρ) * x / (1 - x) ≤ 1 / 4 := by
  have hx0 := h.x0
  have hx8 := h.x8
  have hl := h.low
  have hh := h.high
  have h1x : 0 < 1 - x := by linarith
  have hρx : 0 ≤ ρ * x := mul_nonneg (by linarith) hx0
  have hρx2 : ρ * x ≤ 1 / 4 := by nlinarith
  have hρ1x : (ρ - 1) * x ≤ 2 := by nlinarith
  have hF0 : 0 ≤ 1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2 := by
    have : 0 ≤ ρ * (ρ - 1) * x ^ 2 := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg x)
    linarith
  have hF1 : 1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2 ≤ 1 := by
    have : ρ * (ρ - 1) * x ^ 2 = (ρ * x) * ((ρ - 1) * x) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hρ1x hρx]
  have hP : (1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2) * (2 - ρ) ≤ 1 * (1 / 2) :=
    mul_le_mul hF1 (by linarith) (by linarith) zero_le_one
  rw [div_le_iff₀ h1x]
  nlinarith [mul_le_mul_of_nonneg_right hP hx0]

/-- `2⁻¹ ^ n = 2 ^ k * 2⁻¹ ^ (n + k)` in `ℝ≥0∞`. -/
theorem inv_two_pow_split (n k : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ n = 2 ^ k * (2 : ℝ≥0∞)⁻¹ ^ (n + k) := by
  rw [pow_add, mul_left_comm, ← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow,
    mul_one]

/-- The cap term of the fair coin at the start is below `2^-205`. -/
theorem lam_le_205 (q : ℕ) : lam (H0.LmaxOf q) 0 q ≤ (2 : ℝ≥0∞)⁻¹ ^ 205 := by
  refine le_trans (H0.lam_start q) ?_
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ 205 = ENNReal.ofReal ((1 / 2 : ℝ) ^ 205) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h2]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (64 / 65 : ℝ) ^ (2 ^ 15 : ℕ) = ((64 / 65 : ℝ) ^ 64) ^ 512 := by rw [← pow_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) ^ 512 := pow_le_pow_left₀ (by norm_num) (by norm_num) 512
    _ ≤ (1 / 2 : ℝ) ^ 205 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)

/-- A failing index carries a share `2^-b` of the kept views. -/
theorem one_le_failMass {Fail : Finset (Fin (2 ^ subtreeHeight))} {l : Fin (2 ^ subtreeHeight)} (hl : l ∈ Fail) :
    1 ≤ (2 : ℝ≥0∞) ^ subtreeHeight * failMass Fail := by
  have hge : ∀ {V : Type} (U : Finset V) (g : V → ℝ≥0∞) (u : V), u ∈ U →
      (U.card : ℝ≥0∞)⁻¹ * g u ≤ freshAvg U g := fun U g u hu => by
    unfold freshAvg
    exact mul_le_mul_right (Finset.single_le_sum (f := g) (fun _ _ => bot_le) hu) _
  have hinner : freshAvg (Finset.univ : Finset (FTree → FLeaf))
      (fun m => (fun v : View => if v.1 ∈ Fail then (1 : ℝ≥0∞) else 0) (l, m)) = 1 := by
    calc _ = freshAvg (Finset.univ : Finset (FTree → FLeaf)) (fun _ => (1 : ℝ≥0∞)) := by
          congr 1
          funext m
          exact if_pos hl
      _ = 1 := freshAvg_const _ Finset.univ_nonempty 1
  have hmass : failMass Fail = freshAvg (Finset.univ : Finset (Fin (2 ^ subtreeHeight))) fun l' =>
      freshAvg (Finset.univ : Finset (FTree → FLeaf))
        (fun m => (fun v : View => if v.1 ∈ Fail then (1 : ℝ≥0∞) else 0) (l', m)) := by
    unfold failMass
    exact H0Avg.freshAvg_prod _
  have hcard : (((Finset.univ : Finset (Fin (2 ^ subtreeHeight))).card : ℕ) : ℝ≥0∞) = 2 ^ subtreeHeight := by
    rw [Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ subtreeHeight * (((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * 1) := by
        rw [mul_one, ENNReal.mul_inv_cancel (by simp) (by simp)]
    _ ≤ (2 : ℝ≥0∞) ^ subtreeHeight * failMass Fail := by
        refine mul_le_mul_right ?_ _
        rw [hmass]
        refine le_trans (le_of_eq ?_) (hge _ _ l (Finset.mem_univ l))
        rw [hcard]
        exact congrArg (fun t => ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * t) hinner.symm

/-- **The slack of the route**: the cap terms, the failing mass at `2^-201` and the seed term fit in
`(q' + keygenCost + N) · 2^-200`. -/
theorem slack_arith (Q N Kk : ℕ) (hK : 1 ≤ Kk) {la d V : ℝ≥0∞} (hla : la ≤ (2 : ℝ≥0∞)⁻¹ ^ 205)
    (hd1 : d ≤ 1) (hd : 16 * d ≤ 4) (hV : 16 * V ≤ 4) :
    (la + (1 + d) * la) + ((1 + d) * ((Q : ℝ≥0∞) + N) + Q * V) * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * (((Q + Kk : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      ((Q + Kk + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := by
  set u : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 205 with hu
  have h201 : (2 : ℝ≥0∞)⁻¹ ^ 201 = 16 * u := by
    rw [hu, inv_two_pow_split 201 4]; norm_num
  have h200 : (2 : ℝ≥0∞)⁻¹ ^ 200 = 32 * u := by
    rw [hu, inv_two_pow_split 200 5]; norm_num
  have h1 : la + (1 + d) * la ≤ 3 * u := by
    calc la + (1 + d) * la ≤ u + (1 + 1) * u := by gcongr
      _ = 3 * u := by ring
  have h2 : (1 + d) * ((Q : ℝ≥0∞) + N) * (16 * u) ≤ 20 * ((Q : ℝ≥0∞) + N) * u := by
    have : (1 + d) * 16 ≤ 20 := by
      calc (1 + d) * 16 = 16 + 16 * d := by ring
        _ ≤ 16 + 4 := by gcongr
        _ = 20 := by norm_num
    calc (1 + d) * ((Q : ℝ≥0∞) + N) * (16 * u) = ((1 + d) * 16) * ((Q : ℝ≥0∞) + N) * u := by ring
      _ ≤ 20 * ((Q : ℝ≥0∞) + N) * u := by gcongr
  have h3 : (Q : ℝ≥0∞) * V * (16 * u) ≤ 4 * (Q : ℝ≥0∞) * u := by
    calc (Q : ℝ≥0∞) * V * (16 * u) = (16 * V) * (Q : ℝ≥0∞) * u := by ring
      _ ≤ 4 * (Q : ℝ≥0∞) * u := by gcongr
  have h4 : 2 * (((Q + Kk : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤ ((Q + Kk : ℕ) : ℝ≥0∞) * u := by
    rw [div_eq_mul_inv, mul_left_comm]
    refine mul_le_mul_right ?_ _
    rw [ENNReal.inv_pow, show (2 : ℝ≥0∞) * 2⁻¹ ^ 256 = 2⁻¹ ^ 255 by rw [inv_two_pow_split 255 1, pow_one], hu]
    exact pow_le_pow_of_le_one (by simp) (ENNReal.inv_le_one.2 one_le_two) (by norm_num)
  have hnat : ((3 + 20 * (Q + N) + 4 * Q + (Q + Kk) : ℕ) : ℝ≥0∞) ≤ ((32 * (Q + Kk + N) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (show 3 + 20 * (Q + N) + 4 * Q + (Q + Kk) ≤ 32 * (Q + Kk + N) by omega)
  calc (la + (1 + d) * la) + ((1 + d) * ((Q : ℝ≥0∞) + N) + Q * V) * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * (((Q + Kk : ℕ) : ℝ≥0∞) / 2 ^ 256)
      = (la + (1 + d) * la) + ((1 + d) * ((Q : ℝ≥0∞) + N) * (16 * u) + (Q : ℝ≥0∞) * V * (16 * u)) +
          2 * (((Q + Kk : ℕ) : ℝ≥0∞) / 2 ^ 256) := by rw [h201]; ring
    _ ≤ 3 * u + (20 * ((Q : ℝ≥0∞) + N) * u + 4 * (Q : ℝ≥0∞) * u) + ((Q + Kk : ℕ) : ℝ≥0∞) * u := by
        gcongr
    _ = ((3 + 20 * (Q + N) + 4 * Q + (Q + Kk) : ℕ) : ℝ≥0∞) * u := by push_cast; ring
    _ ≤ ((32 * (Q + Kk + N) : ℕ) : ℝ≥0∞) * u := mul_le_mul_left hnat _
    _ = ((Q + Kk + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := by rw [h200]; push_cast; ring

/-- The P-part's right side regrouped as `Rp + cU · WC + digest payments`. -/
theorem regroup_ppart {L a b c d e f : ℝ≥0∞} (h : L ≤ a + (b + c + d) + e + f) : L ≤ (a + (b + d) + f) + c + e :=
  h.trans (le_of_eq (by ring))

/-- One sample's `Rp` in the form `A + C · failMass`. -/
theorem sample_arith {bE a k1 k2 cs la X px v fm d n N : ℝ≥0∞} (hk : k1 + k2 ≤ cs) (hX : X ≤ px + v * fm) :
    bE + (a + (k1 + k2 + la + X) + (1 + d) * ((n * fm + N * fm) + la)) ≤
      bE + a + cs + px + (la + (1 + d) * la) + ((1 + d) * (n + N) + v) * fm := by
  calc _ ≤ bE + (a + (cs + la + (px + v * fm)) + (1 + d) * ((n * fm + N * fm) + la)) := by gcongr
    _ = _ := by ring

/-- The last step: the main inequality with the slack. -/
theorem close_arith {bE O G G' cs P la d Cc e201 tw S R : ℝ≥0∞} (hG : G' ≤ G)
    (hslack : (la + (1 + d) * la) + Cc * e201 + tw ≤ S) (hmain : bE + O + G + cs + P + S ≤ R) :
    (bE + (O + G') + cs + P + (la + (1 + d) * la)) + Cc * e201 + tw ≤ R := by
  calc _ = (bE + O + G' + cs + P) + ((la + (1 + d) * la) + Cc * e201 + tw) := by ring
    _ ≤ (bE + O + G + cs + P) + S := by gcongr
    _ ≤ R := hmain

/-! ### The facts of a sample -/

section SampleFactsSec

open Completeness SeedModel Graph Assembly Reduce Internalize

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (steps : Message → Randomness)
  (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

/-- No FORS secret is known at the start of a sample's comparison. -/
theorem known_secret_none (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed))) (i : Index) (κ : FTree) (l : FLeaf) :
    known (Coordinate.fors i κ l 0) = none := by
  have h := (exposeR_known_support (fun c => c ∈ aboveList (truncateHash parameterOutput) prepared.1) _
    (knownOf (truncateHash parameterOutput) fixed) (knownOf (truncateHash parameterOutput) fixed) known
    (fun _ hc => hc) (fun _ _ h => h) (fun _ _ h => Or.inl h) hk).2
  cases hc : known (Coordinate.fors i κ l 0) with
  | none => rfl
  | some v =>
      rcases h _ v hc with h1 | h1
      · have := knownOf_known _ _ _ v h1
        simp [KnownCoordinate] at this
      · exact (mem_aboveList.1 h1).elim

/-- **The facts of a sample.** -/
theorem sampleFacts_sample (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    SampleFacts (ctxA parameterOutput fixed highs remaining prepared known ρ)
      (sampleData parameterOutput fixed highs remaining steps) (sampleModel parameterOutput highs)
      (failSet prepared.1) := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  set data := sampleData parameterOutput fixed highs remaining steps with hdata
  have hyp := stepHyp_sample parameterOutput fixed highs remaining prepared known ρ hprepared
  have hmsgP : ∀ (p : Pair) (call : DigestCall), IsMsgInput (pblk K.p data p call) := fun p call =>
    msgInput_digestInput _ _ _ _ _
  exact
    { hyp := hyp
      parse := fun p call => by rw [hyp.parse]; exact parse_msg_none _ _ _ (hmsgP p call)
      kind := fun p call => hyp.msg _ (hmsgP p call)
      digest := fun p call => by rw [hyp.digest]; exact hmsgP p call
      clean := fun p call => ForsPotential.prepared_clean parameterOutput fixed highs remaining prepared hprepared _
        (hmsgP p call)
      msg := hyp.msg
      fail := fun msg r digest budget s1 hprep out hout hnone =>
        finishRest_fail parameterOutput fixed highs remaining steps prepared hprepared _ msg r digest budget s1 hprep
          out hout hnone
      out := fun a i κ l => by
        rw [hyp.outgoing]
        cases a <;> simp [Address.outputCoordinate] }

end SampleFactsSec

/-! ### The route -/

open Completeness SeedModel Graph Assembly Reduce Internalize in
/-- **The SW route from the tail bound of the excess account.** -/
theorem detSW_of (hX : HTail) : DetSW := by
  intro hb adversary q hHb hab hcalls hbound hq hK hN70 hfairq ρ β δ cU m Pb b0c b0n hN hm0 hcU hFT hb0 hmain
  set q' := q - keygenCost with hq'
  have hsum : q' + keygenCost = q := by omega
  set x : ℝ := (q' : ℝ) / 2 ^ 128 with hx
  set wbar := H0.wbarOf q' with hwbar
  set Lmax := H0.LmaxOf q' with hLmax
  set r : ℝ := 1 / (2 ^ subtreeHeight * 2 ^ forsHeight) with hr
  set T : ℕ := ⌈3 * (q' : ℝ) * r / 2⌉₊ + 2 ^ 12 with hT
  have hT1 : 2 ^ 12 ≤ T := Nat.le_add_left _ _
  have hT3 : 3 * (q' : ℝ) * r ≤ 2 * T := by
    have h := Nat.le_ceil (3 * (q' : ℝ) * r / 2)
    rw [hT]
    push_cast
    linarith
  have hT4097 : (T : ℝ) ≤ 3 * (q' : ℝ) * r / 2 + 4097 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 3 * (q' : ℝ) * r / 2 by positivity)
    rw [hT]
    push_cast
    linarith
  have hfair : FairS wbar (q' + digestAttemptLimit) Lmax := H0.fair_of q' hfairq
  have hlam : lam Lmax 0 q' ≤ (2 : ℝ≥0∞)⁻¹ ^ 205 := lam_le_205 q'
  have hlam101 : lam Lmax 0 q' ≤ (2 : ℝ≥0∞)⁻¹ ^ 101 :=
    hlam.trans (pow_le_pow_of_le_one (by simp) (ENNReal.inv_le_one.2 one_le_two) (by norm_num))
  have hK1 : 1 ≤ keygenCost := by
    have := Nat.two_pow_pos (keptHeight topLayer)
    unfold keygenCost Prefix.keygenHashCost
    omega
  -- cap `δ` at `1/4` and drop an infinite `b0n` (it is multiplied by `δ = 0`)
  set δ' : ℝ := min δ (1 / 4) with hδ'
  set b0n' : ℝ≥0∞ := if b0n = ⊤ then 0 else b0n with hb0n'
  have hN' : SWNumeric ρ β δ' x cU := { hN with delta := le_min hN.delta hN.delta_lhs_le }
  have hδle : ENNReal.ofReal δ' ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hb0n_ne : b0n' ≠ ⊤ := by
    rw [hb0n']
    split_ifs with h
    · exact ENNReal.zero_ne_top
    · exact h
  have hδ0 : b0n = ⊤ → ENNReal.ofReal δ' = 0 := by
    intro ht
    have hδz : ENNReal.ofReal δ = 0 := by
      by_contra hne
      have h1 : ENNReal.ofReal δ * b0n = ⊤ := by rw [ht]; exact ENNReal.mul_top hne
      rw [h1, add_top] at hb0
      exact ENNReal.ofReal_ne_top (top_le_iff.1 hb0)
    exact le_antisymm (hδle.trans hδz.le) bot_le
  have hb0' : b0c + ENNReal.ofReal δ' * b0n' ≤ ENNReal.ofReal (β / 2 ^ 128) := by
    refine le_trans (add_le_add le_rfl ?_) hb0
    by_cases ht : b0n = ⊤
    · rw [hb0n', if_pos ht, mul_zero]
      exact bot_le
    · rw [hb0n', if_neg ht]
      exact mul_le_mul_left hδle _
  have hGle : ENNReal.ofReal δ' * ((q' : ℝ≥0∞) * startExcessG witnessNear wbar b0n' q') ≤
      ENNReal.ofReal δ * ((q' : ℝ≥0∞) * startExcessG witnessNear wbar b0n q') := by
    by_cases ht : b0n = ⊤
    · rw [hδ0 ht, zero_mul]
      exact bot_le
    · rw [hb0n', if_neg ht]
      exact mul_le_mul_left hδle _
  have hd1 : ENNReal.ofReal δ' ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (by norm_num))
  have hd16 : 16 * ENNReal.ofReal δ' ≤ 4 := by
    rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num]
    refine ENNReal.ofReal_le_ofReal ?_
    have := min_le_right δ (1 / 4)
    linarith
  have hb28 : subtreeHeight ≤ 28 := hHb ▸ totalHeight_le_28
  have hV16 : 16 * (ν * 2 ^ subtreeHeight) ≤ 4 := by
    calc 16 * (ν * 2 ^ subtreeHeight) = ν * 2 ^ (subtreeHeight + 4) := by rw [pow_add]; norm_num; ring
      _ ≤ ν * 2 ^ 128 := mul_le_mul_right (pow_le_pow_right₀ one_le_two (by omega)) _
      _ = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
      _ ≤ 4 := by norm_num
  have hrate : ν * ((signatureLimit : ℝ≥0∞) * revRate + ENNReal.ofReal m) ≤ ENNReal.ofReal (cU / 2 ^ 128) := by
    rw [SWRoute.revRate_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) hm0, ← nu_eq_ofReal', ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (signatureLimit : ℝ) * (1 / (2 ^ subtreeHeight * 2 ^ forsHeight)) + m ≤ cU := by
      rw [mul_one_div]
      exact hcU
    calc 1 / 2 ^ 128 * ((signatureLimit : ℝ) * (1 / (2 ^ subtreeHeight * 2 ^ forsHeight)) + m)
        ≤ 1 / 2 ^ 128 * cU := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = cU / 2 ^ 128 := by ring
  -- the bound of every sample
  have hsample : ∀ steps parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize (truncSign (Memo.memoAdv adversary) signatureLimit)) q
            (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)))) known
          prepared.2] ≤
        ((1 - budgetE ρ 0 q') + ((q' : ℝ≥0∞) * startExcessO wbar b0c q' +
            ENNReal.ofReal δ' * ((q' : ℝ≥0∞) * startExcessG witnessNear wbar b0n' q')) + coinSW q' +
            ENNReal.ofReal (x * Pb) + (lam Lmax 0 q' + (1 + ENNReal.ofReal δ') * lam Lmax 0 q')) +
          ((1 + ENNReal.ofReal δ') * ((q' : ℝ≥0∞) + signatureLimit) + (q' : ℝ≥0∞) * (ν * 2 ^ subtreeHeight)) *
            failMass (failSet prepared.1) := by
    intro steps parameterOutput fixed highs remaining prepared hprepared known hk
    set param := truncateHash parameterOutput with hparam
    set data := sampleData parameterOutput fixed highs remaining steps with hdata
    set model := sampleModel parameterOutput highs with hmodel
    set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hKdef
    set Fail := failSet prepared.1 with hFail
    set start : State := DebtState.start prepared.2 known with hstart
    set M := (internalize (truncSign (Memo.memoAdv adversary) signatureLimit)).main ⟨data.root, param⟩ with hM
    have hF := sampleFacts_sample parameterOutput fixed highs remaining steps prepared known ρ hprepared
    have hnr : NoRepeat M [] :=
      noRepeat_internalize_adversary _ (truncMemo_noRepeat adversary) _
    have hsb : SignBound M signatureLimit :=
      signBound_internalize_adversary _ _ (truncMemo_signBound adversary) _
    have hknown := known_secret_none parameterOutput fixed prepared known hk
    have hw1 : weightA K data.root start = 1 := weightA_start known K data.root
    have hpp := ppart_closed K data model wbar b0c b0n' δ' Fail Lmax T (ENNReal.ofReal (cU / 2 ^ 128))
      (ENNReal.ofReal m) hcalls hHb hF.parse hF.msg hF.digest hF.clean hF.fail hF.out q' hfair hb0n_ne hrate
      M hnr hsb known hknown hw1
    -- the excess account
    have hXS : ν * XS K data.root data wbar Fail model (ENNReal.ofReal m) M [] q' start [] [] 0 ≤
        ENNReal.ofReal (x * Pb) + (q' : ℝ≥0∞) * (ν * 2 ^ subtreeHeight) * failMass Fail := by
      by_cases hE : Fail = ∅
      · refine le_trans ?_ le_self_add
        have h := hX K data model wbar m Pb q' hFT rfl hHb hcalls hF.parse hF.kind hF.clean
          (fun msg r digest budget s1 hprep out hout hnone => hE ▸ hF.fail msg r digest budget s1 hprep out hout hnone)
          hF.out (q' + digestAttemptLimit) Lmax hfair (Nat.le_add_right _ _) hlam101 M hnr hsb known hknown
        rw [hE]
        exact h
      · obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.2 hE
        refine le_trans ?_ le_add_self
        have h1m : ENNReal.ofReal (1 - m) ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        calc ν * XS K data.root data wbar Fail model (ENNReal.ofReal m) M [] q' start [] [] 0
            ≤ ν * ((q' : ℝ≥0∞) * ENNReal.ofReal (1 - m)) :=
              mul_le_mul_right (XS_le_budget K data wbar Fail model m M [] q' start [] [] 0) _
          _ ≤ ν * ((q' : ℝ≥0∞) * 1) := by gcongr
          _ ≤ ν * ((q' : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ subtreeHeight * failMass Fail)) := by
              gcongr
              exact one_le_failMass hl
          _ = (q' : ℝ≥0∞) * (ν * 2 ^ subtreeHeight) * failMass Fail := by ring
    -- the coin
    have hcoin : coinPotK T q' + capC param data T q' start [] [] ≤ coinSW q' := by
      unfold coinSW
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add (coinPotK_le T q' hab hT4097) (capC_start_le param data prepared.2 known T q' hT1 hT3)
    refine le_trans (sample_boundSW hb (truncSign (Memo.memoAdv adversary) signatureLimit) q (by omega)
      parameterOutput fixed highs remaining steps prepared hprepared known hk ρ β δ' cU hN' b0c b0n' hb0'
      (((q' : ℝ≥0∞) * startExcessO wbar b0c q' +
          ENNReal.ofReal δ' * ((q' : ℝ≥0∞) * startExcessG witnessNear wbar b0n' q')) +
        ((coinPotK T q' + capC param data T q' start [] [] + lam Lmax 0 q') +
          ν * XS K data.root data wbar Fail model (ENNReal.ofReal m) M [] q' start [] [] 0) +
        (1 + ENNReal.ofReal δ') * (((q' : ℝ≥0∞) * failMass Fail + signatureLimit * failMass Fail) + lam Lmax 0 q'))
      (fun _ => regroup_ppart hpp)) ?_
    exact sample_arith hcoin hXS
  refine (det_of_samplesSW adversary q hbound _ _ hsample).trans ?_
  have hqcast : (q : ℝ≥0∞) = ((q' + keygenCost : ℕ) : ℝ≥0∞) := by rw [hsum]
  rw [hqcast]
  exact close_arith hGle (slack_arith q' signatureLimit keygenCost hK1 hlam hd1 hd16 hV16) hmain

end FORS.Security.SWRoute
