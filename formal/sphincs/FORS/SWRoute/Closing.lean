import FORS.SWRoute.ClosingReal
import FORS.SWRoute.NumericFacts
import FORS.CoverBound.NearOptionB
import FORS.SWRoute.ForecastCert
import FORS.Certificates.Closing

/-! **The certificate of the SW route and the three routes together.** A SW cover (`CoverSW`) is a
Poisson table, a near-mean certificate (for the contact coefficient), cover options, near options at
a baseline and entries `[q_a, q_b]` with a rate `ρ`, a digest decrement `β`, an arming bound `δ` and
one option of each kind. An entry is checked at its ends (`checkEntrySW`): the side conditions at
`q_b`, the digest payment `cthr_cover + δ cthr_near ≤ β / 2^128`, and the main inequality. Given the
route's statement `DetSW`, every budget of a checked chain has advantage at most `q / 2^127`
(`det_of_coverSW`), and `det_bitsF3` combines the small route up to `q_h`, a SW cover from `q_h + 1`
and the large route's covers from the SW cover's top. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenDebt ForsPotential H0

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

/-! ### The checker -/

/-- A SW entry: budgets `[qa, qb]`, the rate `ρ`, the digest decrement `β`, the arming bound `δ`, the
cap `m` of the own-leaf near forecast and its tail `Pb`, the index of its cover option, of its near
option and of its tail certificate. -/
abbrev EntrySW := ℕ × ℕ × ℚ × ℚ × ℚ × ℚ × ℚ × ℕ × ℕ × ℕ

/-- A SW cover certificate. -/
structure CoverSW where
  qtop : ℕ
  tab : PoisT
  opts : List Opt
  nopts : List OptNB
  tails : List TailCert
  entries : List EntrySW

/-- The check of one SW entry. -/
def checkEntrySW (b k a K N qtop : ℕ) (t : PoisT) (opts : List Opt) (nopts : List OptNB)
    (tails : List TailCert) : EntrySW → Bool
  | (qa, qb, ρ, β, δ, m, Pb, ic, inr, itl) =>
    match opts[ic]?, nopts[inr]?, tails[itl]? with
    | some o, some n, some tc =>
        decide (qa ≤ qb) && decide (qb ≤ qtop) && checkTail b k a t qb m tc Pb && checkNumSW ρ β δ ((qb : ℚ) / 2 ^ 128) (cUQ b a N m) &&
          decide (0 ≤ δ) && decide (0 ≤ o.cthr) && decide (0 ≤ n.cthr) &&
          decide (o.cthr + δ * n.cthr ≤ β / 2 ^ 128) && decide (0 ≤ o.B) && decide (0 ≤ n.B) &&
          decide (0 ≤ Pb) && swMainQ K N qa qb ρ δ o.B n.B Pb
    | _, _, _ => false

/-- Consecutive SW entries cover `[last, qtop]`. -/
def chainSW (b k a K N qtop : ℕ) (t : PoisT) (opts : List Opt) (nopts : List OptNB) (tails : List TailCert) :
    ℕ → List EntrySW → Bool
  | last, [] => decide (qtop < last)
  | last, e :: rest => decide (e.1 ≤ last) && checkEntrySW b k a K N qtop t opts nopts tails e &&
      chainSW b k a K N qtop t opts nopts tails (e.2.1 + 1) rest

/-- A SW cover of every budget `qstart ≤ q ≤ qtop`. -/
def checkCoverSW (H b k a K N qstart : ℕ) (c : CoverSW) : Bool :=
  decide (H = b) && decide (31 ≤ b + a) && decide ((H + k * a + 255) / 256 = 1) && checkRate H b N c.qtop c.tab && checkPT c.tab &&
    c.opts.all (checkOpt H b k a c.tab) && c.nopts.all (checkOptNB H b k a c.tab) &&
    chainSW b k a K N c.qtop c.tab c.opts c.nopts c.tails qstart c.entries

/-! ### Soundness of the checker -/

theorem chainSW_sound (b k a K N qtop : ℕ) (t : PoisT) (opts : List Opt) (nopts : List OptNB)
    (tails : List TailCert) :
    ∀ (entries : List EntrySW) (last : ℕ), chainSW b k a K N qtop t opts nopts tails last entries = true →
      ∀ q, last ≤ q → q ≤ qtop → ∃ e ∈ entries, e.1 ≤ q ∧ q ≤ e.2.1 ∧
        checkEntrySW b k a K N qtop t opts nopts tails e = true
  | [], last, h, q, hq, hq' => by
      simp only [chainSW, decide_eq_true_eq] at h
      omega
  | e :: rest, last, h, q, hq, hq' => by
      simp only [chainSW, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨he1, he2⟩, hrest⟩ := h
      by_cases hle : q ≤ e.2.1
      · exact ⟨e, List.mem_cons_self .., by omega, hle, he2⟩
      · obtain ⟨e', he', h1, h2, h3⟩ := chainSW_sound b k a K N qtop t opts nopts tails rest _ hrest q (by omega) hq'
        exact ⟨e', List.mem_cons_of_mem _ he', h1, h2, h3⟩

/-- What a checked entry gives. -/
theorem checkEntrySW_sound {b k a K N qtop : ℕ} {t : PoisT} {opts : List Opt} {nopts : List OptNB}
    {tails : List TailCert} {qa qb : ℕ} {ρ β δ m Pb : ℚ} {ic inr itl : ℕ}
    (h : checkEntrySW b k a K N qtop t opts nopts tails (qa, qb, ρ, β, δ, m, Pb, ic, inr, itl) = true) :
    ∃ o ∈ opts, ∃ n ∈ nopts, ∃ tc ∈ tails, qa ≤ qb ∧ qb ≤ qtop ∧ checkTail b k a t qb m tc Pb = true ∧ checkNumSW ρ β δ ((qb : ℚ) / 2 ^ 128) (cUQ b a N m) = true ∧
      0 ≤ δ ∧ 0 ≤ o.cthr ∧ 0 ≤ n.cthr ∧ o.cthr + δ * n.cthr ≤ β / 2 ^ 128 ∧ 0 ≤ o.B ∧ 0 ≤ n.B ∧
      0 ≤ Pb ∧ swMainQ K N qa qb ρ δ o.B n.B Pb = true := by
  rcases ho : opts[ic]? with _ | o <;> rcases hn : nopts[inr]? with _ | n <;>
    rcases htc : tails[itl]? with _ | tc <;>
    simp only [checkEntrySW, ho, hn, htc, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq,
      Bool.false_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h0'⟩, h0''⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨o, List.mem_of_getElem? ho, n, List.mem_of_getElem? hn, tc, List.mem_of_getElem? htc, h0, h0', h0'',
    h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ### One budget of a checked SW cover -/

theorem coinSW_le (q qb : ℕ) (hq : q ≤ qb) : coinSW q ≤ ENNReal.ofReal (coinQ qb : ℝ) := by
  unfold coinSW coinQ
  apply ENNReal.ofReal_le_ofReal
  have h : (q : ℝ) ≤ qb := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  push_cast
  have h1 : (q : ℝ) / 2 ^ 128 ≤ qb / 2 ^ 128 := by gcongr
  have h2 : ((q : ℝ) / 2 ^ 128) ^ 2 ≤ (qb / 2 ^ 128) ^ 2 := by gcongr
  linarith [div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 ^ 30),
    div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ 100)]

set_option maxHeartbeats 1000000 in
/-- **One budget of a checked SW cover**, from the route's statement. -/
theorem det_of_coverSW (hSW : DetSW) (hb0 : 0 < keptHeight topLayer) (H b k a K N qstart : ℕ)
    (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a)
    (hK : Prefix.keygenHashCost = K) (hN : signatureLimit = N) (hN70 : signatureLimit ≤ 2 ^ 70)
    (c : CoverSW) (hcov : checkCoverSW H b k a K N qstart c = true)
    (adversary : Adversary) (q : ℕ) (hbound : HasHashQueryBound adversary q) (hq127 : q < 2 ^ 127)
    (hKq : keygenCost ≤ q) (hq0 : qstart ≤ q - keygenCost) (hqt : q - keygenCost ≤ c.qtop) :
    forgeAdvantage adversary ≤ q / 2 ^ 127 := by
  simp only [checkCoverSW, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcov
  obtain ⟨⟨⟨⟨⟨⟨⟨hHb, hba⟩, hdc⟩, hr⟩, ht⟩, hopts⟩, hnopts⟩, hchain⟩ := hcov
  have hdc' : digestCalls = 1 := by
    have e : digestCalls = (H + k * a + 256 - 1) / 256 := by
      unfold digestCalls messageDigestBits hashOutputBits
      rw [hH, hk, ha]
    rw [e]
    generalize k * a = m at hdc ⊢
    omega
  set q' := q - keygenCost with hq'def
  obtain ⟨⟨qa, qb, ρ, β, δ, m, Pb, ic, inr, itl⟩, -, hqa, hqb, he⟩ :=
    chainSW_sound b k a K N c.qtop c.tab c.opts c.nopts c.tails c.entries qstart hchain q' hq0 hqt
  dsimp only at hqa hqb
  obtain ⟨o, ho, n, hn, tc, -, -, hqbt, htc, hnum, hδ, hoc, hnc, hpay, hoB, hnB, hPb, hmain⟩ :=
    checkEntrySW_sound he
  have htl : ForecastTail (m : ℝ) q' (Pb : ℝ) :=
    tailOK_of_check H b k a N c.qtop hH hb hk ha hN c.tab hr ht qa qb hqbt m Pb tc htc q' hqa hqb
  have hoc' := hopts o ho
  have hnc' := hnopts n hn
  -- the side conditions at `q'`
  have hnumR := checkNumSW_sound hnum
  have hxle : ((q' : ℕ) : ℝ) / 2 ^ 128 ≤ (((qb : ℚ) / 2 ^ 128 : ℚ) : ℝ) := by
    push_cast
    exact div_le_div_of_nonneg_right (by exact_mod_cast hqb) (by positivity)
  have hnum' : SWNumeric (ρ : ℝ) (β : ℝ) (δ : ℝ) (((q' : ℕ) : ℝ) / 2 ^ 128) (cUQ b a N m : ℝ) :=
    hnumR.mono (by positivity) hxle
  have hfair := fair_of_rate H b N c.qtop c.tab hr hH hb q' hqt
  have hcU : (signatureLimit : ℝ) / (2 ^ subtreeHeight * 2 ^ forsHeight) + (m : ℝ) ≤ (cUQ b a N m : ℝ) := by
    unfold cUQ; rw [hb, ha, hN]; push_cast; exact le_rfl
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  have hocR : (0 : ℝ) ≤ (o.cthr : ℝ) := by exact_mod_cast hoc
  have hncR : (0 : ℝ) ≤ (n.cthr : ℝ) := by exact_mod_cast hnc
  have hpayE : ENNReal.ofReal (o.cthr : ℝ) + ENNReal.ofReal (δ : ℝ) * ENNReal.ofReal (n.cthr : ℝ) ≤
      ENNReal.ofReal ((β : ℝ) / 2 ^ 128) := by
    rw [← ENNReal.ofReal_mul hδR, ← ENNReal.ofReal_add hocR (mul_nonneg hδR hncR)]
    apply ENNReal.ofReal_le_ofReal
    have := (Rat.cast_le (K := ℝ)).mpr hpay
    push_cast at this
    exact this
  refine hSW hb0 adversary q (by rw [hH, hb, hHb]) (by rw [hb, ha]; exact hba) hdc' hbound hq127 hKq hN70 hfair (ρ : ℝ) (β : ℝ) (δ : ℝ) _
    (m : ℝ) (Pb : ℝ) (ENNReal.ofReal (o.cthr : ℝ)) (ENNReal.ofReal (n.cthr : ℝ)) hnum' hcU htl hpayE ?_
  -- the main inequality
  have hρ1 : (1 : ℝ) ≤ (ρ : ℝ) := by linarith [hnum'.low]
  have hρ2 : (ρ : ℝ) ≤ 2 := hnum'.high
  have hq'R : ((q' : ℕ) : ℝ) ≤ spaceReal := by
    have h1 : q' ≤ 2 ^ 127 := by omega
    have : ((q' : ℕ) : ℝ) ≤ ((2 ^ 127 : ℕ) : ℝ) := by exact_mod_cast h1
    unfold spaceReal
    push_cast at this
    linarith [show (2 : ℝ) ^ 127 ≤ 2 ^ 128 by norm_num]
  have hsat := one_sub_budgetE_start_le hρ1 hρ2 q' hq'R
  have hC := startExcessO_le_opt H b k a N c.qtop c.tab o hr ht hoc' hH hb hk ha hN q' hqt _ le_rfl
  have hNe := startExcessG_near_le_optNB hH hb hk ha hN c.tab n hr ht hnc' q' hqt _ le_rfl
  have hcoin := coinSW_le q' qb hqb
  have hoB' : (0 : ℝ) ≤ (o.B : ℝ) := by exact_mod_cast hoB
  have hnB' : (0 : ℝ) ≤ (n.B : ℝ) := by exact_mod_cast hnB
  have hmainR : satUp (ρ : ℝ) ((qa : ℝ) / 2 ^ 128) + (qb : ℝ) * (o.B : ℝ) + (δ : ℝ) * ((qb : ℝ) * (n.B : ℝ)) +
      (coinQ qb : ℝ) + (qb : ℝ) / 2 ^ 128 * (Pb : ℝ) + ((qb : ℝ) + K + N) / 2 ^ 200 ≤
        2 * ((qa : ℝ) / 2 ^ 128) + (K : ℝ) / 2 ^ 127 := by
    unfold swMainQ at hmain
    rw [decide_eq_true_eq] at hmain
    have := (Rat.cast_le (K := ℝ)).mpr hmain
    unfold satUpQ at this
    unfold satUp
    push_cast at this ⊢
    exact this
  have hPbR : (0 : ℝ) ≤ (Pb : ℝ) := by exact_mod_cast hPb
  have hcoin0 : (0 : ℝ) ≤ (coinQ qb : ℝ) := by
    unfold coinQ; push_cast; positivity
  have hreal := sw_entry_real (q' : ℝ) (qa : ℝ) (qb : ℝ) (K : ℝ) (N : ℝ) (ρ : ℝ) (δ : ℝ) (o.B : ℝ) (n.B : ℝ)
    (o.B : ℝ) (n.B : ℝ) (by exact_mod_cast hqa) (by exact_mod_cast hqb) (Nat.cast_nonneg _) hρ1 hρ2 hδR le_rfl
    le_rfl hoB' hnB' (coinQ qb : ℝ) (coinQ qb : ℝ) le_rfl (Pb : ℝ) hPbR hmainR
  have hsat0 : 0 ≤ satUp (ρ : ℝ) (((q' : ℕ) : ℝ) / 2 ^ 128) := by
    have := one_sub_rpow_le_satUp hρ1 hρ2 (x := ((q' : ℕ) : ℝ) / 2 ^ 128) (by positivity)
      (by rw [div_le_one (by positivity)]; unfold spaceReal at hq'R; exact hq'R)
    have h0 : (1 - ((q' : ℕ) : ℝ) / 2 ^ 128) ^ (ρ : ℝ) ≤ 1 := by
      apply Real.rpow_le_one
      · rw [sub_nonneg, div_le_one (by positivity)]; unfold spaceReal at hq'R; exact hq'R
      · have : (0 : ℝ) ≤ ((q' : ℕ) : ℝ) / 2 ^ 128 := by positivity
        linarith
      · linarith
    linarith
  rw [← hq'def]
  have e1 : ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 =
      ENNReal.ofReal (((q' : ℝ) + K + N) / 2 ^ 200) := by
    rw [show keygenCost = K from hK, hN]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ← inv_pow, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have e2 : ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127 = ENNReal.ofReal (((q' : ℝ) + K) / 2 ^ 127) := by
    rw [show keygenCost = K from hK]
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have eC : ((q' : ℕ) : ℝ≥0∞) * ENNReal.ofReal (o.B : ℝ) = ENNReal.ofReal ((q' : ℝ) * (o.B : ℝ)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have eN : ENNReal.ofReal (δ : ℝ) * (((q' : ℕ) : ℝ≥0∞) * ENNReal.ofReal (n.B : ℝ)) =
      ENNReal.ofReal ((δ : ℝ) * ((q' : ℝ) * (n.B : ℝ))) := by
    rw [ENNReal.ofReal_mul hδR, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [e1, e2]
  calc (1 - budgetE (ρ : ℝ) 0 q') + (q' : ℝ≥0∞) * startExcessO (wbarOf q') (ENNReal.ofReal (o.cthr : ℝ)) q' +
        ENNReal.ofReal (δ : ℝ) * ((q' : ℝ≥0∞) *
          startExcessG witnessNear (wbarOf q') (ENNReal.ofReal (n.cthr : ℝ)) q') + coinSW q' +
        ENNReal.ofReal (((q' : ℕ) : ℝ) / 2 ^ 128 * (Pb : ℝ)) +
        ENNReal.ofReal (((q' : ℝ) + K + N) / 2 ^ 200)
      ≤ ENNReal.ofReal (satUp (ρ : ℝ) (((q' : ℕ) : ℝ) / 2 ^ 128)) + ENNReal.ofReal ((q' : ℝ) * (o.B : ℝ)) +
        ENNReal.ofReal ((δ : ℝ) * ((q' : ℝ) * (n.B : ℝ))) + ENNReal.ofReal (coinQ qb : ℝ) +
        ENNReal.ofReal (((q' : ℕ) : ℝ) / 2 ^ 128 * (Pb : ℝ)) +
        ENNReal.ofReal (((q' : ℝ) + K + N) / 2 ^ 200) := by
        rw [← eC, ← eN]
        gcongr
    _ = ENNReal.ofReal (satUp (ρ : ℝ) (((q' : ℕ) : ℝ) / 2 ^ 128) + (q' : ℝ) * (o.B : ℝ) +
        (δ : ℝ) * ((q' : ℝ) * (n.B : ℝ)) + (coinQ qb : ℝ) + (q' : ℝ) / 2 ^ 128 * (Pb : ℝ) +
        ((q' : ℝ) + K + N) / 2 ^ 200) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) hcoin0,
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hsat0 (by positivity)]
    _ ≤ ENNReal.ofReal (((q' : ℝ) + K) / 2 ^ 127) := ENNReal.ofReal_le_ofReal hreal

end FORS.Security.SWRoute

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

set_option maxRecDepth 100000 in
/-- The small-budget case of `det_bitsFH`, on its own. -/
theorem det_small_caseF (hb0 : 0 < keptHeight topLayer) (H b k a K N : ℕ) (hH : totalHeight = H)
    (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a)
    (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate H b N qh t = true) (ho : H0.checkOpt H b k a t o = true)
    (hon : H0.checkOptN H k a t on = true)
    (hsmall : checkSmallF H b a N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (q : ℕ) (hq1 : 1 ≤ q) (adversary : Adversary) (hbound : HasHashQueryBound adversary q)
    (hq127 : q < 2 ^ 127) (hs : q - keygenCost ≤ qh) :
    forgeAdvantage adversary ≤ q / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hpayR, hcheck⟩ := checkSmallF_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  set c : ℚ := (2 ^ b * on.En : ℚ) / 2 with hcdef
  set κ : ℚ := 2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) / (2 ^ b * 2 ^ a) with hκdef
  have hκR : (κ : ℝ) = 2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) / (2 ^ b * 2 ^ a) := by
    rw [hκdef]
    push_cast
    ring
  have hκ0 : 0 ≤ κ := by
    have hR : (0 : ℝ) ≤ (κ : ℝ) := by
      rw [hκR]
      have h1 : (ρ : ℝ) ≤ 2 := hnum.high
      have h2 : (0 : ℝ) ≤ (qh : ℝ) / 2 ^ 128 := by positivity
      have h3 : (0 : ℝ) ≤ (N : ℝ) / (2 ^ b * 2 ^ a) := by positivity
      linarith
    exact_mod_cast hR
  have hκ1 : κ ≤ 1 := by
    have hR : (κ : ℝ) ≤ 1 := by
      rw [hκR]
      linarith
    exact_mod_cast hR
  have hc2 : (0 : ℚ) ≤ κ * c := mul_nonneg hκ0 hc
  have hcheck' : (ρ : ℝ) + 2 ^ 128 * (o.B : ℝ) +
      (2 * (H0.scanM : ℝ) - 1) * (qh : ℝ) / ((H0.scanM : ℝ) * 2 ^ 129) +
      qh * ((κ * c : ℚ) : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
    rw [Rat.cast_mul, hκR, ← H0.scanMb_eq H b hH hb]
    refine le_of_eq_of_le ?_ hcheck
    ring
  have hx : ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
  have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
    numeric_monoF hnum hx (by positivity)
  have hκq : 2 - (ρ : ℝ) + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ (κ : ℝ) := by
    have he : (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) =
        (N : ℝ) / (2 ^ b * 2 ^ a) := by
      rw [hb, ha, hN]
      field_simp
    rw [hκR, he]
    linarith
  refine le_trans (det_smallF hb0 adversary q hbound (by omega) (ρ : ℝ) hnum' κ hκ0 hκ1 hκq
    H b k a N hH hb hk ha hN t o on hpt qh hrt hs ho hon hcthr) ?_
  exact small_closeFF q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (κ * c) hB hc2 hcheck'

set_option maxRecDepth 100000 in
/-- The large-budget case of `det_bitsFH`, from any start `qs` of the chain of covers. -/
theorem det_large_caseF (hb0 : 0 < keptHeight topLayer) (H b k a K N : ℕ) (hH : totalHeight = H)
    (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a)
    (hK : Prefix.keygenHashCost = K) (hN : signatureLimit = N) (hN70' : signatureLimit ≤ 2 ^ 70)
    (qs : ℕ) (covers heavy : List H0.CoverW) (hcov : checkCoversH H b k a K N qs covers heavy = true)
    (q : ℕ) (adversary : Adversary) (hbound : HasHashQueryBound adversary q)
    (hq127 : q < 2 ^ 127) (hs : qs ≤ q - keygenCost) (hKq : keygenCost ≤ q) :
    forgeAdvantage adversary ≤ q / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  have hkg : keygenCost = K := hK
  have e1 : (q - keygenCost) + Prefix.keygenHashCost = q - keygenCost + keygenCost :=
    rfl
  rcases checkCoversH_sound H b k a K N heavy covers qs hcov (q - keygenCost)
    hs (by rw [← hkg]; omega) with ⟨cover, -, qs', hcv, hqs, hqt⟩ | ⟨cover, -, qs', hcv, hqs, hqt⟩
  · have hcovb := H0.h0W_bound_of_cover H b k a K N qs' cover hcv hH hb hk ha hK hN (q - keygenCost) hqs hqt
    have hfairq := H0.fair_of_cover H b k a K N qs' cover hcv hH hb (q - keygenCost) hqt
    have h := det_largeW hb0 hN70' adversary q hbound hq127 hKq hfairq (by
      rw [e1] at hcovb
      exact hcovb)
    refine le_trans h (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat]
  · have hcovb := H0.h0H_bound_of_cover H b k a K N qs' cover hcv hH hb hk ha hK hN (q - keygenCost) hqs hqt
    have hfairq := H0.fair_of_coverH H b k a K N qs' cover hcv hH hb (q - keygenCost) hqt
    have h := det_largeH hb0 adversary q hbound hq127 hKq (H0.wbarH (q - keygenCost))
      (H0.LmaxOf (q - keygenCost)) (H0.fair_ofH (q - keygenCost) hfairq) (lam_start_leF (q - keygenCost)) (by
      rw [e1] at hcovb
      exact hcovb)
    refine le_trans h (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **127 bits for the deterministic signer with three routes**: the small route up to `qh`, a checked
SW cover of `[qh + 1, sw.qtop]` (given the SW route's statement), and a checked chain of light, then
heavy, covers of the large budgets from `sw.qtop + 1`. -/
theorem det_bitsF3 (hSW : SWRoute.DetSW) (hb0 : 0 < keptHeight topLayer) (H b k a K N : ℕ)
    (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a)
    (hK : Prefix.keygenHashCost = K) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate H b N qh t = true) (ho : H0.checkOpt H b k a t o = true)
    (hon : H0.checkOptN H k a t on = true)
    (hsmall : checkSmallF H b a N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (sw : SWRoute.CoverSW) (hsw : SWRoute.checkCoverSW H b k a K N (qh + 1) sw = true)
    (covers heavy : List H0.CoverW) (hcov : checkCoversH H b k a K N (sw.qtop + 1) covers heavy = true) :
    HasClassicalSecurityBits 127 := by
  have hN70 : signatureLimit ≤ 2 ^ 70 := by
    obtain ⟨-, -, hN70, -⟩ := checkSmallF_sound hsmall
    exact hN ▸ hN70
  intro q hq1 adversary hbound
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hq127 : q < 2 ^ 127 := Nat.lt_of_not_le hbig
  by_cases hs : q - keygenCost ≤ qh
  · exact det_small_caseF hb0 H b k a K N hH hb hk ha hN qh ρ t o on hpt hrt ho hon hsmall q hq1
      adversary hbound hq127 hs
  · by_cases hm : q - keygenCost ≤ sw.qtop
    · have hKq : keygenCost ≤ q := by
        have : 1 ≤ keygenCost := one_le_keygenCostF
        omega
      have h := SWRoute.det_of_coverSW hSW hb0 H b k a K N (qh + 1) hH hb hk ha hK hN hN70 sw hsw adversary q hbound
        hq127 hKq (by omega) hm
      refine le_trans h (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat]
    · have hKq : keygenCost ≤ q := by
        have : 1 ≤ keygenCost := one_le_keygenCostF
        omega
      exact det_large_caseF hb0 H b k a K N hH hb hk ha hK hN hN70 (sw.qtop + 1) covers heavy hcov q
        adversary hbound hq127 (by omega) hKq

end FORS.Security.ForsPotential
