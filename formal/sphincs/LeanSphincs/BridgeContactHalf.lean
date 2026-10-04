import LeanSphincs.BridgeContactBound

/-! **A4b with the near term halved.** The product potential `(C_F + y 2^-128) · potNear(y)` of
`BridgeContactB` charges every remaining query both as a FORS query making a contact and as a
digest query raising `potNear`, so its start value is quadratic, `y² 2^-128 H`. One query is only
one of the two: the refined potential

  `ψ(y) = C_F · potNear(y) + 2^-128 · Σ_{j < y} potNear(j)`

pays a contact made with `j` queries left by `potNear(j)` only. A new pair moves every level down
by one, an ordinary query keeps every level and adds `2^-128` contacts on average, which the top
level of the sum pays, and a signing call keeps every level in expectation: the signing lemmas of
`BridgeForsGeneric` hold with the forecast level decoupled from the run's budget. At the start
`C_F = 0` and the sum is at most `y (y (H / 2 + φ) + N φ)`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Signing at a decoupled level -/

/-- The bound for one signing outcome with the gate and the signature limit: zero once the gate is
on or no signature is left. -/
noncomputable def canonL (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞)
    (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (gate : State → Prop) (m : Message) (s : State)
    (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (K : ℕ)
    (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  if gate s ∨ signatureLimit ≤ L.length then 0
  else canonG parameter data W wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) K out

section SignLevel

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ) (m : Message)

/-- **The potential after one signing outcome, at any level.** The bound of `sign_pointG` with
the level `K` of the bound free of the run's budget. -/
theorem sign_pointG_level (hW : WitnessProps W) {gate : State → Prop}
    (hgate : ∀ s s' : State, Extends s s' → gate s → gate s')
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hD : DInv R d) (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' K : ℕ} (hk : k' ≤ K) :
    potG parameter data W wbar b0 Fail gate out.2 (newPairs parameter data m s out.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d out) k' ≤
      canonL parameter data W wbar b0 Fail gate m s P L d K out := by
  unfold canonL
  obtain ⟨_, hP', _, _, hview⟩ := sign_params tg initial model Fail Qtot hparse hfail attempts budget
    s P d R hprep hP hD hC out hout r hr
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    attempts budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  unfold potG
  by_cases hcase : gate out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [if_pos hcase]; exact bot_le
  rw [if_neg hcase]
  have hreal : ¬gate s := fun h => hcase (Or.inl (hgate s out.2 hext h))
  have hlen : L.length < signatureLimit := by
    have := hcase
    simp only [List.length_append, List.length_singleton, not_or, not_lt] at this
    omega
  rw [if_neg (by push_neg; exact ⟨hreal, hlen⟩)]
  have hn : signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length = signatureLimit - (L.length + 1) := by simp
  rw [hn]
  set n := signatureLimit - (L.length + 1) with hndef
  have hnotnew : ∀ q ∈ P, q ∉ newPairs parameter data m s out.2 := by
    intro q hq hnew
    obtain ⟨_, h0, _⟩ := (mem_newPairs parameter data m s).1 hnew
    obtain ⟨u, hu, _⟩ := (hP.mem q).1 hq
    rw [h0] at hu; cases hu
  unfold coreG canonG
  rw [List.map_append, List.sum_append]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u0, u1, hnew, _, h0, hl, h1, hs0, _, hfl, hsig⟩ |
        ⟨_, _, _, _, hnew, _⟩
    · unfold newPairs; rw [hnew]; simp
    · have hs1 : s.cache (blk parameter data m ρ 1) = none := hP.first (m, ρ) hs0
      have hv : pview parameter data out.2 (m, ρ) = viewOf u0 u1 := pview_of_cached h0 h1
      have hlist : newPairs parameter data m s out.2 = [(m, ρ)] := by
        unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
      rw [hlist]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      refine le_trans ?_ (freshNewWeight_ge hr hs1 h0 hl h1 (fun v => if v.1 ∈ Fail then 1 else 0))
      unfold candG
      rw [hv]
      split_ifs with hu hF hF'
      · exact le_rfl
      · exfalso
        rcases r with _ | sig
        · exact hF (hfl rfl)
        · exact not_unsigned_signed (m := m) (L := L) (sig := sig) (by rw [hsig sig rfl]; exact hu)
      · exact bot_le
      · exact le_rfl
    · unfold newPairs; rw [hnew]; simp
  · refine List.sum_le_sum fun q hq => ?_
    unfold candG
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [if_pos hU', if_pos hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueG
        rw [hview q hq, List.erase_append_right _ (hnotnew q hq),
          coinItems_after (P.erase q) fun q' hq' => hview q' (List.mem_of_mem_erase hq')]
        refine post_term_leO hw (hW _) _ n _ hk _ fun J => ?_
        refine upper_pointO hw (hW _) hP (· = q) out r hr Fail hshape (fun sig hsig _ heq => ?_) J
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [if_neg hU']
      exact bot_le
  · refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueG
    rw [coinItems_after P hview]
    refine post_term_leO hw (excessW_props hW hb0) _ n _ hk _ fun J => ?_
    exact upper_pointO hw (excessW_props hW hb0) hP (fun _ => False) out r hr Fail hshape (fun _ _ _ h => h) J

/-- **The signing step in expectation, at any level.** The bound of `sign_expectG` for a forecast
level `K` free of the run's budget: averaged over a signing call run with any budget, the bound
at level `K` is at most the potential at level `K` before the call. -/
theorem sign_expectG_level (hW : WitnessProps W) (gate : State → Prop)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (attempts budget K : ℕ) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m) (d : Multiset View) (hP : PInv parameter data s P)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        canonL parameter data W wbar b0 Fail gate m s P L d K out ≤
      potG parameter data W wbar b0 Fail gate s P L d K := by
  unfold canonL
  by_cases hcase : gate s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬gate s ∧ L.length < signatureLimit := by push_neg at hcase; exact hcase
  have hlen := hcase'.2
  unfold potG
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ call, model.parse (blk parameter data m ρ call) = none := fun ρ call => hparse (m, ρ) call
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  have hmass : ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] ≤ 1 :=
    tsum_probOutput_le_one
  have hFN := loop_bound_fresh tg initial model parameter data m hparse' s hnob1 hlandb1
    (fun v => if v.1 ∈ Fail then 1 else 0) attempts budget s (related_self parameter data m s)
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (W (pview parameter data s q))
          (· = q) out J) K (restItems parameter data m s L (P.erase q))) else 0) ≤
      candG parameter data W wbar Fail s P L d (n + 1) K q := by
    intro q _
    unfold candG
    split_ifs
    · rw [ENNReal.tsum_mul_right, mul_one]; exact hmass
    · unfold candValueG
      rw [creations_perm (virtualOnce_perm' wbar (n + 1) d) K _ _ (coinItems_perm parameter data m s L hm _)]
      have h := term_expectO tg initial model hparse' hfair (hW (pview parameter data s q)) hP (· = q)
        attempts budget K hcount (restItems parameter data m s L (P.erase q)) (n := n) (d := d)
      rwa [← erase_eq_filter' hP.nodup q] at h
    · simp
  have hH := term_expectO tg initial model (n := n) (d := d) hparse' hfair (excessW_props hW hb0) hP
    (fun _ => False) attempts budget K hcount (restItems parameter data m s L P)
  rw [filter_false'] at hH
  have hHv : hValueG parameter data W wbar b0 s P L d (n + 1) K =
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excessW W b0) (n + 1) J d) K
        (msgItems parameter data m s P ++ restItems parameter data m s L P) := by
    unfold hValueG
    exact creations_perm (virtualOnce_perm' wbar (n + 1) d) K _ _ (coinItems_perm parameter data m s L hm _)
  unfold canonG coreG
  simp only [mul_add, ENNReal.tsum_add]
  rw [tsum_list_sum]
  have hφ : freshAvg Finset.univ (fun v : View => if v.1 ∈ Fail then (1 : ℝ≥0∞) else 0) = failMass Fail := rfl
  rw [hφ] at hFN
  calc _ ≤ failMass Fail + (P.map (candG parameter data W wbar Fail s P L d (n + 1) K)).sum +
        (K * hValueG parameter data W wbar b0 s P L d (n + 1) K + K * failMass Fail) +
          n * failMass Fail := by
        refine add_le_add (add_le_add (add_le_add hFN (List.sum_le_sum hT)) (add_le_add ?_ ?_)) ?_
        · simp only [mul_left_comm _ (K : ℝ≥0∞), ENNReal.tsum_mul_left]
          rw [hHv]
          exact mul_le_mul_left' hH _
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
    _ = _ := by push_cast; ring

end SignLevel

/-! ### Finite sums under expectations -/

omit [Params] in
theorem pairE_range_sum (n : ℕ) (F : HashOutput → HashOutput → ℕ → ℝ≥0∞) :
    pairE (fun a b => ∑ j ∈ Finset.range n, F a b j) = ∑ j ∈ Finset.range n, pairE (fun a b => F a b j) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact pairE_const 0
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [pairE_add, ih]

omit [Params] in
theorem tsum_range_sum {β : Type} (w : β → ℝ≥0∞) (n : ℕ) (f : β → ℕ → ℝ≥0∞) :
    ∑' x, w x * ∑ j ∈ Finset.range n, f x j = ∑ j ∈ Finset.range n, ∑' x, w x * f x j := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, mul_add, ENNReal.tsum_add, ih]

/-! ### The refined potential -/

section DefsH

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- **The refined product potential** of A4b: the contacts times the near potential, plus the
contact rate times the near potentials at every lower level. -/
noncomputable def psiH : Potential := fun s P L d _ budget =>
  (contacts parameter K s).card * potN parameter data wbar Fail s P L d budget +
    contactRate * ∑ j ∈ Finset.range budget, potN parameter data wbar Fail s P L d j

end DefsH

/-! ### The four steps -/

section StepsH

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A new pair moves the near potential down by one level. -/
theorem potN_newPair (hw : wbar ≤ 1) {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (j : ℕ) :
    pairE (fun u0 u1 => potN parameter data wbar Fail (withPair parameter data s p u0 u1) (addPair parameter P p u0)
      L d j) ≤ potN parameter data wbar Fail s P L d (j + 1) := by
  unfold potN potG
  by_cases hL : False ∨ signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  · simp only [if_neg hL]
    have h := coreG_newPair wbar 0 Fail witnessNear_props hw ENNReal.zero_ne_top hP hp0 L d
      (signatureLimit - L.length) j
    rwa [add_zero] at h

/-- **A new pair.** -/
theorem psiH_newPair (hw : wbar ≤ 1) (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) :
    NewPairPays parameter data Qtot initial model (psiH parameter data K wbar Fail) := by
  intro budget s P L d R hb hB p hp0
  have hp1 := hB.pinv.first p hp0
  simp only [psiH]
  have hc : ∀ a b, ((contacts parameter K (withPair parameter data s p a b)).card : ℝ≥0∞) =
      (contacts parameter K s).card := fun a b => by rw [contacts_withPair parameter data K model hB.cinv hparse hp0 hp1]
  simp only [hc]
  rw [pairE_add, pairE_const_mul, pairE_const_mul, pairE_range_sum]
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine add_le_add (mul_le_mul_left' (potN_newPair parameter data wbar Fail hw hB.pinv hp0 L d y) _)
    (mul_le_mul_left' ?_ _)
  rw [Finset.sum_range_succ']
  exact le_trans (Finset.sum_le_sum fun j _ => potN_newPair parameter data wbar Fail hw hB.pinv hp0 L d j)
    le_self_add

/-- **Any other ordinary query.** -/
theorem psiH_ordinary (hw : wbar ≤ 1) (hrows : FtsRows parameter model) :
    OrdinaryPays parameter data Qtot initial model (psiH parameter data K wbar Fail) := by
  intro budget s P L d R hb hB x hnew
  simp only [psiH]
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set Q := potN parameter data wbar Fail s P L d y with hQ
  set S := ∑ j ∈ Finset.range y, potN parameter data wbar Fail s P L d j with hS
  set c : ℝ≥0∞ := ((contacts parameter K s).card : ℝ≥0∞) with hcdef
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      ((contacts parameter K r.2).card : ℝ≥0∞) * potN parameter data wbar Fail r.2 P L d y +
          contactRate * ∑ j ∈ Finset.range y, potN parameter data wbar Fail r.2 P L d j ≤
        (c + ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞)) * Q + contactRate * S := by
    intro r hr
    have hext := ordinaryStep_extends model x s r hr
    obtain ⟨_, hview⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hB.pinv
    have hgrow : ∀ j, potN parameter data wbar Fail r.2 P L d j ≤ potN parameter data wbar Fail s P L d j :=
      fun j => potG_grow wbar 0 Fail witnessNear_props gate_false_mono hw ENNReal.zero_ne_top hext hview L d le_rfl
    refine add_le_add (mul_le_mul' ?_ (hgrow y)) (mul_le_mul_left' (Finset.sum_le_sum fun j _ => hgrow j) _)
    rw [hcdef, add_comm]
    exact_mod_cast Finset.card_le_card_sdiff_add_card
  have hmean := ordinary_contacts_mean (K := K) hrows x s hB.cinv
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ((c + ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞)) * Q + contactRate * S) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_left' (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = ((∑' r, Pr[= r | ordinaryStep model x s.known s]) * c +
          ∑' r, Pr[= r | ordinaryStep model x s.known s] *
            ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞)) * Q +
          (∑' r, Pr[= r | ordinaryStep model x s.known s]) * (contactRate * S) := by
        simp only [add_mul, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← mul_assoc]
    _ ≤ (1 * c + contactRate) * Q + 1 * (contactRate * S) := by
        gcongr
        · exact tsum_probOutput_le_one
        · exact hmean
        · exact tsum_probOutput_le_one
    _ = c * Q + contactRate * (S + Q) := by ring
    _ ≤ c * potN parameter data wbar Fail s P L d (y + 1) +
          contactRate * ∑ j ∈ Finset.range (y + 1), potN parameter data wbar Fail s P L d j := by
        rw [Finset.sum_range_succ]
        gcongr
        exact potG_mono wbar 0 Fail witnessNear_props _ hw ENNReal.zero_ne_top s P L d (Nat.le_succ y)

/-- **A signing call** on a fresh message. Every level of the near potential is kept in
expectation, and the cost of the call only drops levels. -/
theorem psiH_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hQ : Qtot + digestAttemptLimit ≤ Cmax) :
    SignPays parameter data Qtot tg initial model (psiH parameter data K wbar Fail) := by
  intro budget s P L d R hB m hm
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hB.count m; omega
  set c : ℝ≥0∞ := ((contacts parameter K s).card : ℝ≥0∞) with hcdef
  set canon : ℕ → Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun k o1 =>
    canonL parameter data witnessNear wbar 0 Fail (fun _ => False) m s P L d k o1 with hcanon
  have hse : ∀ k, ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit)
      budget s] * canon k o1 ≤ potN parameter data wbar Fail s P L d k := fun k =>
    sign_expectG_level tg initial model parameter data wbar 0 Fail m witnessNear_props (fun _ => False) hparse hfair
      ENNReal.zero_ne_top digestAttemptLimit budget k s P L hm d hB.pinv hcount
  have hpt : ∀ o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit)
      budget s), o1.1.1.elim 0 (fun r => psiH parameter data K wbar Fail o1.2 (newPairs parameter data m s o1.2 ++ P)
        (L ++ [⟨m, r⟩]) (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
        c * canon budget o1 + contactRate * ∑ j ∈ Finset.range budget, canon j o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => exact bot_le
    | some r =>
        simp only [Option.elim, psiH]
        have hcon := (interp_contacts_avoid (K := K) tg initial hrows _ (avoids_loopF parameter data m _)
          budget s hB.cinv o1 ho1).2
        rw [hcon]
        have hpoint : ∀ k' K', k' ≤ K' → potN parameter data wbar Fail o1.2 (newPairs parameter data m s o1.2 ++ P)
            (L ++ [⟨m, r⟩]) (discAfter parameter data m s d o1) k' ≤ canon K' o1 := fun k' K' hk =>
          sign_pointG_level tg initial model parameter data wbar 0 Fail Qtot m witnessNear_props gate_false_mono
            hparse (hfail m) hfair.le_one ENNReal.zero_ne_top digestAttemptLimit budget s P L d R hB.prep hB.pinv
            hB.dinv hB.count o1 ho1 r hres hk
        refine add_le_add (mul_le_mul_left' (hpoint _ _ (Nat.sub_le _ _)) _) (mul_le_mul_left' ?_ _)
        calc _ ≤ ∑ j ∈ Finset.range (budget - traceCost o1.1.2.2.1), canon j o1 :=
              Finset.sum_le_sum fun j _ => hpoint j j le_rfl
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.sub_le _ _))
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit)
        budget s] * (c * canon budget o1 + contactRate * ∑ j ∈ Finset.range budget, canon j o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit)
          budget s)
        · exact mul_le_mul_left' (hpt o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = c * ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit)
          budget s] * canon budget o1 +
        contactRate * ∑ j ∈ Finset.range budget, ∑' o1, Pr[= o1 | interp tg initial model
          (signCostSourceLoop parameter data m digestAttemptLimit) budget s] * canon j o1 := by
        rw [← tsum_range_sum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun o1 => ?_
        ring
    _ ≤ _ := add_le_add (mul_le_mul_left' (hse budget) _)
        (mul_le_mul_left' (Finset.sum_le_sum fun j _ => hse j) _)

/-- **The end of the game.** A valid finished game with A4b has a contact and a near-covered
candidate. -/
theorem psiH_final (hw : wbar ≤ 1) : FinalPays parameter data Qtot initial model (psiH parameter data K wbar Fail)
    (finalB parameter data K) := by
  intro budget s P L d R hB forgery verified
  simp only [finalB, Option.elim, psiH]
  split_ifs with hcase
  swap
  · exact bot_le
  obtain ⟨hvalid, i, t, l, hgr, m, ρ, digest, hdig, hland, hunsigned, hidx, -, hnear⟩ := hcase
  -- a contact
  have hc1 : (1 : ℝ≥0∞) ≤ (contacts parameter K s).card := by
    obtain ⟨secret, hmem⟩ := mem_contacts_of_GR parameter K hgr
    exact_mod_cast Finset.card_pos.2 ⟨_, hmem⟩
  -- the near-covered candidate
  set q : Pair := (m, ρ) with hq
  unfold HiddenBridge.cachedDigest at hdig
  have hpot : (1 : ℝ≥0∞) ≤ potN parameter data wbar Fail s P L d budget := by
    cases h0 : s.cache (pblk parameter data q 0) with
    | none =>
        have h0' : s.cache (tweakableHashInput parameter (.message 0) (messageDigestPayload data.root m ρ)) = none := h0
        rw [h0'] at hdig; cases hdig
    | some a =>
        cases h1 : s.cache (pblk parameter data q 1) with
        | none =>
            have h0' : s.cache (tweakableHashInput parameter (.message 0)
                (messageDigestPayload data.root m ρ)) = some a := h0
            have h1' : s.cache (tweakableHashInput parameter (.message 1)
                (messageDigestPayload data.root m ρ)) = none := h1
            rw [h0', h1'] at hdig; cases hdig
        | some b =>
            have h0' : s.cache (tweakableHashInput parameter (.message 0)
                (messageDigestPayload data.root m ρ)) = some a := h0
            have h1' : s.cache (tweakableHashInput parameter (.message 1)
                (messageDigestPayload data.root m ρ)) = some b := h1
            rw [h0', h1'] at hdig
            have hdig' : truncateMessageDigest a b = digest := by simpa using hdig
            subst hdig'
            have hlanded : LandedIn parameter data s q :=
              ⟨a, h0, by rwa [Completeness.digestIndex_truncate] at hland⟩
            have hqP := (hB.pinv.mem q).2 hlanded
            have hv : pview parameter data s q = Lifetime.localDigestView (truncateMessageDigest a b) := by
              simp only [pview, h0, h1, Option.elim, viewOf]
            unfold potN potG
            rw [if_neg (by
              rintro (h | h)
              · exact h
              · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
            unfold coreG
            refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP))
              (le_self_add.trans le_self_add))
            unfold candG
            rw [if_pos (show Unsigned L q from hunsigned)]
            split_ifs
            · exact le_rfl
            · unfold candValueG
              calc (1 : ℝ≥0∞) ≤ witnessNear (pview parameter data s q) d := by
                    unfold witnessNear
                    rw [hv]
                    exact_mod_cast nearCount_pos hB.dinv _ t (fun other hother => by
                      rw [hidx]; exact hnear other hother)
                _ ≤ virtualOnce Finset.univ wbar (witnessNear (pview parameter data s q))
                      (signatureLimit - L.length) (coinItems parameter data s L (P.erase q)) d :=
                    base_le_virtualOnce Finset.univ_nonempty hw (witnessNear_props _).1 (witnessNear_props _).2.1
                      (witnessNear_props _).2.2 _ _ d
                _ ≤ _ := creations_mono_count (k := 0) Finset.univ_nonempty landing_le_one
                      (virtualOnce_cons_le' wbar hw (witnessNear_props _) _ d) (virtualOnce_perm' wbar _ d)
                      (Nat.zero_le _) _
  calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
    _ ≤ ((contacts parameter K s).card : ℝ≥0∞) * potN parameter data wbar Fail s P L d budget :=
        mul_le_mul' hc1 hpot
    _ ≤ _ := le_self_add

end StepsH

/-! ### The bound -/

section BoundH

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The start of the refined potential: no contacts, and the near potential at every level. -/
theorem psiH_start (known : Knowledge Coordinate) (total : ℕ) :
    psiH parameter data K wbar Fail (DebtState.start initial known) [] [] 0 [] total =
      contactRate * ∑ j ∈ Finset.range total,
        ((j : ℝ≥0∞) * (startNear wbar j + failMass Fail) + signatureLimit * failMass Fail) := by
  simp only [psiH, potN_start]
  have : contacts parameter K (DebtState.start initial known) = ∅ := by
    unfold contacts
    rfl
  rw [this, Finset.card_empty, Nat.cast_zero, zero_mul, zero_add]

/-- **Theorem (b), refined.** In the lazy run of the rest of the game of an adversary that never
repeats a message, the probability that the game finishes with a valid transcript and A4b holds is
at most `2^-128 Σ_{j < total} potNear_j(start)`. -/
theorem a4b_bound_half (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (hfair : Fair wbar (total + digestAttemptLimit))
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[A4bRun parameter data K | interp tg initial model (advProg parameter data M []) total
        (DebtState.start initial known)] ≤
      contactRate * ∑ j ∈ Finset.range total,
        ((j : ℝ≥0∞) * (startNear wbar j + failMass Fail) + signatureLimit * failMass Fail) := by
  have h := final_le_start parameter data tg initial model hparse hkind hrows hclean hcleanF Fail hfail total
    (G := finalB parameter data K) (fun _ _ => rfl) (fun o R s x u hx => finalB_store o R s x u hx)
    (psiH_newPair parameter data K wbar Fail total initial model hfair.le_one hparse)
    (psiH_ordinary parameter data K wbar Fail total initial model hfair.le_one hrows)
    (psiH_sign parameter data K wbar Fail total tg initial model hparse hrows hfail hfair le_rfl)
    (psiH_final parameter data K wbar Fail total initial model hfair.le_one) M hnr known
  rw [psiH_start] at h
  rw [probEvent_eq_tsum_ite]
  refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) h
  split_ifs with hE
  · obtain ⟨outcome, hres, hvalid, ha⟩ := hE
    simp only [finalB, hres, Option.elim, if_pos (And.intro hvalid ha), mul_one, le_refl]
  · exact bot_le

end BoundH

/-! ### The start sum -/

section StartSum

/-- The near forecast at the start grows with the number of future pairs. -/
theorem startNear_mono {wbar : ℝ≥0∞} (hw : wbar ≤ 1) {j k : ℕ} (hjk : j ≤ k) :
    startNear wbar j ≤ startNear wbar k := by
  unfold startNear
  exact creations_mono_count Finset.univ_nonempty landing_le_one
    (virtualOnce_cons_le' wbar hw (excessW_props witnessNear_props ENNReal.zero_ne_top) signatureLimit 0)
    (virtualOnce_perm' wbar signatureLimit 0) hjk []

/-- **The start sum.** With `startNear y ≤ 2h`, the near potentials at the levels below `y` sum
to at most `y (y (h + φ) + N φ)`: the levels average `y / 2`. -/
theorem start_sum_le {wbar : ℝ≥0∞} (hw : wbar ≤ 1) (y : ℕ) (φ h : ℝ≥0∞) (hh : startNear wbar y ≤ 2 * h) :
    ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (startNear wbar j + φ) + signatureLimit * φ) ≤
      y * (y * (h + φ) + signatureLimit * φ) := by
  set T : ℝ≥0∞ := ∑ j ∈ Finset.range y, (j : ℝ≥0∞) with hTdef
  have hT : T * 2 ≤ (y : ℝ≥0∞) * y := by
    have h1 : (∑ j ∈ Finset.range y, j) * 2 ≤ y * y := by
      rw [Finset.sum_range_id_mul_two]
      exact Nat.mul_le_mul_left _ (Nat.sub_le y 1)
    have h2 : (((∑ j ∈ Finset.range y, j) * 2 : ℕ) : ℝ≥0∞) ≤ ((y * y : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h1
    simpa only [hTdef, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using h2
  calc ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (startNear wbar j + φ) + signatureLimit * φ)
      ≤ ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (2 * h + φ) + signatureLimit * φ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        gcongr
        exact le_trans (startNear_mono hw (Finset.mem_range.1 hj).le) hh
    _ = T * 2 * h + T * φ + y * (signatureLimit * φ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ y * y * h + y * y * φ + y * (signatureLimit * φ) := by
        gcongr
        exact le_trans (le_mul_of_one_le_right' one_le_two) hT
    _ = _ := by ring

omit [Params] in
theorem ofReal_half (c : ℚ) : ENNReal.ofReal (c : ℝ) = 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) := by
  calc ENNReal.ofReal (c : ℝ) = ENNReal.ofReal (2 * ((c / 2 : ℚ) : ℝ)) := by
        congr 1
        push_cast
        ring
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

end StartSum

/-! ### One sample, and the fair share -/

section GameH

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Theorem (b), refined, one sample.** On the interpreted run of `costGameX` of an adversary that
never repeats a message, the run finishes with a valid transcript and A4b holds with probability at
most `2^-128 Σ_{j < y} (j (startNear_j + φ) + N φ)`, `y = q - keygenCost`, `φ` the failing mass of
the prepared encodings, for any leaf-value knowledge `K`. -/
theorem a4b_bound_game_half (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞) (hfair : Fair wbar (q - keygenCost + digestAttemptLimit))
    (known : Knowledge Coordinate) :
    Pr[A4bRun (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) K |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      contactRate * ∑ j ∈ Finset.range (q - keygenCost),
        ((j : ℝ≥0∞) * (startNear wbar j + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  refine le_trans (costGameX_event param data tg prepared.2 (sampleModel parameterOutput highs) (internalize adversary)
    q _ (fun o R s => ∃ outcome, o = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧ A4b param data K s outcome.2.1 R)
    (fun R s ⟨_, h, _⟩ => by cases h)) ?_
  exact a4b_bound_half param data K wbar (failSet prepared.1) tg prepared.2 (sampleModel parameterOutput highs)
    (sampleModel_parse_blk parameterOutput highs data)
    (fun p call => hmsg _ (msgInput_digestInput param data.root p.1 p.2 call))
    (fun p call => prepared_clean parameterOutput fixed highs remaining prepared hprepared _
      (msgInput_digestInput param data.root p.1 p.2 call))
    (ftsRows_sampleModel parameterOutput highs)
    (prepared_cleanRows parameterOutput fixed highs remaining prepared hprepared)
    (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining prepared
      hprepared tg m ρ digest budget s1 hprep out hout hnone) (q - keygenCost) hfair _
    (noRepeat_internalize_adversary adversary hnr _) known

/-- **Theorem (b) at the fair share, with a certified near H-term, halved.** The near H-term `c`
of `a4b_bound_check` enters at half weight: a single query is either a FORS query that may make a
contact or a digest query that raises the near potential, never both. -/
theorem a4b_bound_check_half (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (b N qb m : ℕ) (c : ℚ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (hc : H0.checkNear b N qb m c = true) (hq : q - keygenCost ≤ qb)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (known : Knowledge Coordinate) :
    Pr[A4bRun (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) K |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
        ((q - keygenCost : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) := by
  have hqb : 2 * qb ≤ 2 ^ 128 := by
    simp only [H0.checkNear, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.2
  have hfair := fair_wbarOf (q - keygenCost) (by omega)
  have h := a4b_bound_game_half adversary hnr q parameterOutput fixed highs remaining prepared hprepared tg hmsg K
    (H0.wbarOf (q - keygenCost)) hfair known
  refine le_trans h ?_
  rw [mul_comm ((q - keygenCost : ℕ) : ℝ≥0∞) contactRate, mul_assoc]
  refine mul_le_mul_left' (start_sum_le hfair.le_one _ _ _ ?_) _
  rw [startNear_wbarOf, ← ofReal_half]
  exact H0.hNearOf_le_of_check b N qb m c hb hN hc _ hq

end GameH

end LeanSphincs.Security.ForsPotential
