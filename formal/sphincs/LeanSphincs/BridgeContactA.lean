import LeanSphincs.BridgeContactB

/-! **A4a.** A contact made at an unknown FORS secret whose leaf is revealed by the run. Contacts are
made at unexposed secrets, so a contact is revealed only by a later signature. One signing call
reveals a given leaf only through the pair it signs: a fresh landed view, which hits the leaf with
probability `2^-b 2^-10`, or a cached pair of the signed message, each with probability at most
`wbar`. The potential

`Ψa = #revealed contacts + (#unrevealed contacts + y 2^-128) · (n 2^-b 2^-10 + wbar (#coins + y landing))`,

with `n` the remaining signatures, `y` the remaining budget and `#coins` the cached landed pairs of
messages not yet signed, pays the event. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Hitting one leaf -/

/-- A kept view hits a FORS leaf position. -/
noncomputable def hitsAt (i : Index) (t : FtsTree) (l : FtsLeaf) (v : View) : ℝ≥0∞ :=
  if v.1 = localIdx i ∧ v.2 t = l then 1 else 0

/-- The probability that a uniform kept view hits a given leaf, `2^-b 2^-10`. -/
noncomputable def matchRate : ℝ≥0∞ := ((2 ^ subtreeHeight * 2 ^ 10 : ℕ) : ℝ≥0∞)⁻¹

theorem card_leafMatch (t : FtsTree) (l : FtsLeaf) :
    (Finset.univ.filter fun r : IndexGroup → FtsLeaf => r t = l).card = 2 ^ 230 := by
  set h : IndexGroup → FtsLeaf → ℕ := fun t' x => if t' = t then (if x = l then 1 else 0) else 1 with hh
  have hpt : ∀ r : IndexGroup → FtsLeaf, (if r t = l then 1 else 0) = ∏ t', h t' (r t') := by
    intro r
    rw [← Finset.mul_prod_erase Finset.univ (fun t' => h t' (r t')) (Finset.mem_univ t)]
    rw [Finset.prod_eq_one (fun t' ht' => by simp only [hh, if_neg (Finset.ne_of_mem_erase ht')])]
    simp [hh]
  rw [Finset.card_filter]
  simp only [hpt]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  rw [← Finset.mul_prod_erase Finset.univ (fun t' => ∑ x, h t' x) (Finset.mem_univ t)]
  have h1 : ∑ x, h t x = 1 := by simp [hh]
  have h2 : ∀ t' ∈ Finset.univ.erase t, ∑ x, h t' x = 2 ^ 10 := by
    intro t' ht'
    simp only [hh, if_neg (Finset.ne_of_mem_erase ht'), Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact H0.card_ftsLeaf
  rw [h1, one_mul, Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  simp only [Fintype.card_fin, ftsTrees]
  norm_num

theorem freshAvg_hitsAt (i : Index) (t : FtsTree) (l : FtsLeaf) :
    freshAvg Finset.univ (hitsAt i t l) = matchRate := by
  unfold freshAvg hitsAt
  have hsum : ∑ v ∈ (Finset.univ : Finset View), (if v.1 = localIdx i ∧ v.2 t = l then (1 : ℝ≥0∞) else 0) =
      ((2 ^ 230 : ℕ) : ℝ≥0∞) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (localIdx i) (fun a _ ha => by simp [ha]) (fun h => absurd (Finset.mem_univ _) h)]
    simp only [true_and]
    rw [← card_leafMatch t l, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun r _ => by split_ifs <;> simp
  rw [hsum, Finset.card_univ, H0.card_view]
  unfold matchRate
  have hsplit : ((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞) =
      ((2 ^ subtreeHeight * 2 ^ 10 : ℕ) : ℝ≥0∞) * ((2 ^ 230 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, show (240 : ℕ) = 10 + 230 from rfl, pow_add, ← mul_assoc]
  rw [hsplit, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inr (by positivity)), mul_assoc,
    ENNReal.inv_mul_cancel (by positivity) (ENNReal.natCast_ne_top _), mul_one]

/-! ### One signing call reveals a leaf rarely -/

section Reveal

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (parameter : PublicParameter) (data : PublicData)
  (m : Message)

/-- A completed signing call that reveals a leaf selected a pair hitting it, fresh or cached. -/
theorem reveal_point (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {s : State} {P : List Pair} (hP : PInv parameter data s P) (hprep : Prepared initial s)
    (attempts budget : ℕ) (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : o1.1.1 = some r) (i : Index) (t : FtsTree) (l : FtsLeaf)
    (hrev : Coordinate.ftsSecret i t l ∈ o1.1.2.1) :
    1 ≤ freshNewWeight parameter data m s (hitsAt i t l) o1 +
      outWeight parameter data m s (fun _ => 0) (fun _ v => hitsAt i t l v) o1 := by
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Finset.univ
    (fun _ _ _ _ _ _ _ _ => Finset.mem_univ _) attempts budget s hprep o1 ho1 r hr
  rcases hpost with ⟨_, hnil, _⟩ | ⟨ρ, u0, u1, hsel, hfts, hsig, hfl⟩
  · rw [hnil] at hrev; cases hrev
  · obtain ⟨hi, hl⟩ := hfts _ hrev i t l rfl
    have hhit : hitsAt i t l (viewOf u0 u1) = 1 := by
      unfold hitsAt
      rw [if_pos ⟨by rw [hi]; rfl, by rw [hl]; rfl⟩]
    rcases hsel.2.2.2.1 with hs0 | hs0
    · have hs1 : s.cache (blk parameter data m ρ 1) = none := hP.first (m, ρ) hs0
      have h := freshNewWeight_ge hr hs1 hsel.1 hsel.2.1 hsel.2.2.1 (hitsAt i t l)
      rw [hhit] at h
      exact le_trans h le_self_add
    · rcases r with _ | sig
      · rw [(hfl rfl).1] at hrev; cases hrev
      · have hρ := hsig sig rfl
        refine le_trans (le_of_eq ?_) le_add_self
        unfold outWeight
        rw [hr]
        simp only
        rw [hρ, hsel.1, hsel.2.2.1]
        simp only [Option.elim, pairWeight, hs0, reduceCtorEq, if_false]
        exact hhit.symm

omit [Params] in
theorem list_sum_le_length {γ : Type} (l : List γ) (f : γ → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    (l.map f).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [add_comm (l.length : ℝ≥0∞)]
      exact add_le_add (hf x) ih

/-- **One signing call** reveals a given leaf with probability at most `2^-b 2^-10` plus `wbar` per
cached pair of the signed message. -/
theorem reveal_le (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {s : State} {P : List Pair} (hP : PInv parameter data s P) (hprep : Prepared initial s)
    {wbar : ℝ≥0∞} {Cmax : ℕ} (hfair : Fair wbar Cmax) (attempts budget : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) (i : Index) (t : FtsTree) (l : FtsLeaf) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (if o1.1.1.isSome ∧ Coordinate.ftsSecret i t l ∈ o1.1.2.1 then 1 else 0) ≤
      matchRate + wbar * ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) := by
  have hparse' : ∀ ρ call, model.parse (blk parameter data m ρ call) = none := fun ρ call => hparse (m, ρ) call
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  set gp : Randomness → View → ℝ≥0∞ := fun _ v => hitsAt i t l v with hgp
  have hgp1 : ∀ ρ v, gp ρ v ≤ 1 := by
    intro ρ v
    simp only [hgp, hitsAt]
    split_ifs <;> simp
  have hfresh := loop_bound_fresh tg initial model parameter data m hparse' s hnob1 hlandb1 (hitsAt i t l)
    attempts budget s (related_self parameter data m s)
  have hpool := loop_bound tg initial model parameter data m hparse' s hnob1 (fun _ => 0) gp 1 ENNReal.one_ne_top
    (fun _ => zero_le_one) hgp1 wbar hfair.ne_top Cmax hfair.cmax hfair.share attempts budget s
    (related_self parameter data m s) hcount
  have hsum := pool_sum_le_msg parameter data m s hP (fun _ => False) (hitsAt i t l)
  rw [filter_false'] at hsum
  simp only [if_neg not_false] at hsum
  have hlen : ((P.filter fun q => decide (q.1 = m)).map fun q => hitsAt i t l (pview parameter data s q)).sum ≤
      ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) :=
    list_sum_le_length _ _ fun q => by unfold hitsAt; split_ifs <;> simp
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (freshNewWeight parameter data m s (hitsAt i t l) o1 + outWeight parameter data m s (fun _ => 0) gp o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s)
        · refine mul_le_mul_left' ?_ _
          split_ifs with hc
          · obtain ⟨hsome, hrev⟩ := hc
            obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
            exact reveal_point tg initial model parameter data m hparse hP hprep attempts budget o1 ho1 r hr i t l hrev
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          freshNewWeight parameter data m s (hitsAt i t l) o1 +
        ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          outWeight parameter data m s (fun _ => 0) gp o1 := by
        simp only [mul_add, ENNReal.tsum_add]
    _ ≤ freshAvg Finset.univ (hitsAt i t l) + (freshAvg Finset.univ (fun _ : View => (0 : ℝ≥0∞)) +
          wbar * ∑ ρ, poolValue parameter data m s gp ρ) := add_le_add hfresh hpool
    _ ≤ matchRate + wbar * ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) := by
        rw [freshAvg_hitsAt, freshAvg_const _ Finset.univ_nonempty, zero_add]
        exact add_le_add le_rfl (mul_le_mul_left' (le_trans hsum hlen) _)

end Reveal

/-! ### The potential -/

section Defs

variable (parameter : PublicParameter) (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞)

/-- **The spec's A4a**: a contact at a revealed leaf. -/
def A4a (s : State) (reveals : List Coordinate) : Prop :=
  ∃ index tree leaf, GRContact parameter K s index tree leaf ∧ Coordinate.ftsSecret index tree leaf ∈ reveals

/-- The final value of A4a: a finished game with a valid transcript. -/
noncomputable def finalA : FinalFn := fun o R s =>
  o.elim 0 fun outcome => if SigningTranscript.Valid outcome.2.1 ∧ A4a parameter K s R then 1 else 0

/-- Cached landed pairs of messages not yet signed. -/
noncomputable def coinCount (P : List Pair) (L : QueryLog SigningSpec) : ℕ := (P.filter fun q => decide (MsgFresh L q)).length

/-- The reveal rate of one unrevealed contact over the rest of the run. -/
noncomputable def riskA (P : List Pair) (L : QueryLog SigningSpec) (budget : ℕ) : ℝ≥0∞ :=
  ((signatureLimit - L.length : ℕ) : ℝ≥0∞) * matchRate + wbar * coinCount P L + budget * (wbar * landing)

/-- Revealed contacts. -/
noncomputable def revealedContacts (s : State) (R : List Coordinate) : Finset (Coordinate × Digest) :=
  (contacts parameter K s).filter fun g => g.1 ∈ R

/-- Unrevealed contacts. -/
noncomputable def openContacts (s : State) (R : List Coordinate) : Finset (Coordinate × Digest) :=
  (contacts parameter K s).filter fun g => g.1 ∉ R

/-- **The potential of A4a.** -/
noncomputable def psiA : Potential := fun s P L _ R budget =>
  if signatureLimit < L.length then 0
  else (revealedContacts parameter K s R).card +
    ((openContacts parameter K s R).card + budget * contactRate) * riskA wbar P L budget

end Defs

/-! ### The four steps -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem a4a_mono {s s' : State} (hext : Extends s s') {R : List Coordinate} (h : A4a parameter K s R) :
    A4a parameter K s' R := by
  obtain ⟨i, t, l, ⟨secret, ans, hc, hg, hK⟩, hR⟩ := h
  exact ⟨i, t, l, ⟨secret, ans, hext.1 _ _ hc, hext.2.2 _ hg, hK⟩, hR⟩

theorem finalA_store (o : Option HiddenBridge.Outcome) (R : List Coordinate) (s : State) (x : HashInput)
    (u : HashOutput) (hx : s.cache x = none) :
    finalA parameter K o R s ≤ finalA parameter K o R (s.store x u) := by
  unfold finalA
  cases o with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd ⟨h1.1, a4a_mono parameter K (extends_store s x u hx) h1.2⟩ h2
      · exact bot_le
      · exact le_rfl

theorem coinCount_addPair (P : List Pair) (L : QueryLog SigningSpec) (p : Pair) (u0 : HashOutput) :
    (coinCount (addPair parameter P p u0) L : ℝ≥0∞) =
      coinCount P L + if Landed parameter (blockIndex u0) then (if MsgFresh L p then 1 else 0) else 0 := by
  unfold coinCount addPair
  split_ifs with hl hf
  · rw [List.filter_cons_of_pos (by simpa using hf)]
    simp
  · rw [List.filter_cons_of_neg (by simpa using hf)]
    simp
  · simp

/-- **A new pair.** -/
theorem psiA_newPair (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) :
    NewPairPays parameter data Qtot initial model (psiA parameter K wbar) := by
  intro budget s P L d R hb hB p hp0
  have hp1 := hB.pinv.first p hp0
  have hc : ∀ a b, contacts parameter K (withPair parameter data s p a b) = contacts parameter K s :=
    fun a b => contacts_withPair parameter data K model hB.cinv hparse hp0 hp1 a b
  simp only [psiA, revealedContacts, openContacts, hc]
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  simp only [if_neg hL]
  set Rv : ℝ≥0∞ := (((contacts parameter K s).filter fun g => g.1 ∈ R).card : ℝ≥0∞)
  set U : ℝ≥0∞ := (((contacts parameter K s).filter fun g => g.1 ∉ R).card : ℝ≥0∞)
  set A0 : ℝ≥0∞ := ((signatureLimit - L.length : ℕ) : ℝ≥0∞) * matchRate + wbar * coinCount P L
  have hpt : ∀ u0 u1 : HashOutput, Rv + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) *
      riskA wbar (addPair parameter P p u0) L (budget - 1) =
      Rv + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * (A0 + ((budget - 1 : ℕ) : ℝ≥0∞) * (wbar * landing)) +
        (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * wbar *
          (if Landed parameter (blockIndex u0) then (if MsgFresh L p then 1 else 0) else 0) := by
    intro u0 u1
    simp only [riskA, coinCount_addPair, A0]
    ring
  refine le_trans (le_of_eq (congrArg pairE (funext fun u0 => funext fun u1 => hpt u0 u1))) ?_
  rw [pairE_add, pairE_add, pairE_const, pairE_const, pairE_const_mul]
  have hland : pairE (fun u0 _ => if Landed parameter (blockIndex u0) then (if MsgFresh L p then (1 : ℝ≥0∞) else 0)
      else 0) ≤ landing := by
    have h := pairE_landed parameter (fun _ => if MsgFresh L p then (1 : ℝ≥0∞) else 0) 0
    simp only [mul_zero, add_zero] at h
    have h' : pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
        (fun _ : View => if MsgFresh L p then (1 : ℝ≥0∞) else 0) (viewOf u0 u1) else 0) ≤ landing := by
      rw [h, freshAvg_const _ Finset.univ_nonempty]
      split_ifs <;> simp
    simpa using h'
  have hbud : ((budget - 1 : ℕ) : ℝ≥0∞) + 1 = budget := by exact_mod_cast Nat.sub_add_cancel hb
  calc Rv + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * (A0 + ((budget - 1 : ℕ) : ℝ≥0∞) * (wbar * landing)) +
        (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * wbar *
          pairE (fun u0 _ => if Landed parameter (blockIndex u0) then (if MsgFresh L p then 1 else 0) else 0)
      ≤ Rv + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * (A0 + ((budget - 1 : ℕ) : ℝ≥0∞) * (wbar * landing)) +
        (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * wbar * landing := by gcongr
    _ = Rv + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) *
          (A0 + (((budget - 1 : ℕ) : ℝ≥0∞) + 1) * (wbar * landing)) := by ring
    _ ≤ Rv + (U + (budget : ℝ≥0∞) * contactRate) * (A0 + (budget : ℝ≥0∞) * (wbar * landing)) := by
        rw [hbud]
        gcongr
        exact Nat.sub_le budget 1
    _ = _ := by simp only [riskA, A0]

/-- **Any other ordinary query.** -/
theorem psiA_ordinary (hrows : FtsRows parameter model) :
    OrdinaryPays parameter data Qtot initial model (psiA parameter K wbar) := by
  intro budget s P L d R hb hB x hnew
  simp only [psiA]
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, mul_zero, tsum_zero, le_refl]
  simp only [if_neg hL]
  set Rv : ℝ≥0∞ := ((revealedContacts parameter K s R).card : ℝ≥0∞) with hRv
  set U : ℝ≥0∞ := ((openContacts parameter K s R).card : ℝ≥0∞) with hU
  set ρ := riskA wbar P L budget with hρ
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      ((revealedContacts parameter K r.2 R).card : ℝ≥0∞) +
          (((openContacts parameter K r.2 R).card : ℝ≥0∞) + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) *
            riskA wbar P L (budget - 1) ≤
        Rv + (U + ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) +
          ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * ρ := by
    intro r hr
    obtain ⟨_, hsub, hnew'⟩ := ordinary_contacts (K := K) hrows x s hB.cinv r hr
    have hRv' : revealedContacts parameter K r.2 R = revealedContacts parameter K s R := by
      unfold revealedContacts
      ext g
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hg, hgR⟩
        refine ⟨?_, hgR⟩
        by_contra hn
        obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hnew' g hg hn
        exact hB.rinv g.1 hgR hk
      · rintro ⟨hg, hgR⟩
        exact ⟨hsub hg, hgR⟩
    have hU' : ((openContacts parameter K r.2 R).card : ℝ≥0∞) ≤
        U + ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) := by
      have hsub' : openContacts parameter K r.2 R ⊆
          openContacts parameter K s R ∪ (contacts parameter K r.2 \ contacts parameter K s) := by
        intro g hg
        obtain ⟨hg1, hg2⟩ := Finset.mem_filter.1 hg
        by_cases hgs : g ∈ contacts parameter K s
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hgs, hg2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hg1, hgs⟩)
      have hnat := le_trans (Finset.card_le_card hsub') (Finset.card_union_le _ _)
      rw [hU]
      exact_mod_cast hnat
    have hρ' : riskA wbar P L (budget - 1) ≤ ρ := by
      simp only [hρ, riskA]
      gcongr
      exact_mod_cast Nat.sub_le budget 1
    rw [hRv']
    gcongr
  have hmean := ordinary_contacts_mean (K := K) hrows x s hB.cinv
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (Rv + (U + ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) +
          ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * ρ) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_left' (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' r, Pr[= r | ordinaryStep model x s.known s]) * Rv +
          ((∑' r, Pr[= r | ordinaryStep model x s.known s]) * U +
            ∑' r, Pr[= r | ordinaryStep model x s.known s] *
              ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) +
            (∑' r, Pr[= r | ordinaryStep model x s.known s]) * (((budget - 1 : ℕ) : ℝ≥0∞) * contactRate)) * ρ := by
        simp only [add_mul, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← mul_assoc]
    _ ≤ 1 * Rv + (1 * U + contactRate + 1 * (((budget - 1 : ℕ) : ℝ≥0∞) * contactRate)) * ρ := by
        gcongr
        · exact tsum_probOutput_le_one
        · exact tsum_probOutput_le_one
        · exact hmean
        · exact tsum_probOutput_le_one
    _ = Rv + (U + (budget : ℝ≥0∞) * contactRate) * ρ := by
        have hcast : ((budget - 1 : ℕ) : ℝ≥0∞) + 1 = budget := by exact_mod_cast Nat.sub_add_cancel hb
        rw [one_mul, one_mul, one_mul, ← hcast]
        ring

omit [Params] in
theorem coinCount_split (P : List Pair) (L : QueryLog SigningSpec) (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m) :
    coinCount P L = (P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m)).length +
      (P.filter fun q => decide (q.1 = m)).length := by
  unfold coinCount
  have h1 : (P.filter fun q => decide (MsgFresh L q)).filter (fun q => !decide (q.1 = m)) =
      P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m) := by
    rw [List.filter_filter]
    congr 1
    funext q
    by_cases hq : q.1 = m <;> by_cases hf : MsgFresh L q <;> simp [hq, hf]
  have h2 : (P.filter fun q => decide (MsgFresh L q)).filter (fun q => decide (q.1 = m)) =
      P.filter fun q => decide (q.1 = m) := by
    rw [List.filter_filter]
    congr 1
    funext q
    by_cases hq : q.1 = m
    · have hf : MsgFresh L q := fun entry he => by rw [hq]; exact hm entry he
      simp [hq, hf]
    · simp [hq]
  have h := List.length_eq_length_filter_add (l := P.filter fun q => decide (MsgFresh L q))
    (fun q => decide (q.1 = m))
  rw [h2, h1] at h
  omega

theorem coinCount_after (P : List Pair) (L : QueryLog SigningSpec) (m : Message) (s s' : State)
    (r : Option Signature) :
    coinCount (newPairs parameter data m s s' ++ P) (L ++ [⟨m, r⟩]) =
      (P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m)).length := by
  unfold coinCount
  rw [List.filter_append]
  have hnew : (newPairs parameter data m s s').filter (fun q => decide (MsgFresh (L ++ [⟨m, r⟩]) q)) = [] := by
    refine List.filter_eq_nil_iff.2 fun q hq => ?_
    obtain ⟨hm, _, _⟩ := (mem_newPairs parameter data m s).1 hq
    simp only [decide_eq_true_eq, msgFresh_append, not_and, not_not]
    exact fun _ => hm
  rw [hnew, List.nil_append]
  congr 1
  congr 1
  funext q
  simp only [msgFresh_append]

/-- **A signing call** on a fresh message. -/
theorem psiA_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model) {Cmax : ℕ} (hfair : Fair wbar Cmax) (hQ : Qtot + digestAttemptLimit ≤ Cmax) :
    SignPays parameter data Qtot tg initial model (psiA parameter K wbar) := by
  intro budget s P L d R hB m hm
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hB.count m; omega
  set sign := signCostSourceLoop parameter data m digestAttemptLimit with hsign
  by_cases hL : signatureLimit ≤ L.length
  · -- after one more signature the potential vanishes
    refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun o1 => ?_) bot_le
    cases hres : o1.1.1 with
    | none => simp
    | some r =>
        simp only [Option.elim, psiA]
        rw [if_pos (by simp only [List.length_append, List.length_singleton]; omega), mul_zero]
  have hL' : ¬signatureLimit < L.length := by omega
  set C := contacts parameter K s with hC
  set Rv : ℝ≥0∞ := ((revealedContacts parameter K s R).card : ℝ≥0∞) with hRv
  set U : ℝ≥0∞ := ((openContacts parameter K s R).card : ℝ≥0∞) with hU
  set Pm : ℝ≥0∞ := ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) with hPm
  set cc' : ℝ≥0∞ := ((P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m)).length : ℝ≥0∞) with hcc'
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  set ρ'' : ℝ≥0∞ := (n : ℝ≥0∞) * matchRate + wbar * cc' + budget * (wbar * landing) with hρ''
  have hrisk : riskA wbar P L budget = (matchRate + wbar * Pm) + ρ'' := by
    simp only [riskA, hρ'', hn1, coinCount_split P L m hm, hPm, hcc']
    push_cast
    ring
  -- the reveal indicator of the open contacts
  set X : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    ∑ g ∈ openContacts parameter K s R, (if o1.1.1.isSome ∧ g.1 ∈ o1.1.2.1 then 1 else 0) with hX
  have hpt : ∀ o1 ∈ support (interp tg initial model sign budget s),
      o1.1.1.elim 0 (fun r => psiA parameter K wbar o1.2 (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
      Rv + X o1 + (U + (budget : ℝ≥0∞) * contactRate) * ρ'' := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => exact bot_le
    | some r =>
        simp only [Option.elim, psiA]
        split_ifs with hgate
        · exact bot_le
        have hcon := (interp_contacts_avoid (K := K) tg initial hrows _ (avoids_loopF parameter data m _)
          budget s hB.cinv o1 ho1).2
        simp only [revealedContacts, openContacts, hcon]
        -- revealed contacts: old ones and the newly revealed open ones
        have hRv' : (((C.filter fun g => g.1 ∈ R ++ o1.1.2.1).card : ℕ) : ℝ≥0∞) ≤ Rv + X o1 := by
          have hsub : C.filter (fun g => g.1 ∈ R ++ o1.1.2.1) ⊆
              C.filter (fun g => g.1 ∈ R) ∪ (openContacts parameter K s R).filter (fun g => g.1 ∈ o1.1.2.1) := by
            intro g hg
            obtain ⟨hgC, hgR⟩ := Finset.mem_filter.1 hg
            rcases List.mem_append.1 hgR with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hgC, h⟩)
            · by_cases hR : g.1 ∈ R
              · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hgC, hR⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hgC, hR⟩, h⟩)
          have hX' : (((openContacts parameter K s R).filter (fun g => g.1 ∈ o1.1.2.1)).card : ℝ≥0∞) = X o1 := by
            simp only [hX, hres, Option.isSome_some, true_and]
            rw [Finset.card_filter]
            push_cast
            rfl
          calc (((C.filter fun g => g.1 ∈ R ++ o1.1.2.1).card : ℕ) : ℝ≥0∞)
              ≤ (((C.filter fun g => g.1 ∈ R) ∪
                  (openContacts parameter K s R).filter (fun g => g.1 ∈ o1.1.2.1)).card : ℝ≥0∞) := by
                exact_mod_cast Finset.card_le_card hsub
            _ ≤ _ := by
                rw [← hX', hRv]
                exact_mod_cast Finset.card_union_le _ _
        have hU' : (((C.filter fun g => g.1 ∉ R ++ o1.1.2.1).card : ℕ) : ℝ≥0∞) ≤ U := by
          refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
          obtain ⟨hgC, hgR⟩ := Finset.mem_filter.1 hg
          exact Finset.mem_filter.2 ⟨hgC, fun h => hgR (List.mem_append_left _ h)⟩
        have hρ' : riskA wbar (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
            (budget - traceCost o1.1.2.2.1) ≤ ρ'' := by
          simp only [riskA, coinCount_after, hρ'', hcc', List.length_append, List.length_singleton]
          gcongr
          exact_mod_cast Nat.sub_le budget _
        have hbud : ((budget - traceCost o1.1.2.2.1 : ℕ) : ℝ≥0∞) ≤ budget := by
          exact_mod_cast Nat.sub_le budget _
        calc _ ≤ (Rv + X o1) + (U + (budget : ℝ≥0∞) * contactRate) * ρ'' := by gcongr
          _ = _ := rfl
  -- the expected reveals of the open contacts
  have hXe : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * X o1 ≤ U * (matchRate + wbar * Pm) := by
    simp only [hX, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    calc ∑ g ∈ openContacts parameter K s R, ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
          (if o1.1.1.isSome ∧ g.1 ∈ o1.1.2.1 then 1 else 0)
        ≤ ∑ _g ∈ openContacts parameter K s R, (matchRate + wbar * Pm) := by
          refine Finset.sum_le_sum fun g hg => ?_
          obtain ⟨i, t, l, ans, hgi, _, _⟩ := (Finset.mem_filter.1 (Finset.mem_filter.1 hg).1).2
          rw [hgi]
          exact reveal_le tg initial model parameter data m hparse hB.pinv hB.prep hfair digestAttemptLimit budget
            hcount i t l
      _ = U * (matchRate + wbar * Pm) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hmass : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] ≤ 1 := tsum_probOutput_le_one
  simp only [psiA, if_neg hL', revealedContacts, openContacts]
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
        (Rv + X o1 + (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_left' (hpt o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = (∑' o1, Pr[= o1 | interp tg initial model sign budget s]) * Rv +
          ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * X o1 +
          (∑' o1, Pr[= o1 | interp tg initial model sign budget s]) *
            ((U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * Rv + U * (matchRate + wbar * Pm) + 1 * ((U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
        gcongr
    _ = Rv + (U * (matchRate + wbar * Pm) + (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by ring
    _ ≤ Rv + ((U + (budget : ℝ≥0∞) * contactRate) * (matchRate + wbar * Pm) +
          (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
        gcongr
        exact le_self_add
    _ = Rv + (U + (budget : ℝ≥0∞) * contactRate) * riskA wbar P L budget := by
        rw [hrisk]
        ring

/-- **The end of the game.** -/
theorem psiA_final : FinalPays parameter data Qtot initial model (psiA parameter K wbar) (finalA parameter K) := by
  intro budget s P L d R hB forgery verified
  simp only [finalA, Option.elim, psiA]
  split_ifs with hcase hL
  · exact absurd hcase.1 (by simp [SigningTranscript.Valid]; omega)
  · obtain ⟨_, i, t, l, hgr, hR⟩ := hcase
    obtain ⟨secret, hmem⟩ := mem_contacts_of_GR parameter K hgr
    have h1 : (1 : ℝ≥0∞) ≤ (revealedContacts parameter K s R).card := by
      exact_mod_cast Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hmem, hR⟩⟩
    exact le_trans h1 le_self_add
  · exact bot_le
  · exact bot_le

end Steps

/-! ### The bound -/

section Bound

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The event A4a of a finished run with a valid transcript. -/
def A4aRun (out : Run HashInput Coordinate HiddenBridge.Outcome × State) : Prop :=
  ∃ outcome, out.1.1 = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧ A4a parameter K out.2 out.1.2.1

/-- **Theorem (a).** In the lazy run of the rest of the game of an adversary that never repeats a
message, the probability that the game finishes with a valid transcript and some contact made at
an unknown secret is revealed is at most `x (N 2^-b 2^-10 + total wbar landing)`,
`x = total · 2^-128`. -/
theorem a4a_bound (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (total : ℕ) (hfair : Fair wbar (total + digestAttemptLimit))
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[A4aRun parameter K | interp tg initial model (advProg parameter data M []) total
        (DebtState.start initial known)] ≤
      ((total : ℝ≥0∞) * contactRate) * (signatureLimit * matchRate + total * (wbar * landing)) := by
  have h := final_le_start parameter data tg initial model hparse hkind hrows hclean hcleanF Finset.univ
    (fun _ _ _ _ _ _ _ _ _ => Finset.mem_univ _) total
    (G := finalA parameter K) (fun _ _ => rfl) (fun o R s x u hx => finalA_store parameter K o R s x u hx)
    (psiA_newPair parameter data K wbar total initial model hparse)
    (psiA_ordinary parameter data K wbar total initial model hrows)
    (psiA_sign parameter data K wbar total tg initial model hparse hrows hfair le_rfl)
    (psiA_final parameter data K wbar total initial model) M hnr known
  have hstart : psiA parameter K wbar (DebtState.start initial known) [] [] 0 [] total =
      ((total : ℝ≥0∞) * contactRate) * (signatureLimit * matchRate + total * (wbar * landing)) := by
    have hc : contacts parameter K (DebtState.start initial known) = ∅ := by
      unfold contacts
      rfl
    simp only [psiA, revealedContacts, openContacts, hc, riskA, coinCount]
    simp
  rw [hstart] at h
  rw [probEvent_eq_tsum_ite]
  refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) h
  split_ifs with hE
  · obtain ⟨outcome, hres, hvalid, ha⟩ := hE
    simp only [finalA, hres, Option.elim, if_pos (And.intro hvalid ha), mul_one, le_refl]
  · exact bot_le

end Bound

end LeanSphincs.Security.ForsPotential
