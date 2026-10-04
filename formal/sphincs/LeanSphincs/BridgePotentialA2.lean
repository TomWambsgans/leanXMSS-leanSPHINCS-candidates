import LeanSphincs.BridgePotentialA

/-! One fresh answer and the linear potential, input class by input class: an input of no WOTS
or FORS shape pays its first-order hazard; a FORS leaf input pays a contact without a guess
record, a contact pair, or a new recorded contact. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

namespace Ctx

variable (K : Ctx)

theorem rate_eq_of {s s' : St} (hA : K.Armed s' ↔ K.Armed s) (hC : K.contactCount s' = K.contactCount s)
    (hK : K.KFset s' = K.KFset s) : K.rate s' = K.rate s := by
  simp only [rate, vrate, hA, hC, hK]

/-- **Other inputs.** An input of no WOTS or FORS shape pays at most its first-order hazard. -/
theorem step_other (y : ℕ) {s : St} {x : HashInput} (hx : s.cache x = none) (hi : K.initial x = none)
    (hAB : ∀ l, Landed K.p l → (∀ i, ¬K.IsA l i x) ∧ ∀ i v, ¬K.IsB l i v x)
    (hE : ∀ l msg ctr, Landed K.p l → x ≠ Wots.encodingInput K.p topLayer rootTree l msg ctr)
    (hF : ∀ index tree leaf secret, x ≠ forsLeafInput K.p index tree leaf secret) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y r.2 ≤ K.pot y s + ν * K.kindUnit x := by
  have h := K.mean_store y hx 0 (fun t => (if ¬K.Bad s ∧ Fatal (K.tg.kind x) s.known t then 1 else 0) +
    ∑ c : Coordinate, if K.tg.kind x = .hidden c ∧ s.known c = none then ν else 0) (fun u => ?_)
  · rw [add_zero] at h
    refine h.trans (add_le_add le_rfl ?_)
    rw [meanD_add, meanD_const]
    refine le_trans (add_le_add (meanD_mono fun t => ?_) le_rfl) (K.fo_mean s x)
    by_cases h1 : Fatal (K.tg.kind x) s.known t
    · rw [if_pos h1]
      split_ifs <;> simp
    · rw [if_neg h1, if_neg (fun h => h1 h.2)]
  · set s' := s.store x u with hs'
    have hsame : ∀ l, Landed K.p l → K.SameLeaf s s' l := fun l hl =>
      K.sameLeaf_store u hx hi l (hAB l hl).1 (hAB l hl).2 (fun msg ctr => hE l msg ctr hl)
    obtain ⟨hW, hA, hC⟩ := K.wots_of_allSame hsame
    have hFC : ∀ index tree leaf secret,
        K.FContact s' index tree leaf secret ↔ K.FContact s index tree leaf secret := by
      intro index tree leaf secret
      rw [K.fContact_store u hx hi]
      exact ⟨fun h => h.resolve_right fun h' => hF _ _ _ _ h'.1, Or.inl⟩
    obtain ⟨hRev, hTwo, hKF⟩ := K.fors_same hFC rfl
    have hreal := realized_store K.tg K.initial s x u hx hi
    rw [K.trunc_eq] at hreal
    have hD := K.done_le (s := s) (s' := s') (Fatal (K.tg.kind x) s.known (truncateHash u)) (by
      rintro (hr | hw | hrev | htwo)
      · rcases hreal.1 hr with hr | hf
        · exact Or.inl (Or.inl hr)
        · exact Or.inr hf
      · exact Or.inl (Or.inr (Or.inl (hW.1 hw)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (hRev.1 hrev))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (hTwo.1 htwo)))))
    have hP := K.pend_store u hx hi
    have hU := K.ua_le_of_subset (K.uaSet_store_of_not u hx hi fun l i hl => (hAB l hl).1 i)
    have hR : K.rate s' ≤ K.rate s + 0 := by rw [add_zero, K.rate_eq_of hA hC hKF]
    have := K.pot_le (cr := 0) (dU := 0) y hD hP (by rw [add_zero, add_zero]; exact hU) hR
    refine this.trans (le_of_eq ?_)
    simp only [mul_zero, add_zero]

/-- **FORS leaf inputs.** A contact pays its second-order event when it has no guess record or
completes a pair, and otherwise one more recorded contact. -/
theorem step_fors (y : ℕ) {s : St} {x : HashInput} (hx : s.cache x = none) (hi : K.initial x = none)
    {index : Index} {tree : FtsTree} {leaf : FtsLeaf} {secret : Digest}
    (hxF : x = forsLeafInput K.p index tree leaf secret) (hk : K.tg.kind x = .none) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y r.2 ≤ K.pot y s +
      ν * ((if ¬K.Bad s ∧ ((Coordinate.ftsSecret index tree leaf, secret) ∉ s.guesses ∨
          ∃ tree' leaf' secret', tree' ≠ tree ∧ K.FContact s index tree' leaf' secret') then 1 else 0) +
        ((y : ℝ≥0∞) * ν) * (if (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses then 1 else 0)) := by
  set rec := (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses with hrec
  set partner := ∃ tree' leaf' secret', tree' ≠ tree ∧ K.FContact s index tree' leaf' secret' with hpartner
  set A : ℝ≥0∞ := if ¬K.Bad s ∧ (¬rec ∨ partner) then 1 else 0 with hAdef
  set B : ℝ≥0∞ := if rec then 1 else 0 with hBdef
  have h := K.mean_store y hx 0 (fun t => if t = K.leafValue index tree leaf then A + ((y : ℝ≥0∞) * ν) * B
    else 0) (fun u => ?_)
  · rw [add_zero] at h
    refine h.trans (le_of_eq ?_)
    rw [meanD_ite_eq _ (fun t => t = K.leafValue index tree leaf) (fun t => Iff.rfl)]
  · set s' := s.store x u with hs'
    set t := truncateHash u with ht
    have hnotA : ∀ l i, ¬K.IsA l i x := fun l i hA => isA_ne_fors hA index tree leaf secret hxF
    have hnotB : ∀ l i v, ¬K.IsB l i v x := fun l i v hB => isB_ne_fors hB index tree leaf secret hxF
    have hsame : ∀ l, Landed K.p l → K.SameLeaf s s' l := fun l _ =>
      K.sameLeaf_store u hx hi l (hnotA l) (hnotB l) (fun msg ctr he => enc_ne_fors (he.symm.trans hxF))
    obtain ⟨hW, hA, hC⟩ := K.wots_of_allSame hsame
    have hFC : ∀ index' tree' leaf' secret', K.FContact s' index' tree' leaf' secret' ↔
        K.FContact s index' tree' leaf' secret' ∨
          (index' = index ∧ tree' = tree ∧ leaf' = leaf ∧ secret' = secret ∧ t = K.leafValue index tree leaf) := by
      intro index' tree' leaf' secret'
      rw [K.fContact_store u hx hi, hxF]
      constructor
      · rintro (h | ⟨heq, hv⟩)
        · exact Or.inl h
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := fors_inj heq
          exact Or.inr ⟨rfl, rfl, rfl, rfl, hv⟩
      · rintro (h | ⟨rfl, rfl, rfl, rfl, hv⟩)
        · exact Or.inl h
        · exact Or.inr ⟨rfl, hv⟩
    have hreal := realized_store_of_none K.tg K.initial s x u hx hi hk
    have hD := K.done_le (s := s) (s' := s') (t = K.leafValue index tree leaf ∧ (¬rec ∨ partner)) (by
      rintro (hr | hw | ⟨index', tree', leaf', secret', hc, hng⟩ |
          ⟨index', tree₁, tree₂, leaf₁, leaf₂, secret₁, secret₂, hne, hc₁, hc₂⟩)
      · exact Or.inl (Or.inl (hreal.1 hr))
      · exact Or.inl (Or.inr (Or.inl (hW.1 hw)))
      · rcases (hFC _ _ _ _).1 hc with hc | ⟨rfl, rfl, rfl, rfl, hv⟩
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, hc, hng⟩)))
        · exact Or.inr ⟨hv, Or.inl hng⟩
      · rcases (hFC _ _ _ _).1 hc₁ with hc₁ | ⟨h1, h2, -, -, hv⟩
        · rcases (hFC _ _ _ _).1 hc₂ with hc₂ | ⟨h1', h2', -, -, hv'⟩
          · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, hne, hc₁, hc₂⟩)))
          · subst h1' h2'
            exact Or.inr ⟨hv', Or.inr ⟨tree₁, leaf₁, secret₁, hne, hc₁⟩⟩
        · rcases (hFC _ _ _ _).1 hc₂ with hc₂ | ⟨-, h2', -, -, -⟩
          · subst h1 h2
            exact Or.inr ⟨hv, Or.inr ⟨tree₂, leaf₂, secret₂, fun h => hne h.symm, hc₂⟩⟩
          · exact absurd (h2.trans h2'.symm) hne)
    have hP : K.pend s' ≤ K.pend s + 0 := by rw [add_zero, K.pend_store_none u hx hi hk]
    have hU := K.ua_le_of_subset (K.uaSet_store_of_not u hx hi fun l i _ => hnotA l i)
    have hKF : ((K.KFset s').encard : ℝ≥0∞) ≤ ((K.KFset s).encard : ℝ≥0∞) +
        (if t = K.leafValue index tree leaf ∧ rec then 1 else 0) := by
      have hsub : K.KFset s' ⊆ insert (index, tree, leaf, secret) (K.KFset s) := by
        rintro ⟨index', tree', leaf', secret'⟩ ⟨hc, hg⟩
        rcases (hFC _ _ _ _).1 hc with hc | ⟨rfl, rfl, rfl, rfl, -⟩
        · exact Or.inr ⟨hc, hg⟩
        · exact Or.inl rfl
      split_ifs with hcase
      · exact (ENat.toENNReal_le.2 (Set.encard_le_encard hsub)).trans (encard_insert_le_ennreal _ _)
      · rw [add_zero]
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro ⟨index', tree', leaf', secret'⟩ ⟨hc, hg⟩
        rcases (hFC _ _ _ _).1 hc with hc | ⟨rfl, rfl, rfl, rfl, hv⟩
        · exact ⟨hc, hg⟩
        · exact absurd ⟨hv, hg⟩ hcase
    have hR := K.rate_le (dV := 0) (dC := 0) (by rw [add_zero]; exact le_of_eq (by simp only [vrate, hA]))
      (by rw [add_zero, hC]) hKF
    have := K.pot_le (cr := 0) (dU := 0) y hD hP (by rw [add_zero, add_zero]; exact hU) hR
    refine this.trans (add_le_add le_rfl ?_)
    by_cases hv : t = K.leafValue index tree leaf
    · rw [if_pos hv]
      simp only [hv, true_and, mul_zero, zero_add, add_zero, hAdef, hBdef, le_refl]
    · rw [if_neg hv]
      simp [hv]

/-! ### Helpers for one changed leaf -/

theorem leafCount_le_of {s s' : St} {l : Index} (hc : ∀ i, K.ContactB s' l i = K.ContactB s l i)
    (hb : K.BadLeaf s l → K.BadLeaf s' l) : K.leafCount s' l ≤ K.leafCount s l := by
  unfold leafCount
  by_cases h' : K.BadLeaf s' l
  · rw [if_pos h']
    exact bot_le
  · rw [if_neg h', if_neg (fun h => h' (hb h))]
    simp only [hc, le_refl]

theorem armedAt_of_le {s s' : St} {l : Index} (hc : ∀ i, K.ContactB s' l i = K.ContactB s l i)
    (hm : ∀ i, K.Marker s' l i ↔ K.Marker s l i) (hb : K.BadLeaf s l → K.BadLeaf s' l)
    (h : K.ArmedAt s' l) : K.ArmedAt s l := by
  obtain ⟨hn, hr⟩ := h
  refine ⟨fun h => hn (hb h), ?_⟩
  simpa only [hc, hm] using hr

theorem vrate_le_self (hρ : K.ρ ≤ 2) {s s' : St} (h : K.Armed s' → K.Armed s) : K.vrate s' ≤ K.vrate s := by
  have := K.vrate_le hρ False (fun h' => Or.inl (h h'))
  simpa using this

theorem meanD_sum {ι : Type} (S : Finset ι) (f : ι → Digest → ℝ≥0∞) :
    meanD (fun t => ∑ j ∈ S, f j t) = ∑ j ∈ S, meanD (f j) := by
  simp only [meanD]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem meanD_mul (c : ℝ≥0∞) (f : Digest → ℝ≥0∞) : meanD (fun t => c * f t) = c * meanD f := by
  simp only [meanD, ← Finset.mul_sum]
  ring

theorem markSet_card (l : Index) (i : ChainIndex) : ((K.markSet l i).card : ℝ≥0∞) ≤ 63 := by
  have h1 := decodingDigests_card_le (unitNeighbors (K.w l) i)
  have h2 := unitNeighbors_card_le (K.w l) i
  rw [unitNeighborBound_eq] at h2
  have : (K.markSet l i).card ≤ 63 := h1.trans h2
  exact_mod_cast this

theorem markAll_card (l : Index) : ((K.markAll l).card : ℝ≥0∞) ≤ 4032 := by
  have h1 := decodingDigests_card_le (allUnitNeighbors (K.w l))
  have h2 := allUnitNeighbors_card_le (K.w l)
  rw [neighborBound_eq] at h2
  have : (K.markAll l).card ≤ 4032 := h1.trans h2
  exact_mod_cast this

theorem markSet_subset (l : Index) (i : ChainIndex) {t : Digest} (h : t ∈ K.markSet l i) : t ∈ K.markAll l := by
  obtain ⟨word, hw, hd⟩ := mem_decodingDigests.1 h
  exact mem_decodingDigests.2 ⟨word, mem_allUnitNeighbors.2 ⟨i, mem_unitNeighbors.1 hw⟩, hd⟩

/-! ### Inputs two steps below the word -/

/-- **Two steps below the word.** One more credit, and a two-edge completion when the answer is
the payload of a contact. -/
theorem step_A (hρ : K.ρ ≤ 2) (y : ℕ) {s : St} {x : HashInput} (hx : s.cache x = none)
    (hi : K.initial x = none) {l : Index} {i : ChainIndex} (hl : Landed K.p l) (hA : K.IsA l i x)
    (hk : K.tg.kind x = .none) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y r.2 ≤
      K.pot y s + (ν / 2 + ν * (if K.Bad s then 0 else ((K.ContactB s l i).encard : ℝ≥0∞))) := by
  have h := K.mean_store y hx 0 (fun t => ν / 2 + if ¬K.Bad s ∧ t ∈ K.ContactB s l i then 1 else 0)
    (fun u => ?_)
  · rw [add_zero] at h
    refine h.trans (le_of_eq ?_)
    rw [meanD_add, meanD_const, meanD_ite]
    by_cases hb : K.Bad s
    · simp [hb]
    · simp [hb]
  · set s' := s.store x u with hs'
    set t := truncateHash u with ht
    have hnotB : ∀ l' i' v', ¬K.IsB l' i' v' x := fun l' i' v' hB => isA_not_isB hA hB
    have hnotE : ∀ l' msg ctr, x ≠ Wots.encodingInput K.p topLayer rootTree l' msg ctr :=
      fun l' msg ctr => isA_ne_enc hA l' msg ctr
    have hnotF : ∀ index tree leaf secret, x ≠ forsLeafInput K.p index tree leaf secret := isA_ne_fors hA
    have hsame : ∀ l', Landed K.p l' → l' ≠ l → K.SameLeaf s s' l' := fun l' _ hne =>
      K.sameLeaf_store u hx hi l' (fun i' hA' => hne (isA_unique hA' hA).1) (hnotB l') (hnotE l')
    have hCB : ∀ i', K.ContactB s' l i' = K.ContactB s l i' := fun i' => by
      rw [K.contactB_store u hx hi]
      exact Set.union_eq_left.2 fun v hv => absurd hv.1 (hnotB l i' v)
    have hMk : ∀ i', K.Marker s' l i' ↔ K.Marker s l i' := fun i' => by
      rw [K.marker_store u hx hi]
      exact ⟨fun h => h.resolve_right fun ⟨⟨msg, ctr, he⟩, _⟩ => hnotE l msg ctr he, Or.inl⟩
    have hAA : ∀ i' w, w ∈ K.AAns s' l i' → w ∈ K.AAns s l i' ∨ (i' = i ∧ w = t) := fun i' w hw => by
      rw [K.aAns_store u hx hi] at hw
      split_ifs at hw with hA'
      · rcases hw with rfl | hw
        · exact Or.inr ⟨(isA_unique hA' hA).2, rfl⟩
        · exact Or.inl hw
      · exact Or.inl hw
    have hmono : K.BadLeaf s l → K.BadLeaf s' l := K.badLeaf_store_of u hx hi
    have hbad : K.BadLeaf s' l → K.BadLeaf s l ∨ t ∈ K.ContactB s l i := by
      rintro (⟨i₀, w, hw1, hw2⟩ | ⟨i₀, hne, hm⟩ | ⟨i₁, i₂, hne, h1, h2⟩)
      · rw [hCB] at hw1
        rcases hAA i₀ w hw2 with hw2 | ⟨rfl, rfl⟩
        · exact Or.inl (Or.inl ⟨i₀, w, hw1, hw2⟩)
        · exact Or.inr hw1
      · rw [hCB] at hne
        exact Or.inl (Or.inr (Or.inl ⟨i₀, hne, (hMk i₀).1 hm⟩))
      · rw [hCB] at h1 h2
        exact Or.inl (Or.inr (Or.inr ⟨i₁, i₂, hne, h1, h2⟩))
    have hFC : ∀ index tree leaf secret,
        K.FContact s' index tree leaf secret ↔ K.FContact s index tree leaf secret := by
      intro index tree leaf secret
      rw [K.fContact_store u hx hi]
      exact ⟨fun h => h.resolve_right fun h' => hnotF _ _ _ _ h'.1, Or.inl⟩
    obtain ⟨hRev, hTwo, hKF⟩ := K.fors_same hFC rfl
    have hreal := realized_store_of_none K.tg K.initial s x u hx hi hk
    have hD := K.done_le (s := s) (s' := s') (t ∈ K.ContactB s l i) (by
      rintro (hr | hw | hrev | htwo)
      · exact Or.inl (Or.inl (hreal.1 hr))
      · rcases K.wotsBad_of_same l hsame hw with hw | ⟨-, hb⟩
        · exact Or.inl (Or.inr (Or.inl hw))
        · rcases hbad hb with hb | ht
          · exact Or.inl (Or.inr (Or.inl ⟨l, hl, hb⟩))
          · exact Or.inr ht
      · exact Or.inl (Or.inr (Or.inr (Or.inl (hRev.1 hrev))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (hTwo.1 htwo)))))
    have hP : K.pend s' ≤ K.pend s + 0 := by rw [add_zero, K.pend_store_none u hx hi hk]
    have hU := K.ua_le_insert x (K.uaSet_store u hx hi)
    have hV := K.vrate_le_self hρ (s := s) (s' := s') fun ha => by
      rcases K.armed_of_same l hsame ha with ha | ⟨hl', ha⟩
      · exact ha
      · exact ⟨l, hl', K.armedAt_of_le hCB hMk hmono ha⟩
    have hC := K.contactCount_of_same l hsame 0 fun _ => by rw [add_zero]; exact K.leafCount_le_of hCB hmono
    have hR := K.rate_le (dV := 0) (dK := 0) (by rw [add_zero]; exact hV) hC (by rw [hKF, add_zero])
    have := K.pot_le (cr := 0) y hD hP (by rw [add_zero]; exact hU) hR
    refine this.trans (le_of_eq ?_)
    simp only [mul_zero, add_zero, zero_add]
    ring

theorem ite_or_le (P : Prop) [Decidable P] (Q : ChainIndex → Prop) [DecidablePred Q] :
    (if P ∨ ∃ i, Q i then (1 : ℝ≥0∞) else 0) ≤ (if P then 1 else 0) + ∑ i, if Q i then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos (Or.inl hP), if_pos hP]
    exact le_self_add
  · by_cases hQ : ∃ i, Q i
    · obtain ⟨i, hi⟩ := hQ
      rw [if_pos (Or.inr ⟨i, hi⟩), if_neg hP, zero_add]
      calc (1 : ℝ≥0∞) = if Q i then 1 else 0 := by rw [if_pos hi]
        _ ≤ _ := Finset.single_le_sum (f := fun i => if Q i then (1 : ℝ≥0∞) else 0) (fun _ _ => bot_le)
            (Finset.mem_univ i)
    · rw [if_neg (by tauto)]
      exact bot_le

/-! ### Encoding inputs -/

/-- **Encoding inputs at a landed leaf.** The first-order hit, a marker at a contacted chain, and
the arming by a new marker. -/
theorem step_enc (hρ : K.ρ ≤ 2) (y : ℕ) {s : St} {x : HashInput} (hx : s.cache x = none)
    (hi : K.initial x = none) {l : Index} {msg : Digest} {ctr : Counter} (hl : Landed K.p l)
    (hxE : x = Wots.encodingInput K.p topLayer rootTree l msg ctr) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y r.2 ≤ K.pot y s + (ν * K.kindUnit x +
      ν * (if K.Bad s then 0 else 63 * ∑ i, (if (K.ContactB s l i).Nonempty then (1 : ℝ≥0∞) else 0)) +
      ν * (((y : ℝ≥0∞) * ν) * (if K.Armed s then 0 else 4032 * ENNReal.ofReal (2 - K.ρ)))) := by
  set PI := ∑ c : Coordinate, if K.tg.kind x = .hidden c ∧ s.known c = none then ν else 0 with hPI
  have h := K.mean_store y hx 0 (fun t => ((if ¬K.Bad s ∧ Fatal (K.tg.kind x) s.known t then 1 else 0) + PI) +
      (if K.Bad s then 0 else ∑ i, if (K.ContactB s l i).Nonempty ∧ t ∈ K.markSet l i then 1 else 0) +
      ((y : ℝ≥0∞) * ν) * (if ¬K.Armed s ∧ t ∈ K.markAll l then ENNReal.ofReal (2 - K.ρ) else 0))
    (fun u => ?_)
  · rw [add_zero] at h
    refine h.trans (add_le_add le_rfl ?_)
    rw [meanD_add, meanD_add, meanD_add, meanD_const, meanD_mul]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · refine le_trans (add_le_add (meanD_mono fun t => ?_) le_rfl) (K.fo_mean s x)
      by_cases h1 : Fatal (K.tg.kind x) s.known t
      · rw [if_pos h1]
        split_ifs <;> simp
      · rw [if_neg h1, if_neg (fun h => h1 h.2)]
    · by_cases hb : K.Bad s
      · simp only [hb, if_true, meanD_const, mul_zero, le_refl]
      · simp only [hb, if_false]
        rw [meanD_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hne : (K.ContactB s l i).Nonempty
        · rw [if_pos hne, mul_one]
          refine (meanD_ite_le _ (K.markSet l i) (fun t ht => ht.2) 1).trans ?_
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (K.markSet_card l i) bot_le
        · rw [if_neg hne, mul_zero, mul_zero]
          have h0 : (fun t => if (K.ContactB s l i).Nonempty ∧ t ∈ K.markSet l i then (1 : ℝ≥0∞) else 0) =
              fun _ => 0 := funext fun t => if_neg fun h => hne h.1
          rw [h0, meanD_const]
    · rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      by_cases ha : K.Armed s
      · simp [ha, meanD_const]
      · simp only [ha, if_false, not_false_eq_true, true_and]
        refine (meanD_ite_le _ (K.markAll l) (fun t ht => ht) _).trans ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (K.markAll_card l) bot_le) bot_le
  · set s' := s.store x u with hs'
    set t := truncateHash u with ht
    have hnotA : ∀ l' i', ¬K.IsA l' i' x := fun l' i' hA => isA_ne_enc hA l msg ctr hxE
    have hnotB : ∀ l' i' v, ¬K.IsB l' i' v x := fun l' i' v hB => isB_ne_enc hB l msg ctr hxE
    have hnotF : ∀ index tree leaf secret, x ≠ forsLeafInput K.p index tree leaf secret := fun _ _ _ _ he =>
      enc_ne_fors (hxE.symm.trans he)
    have hsame : ∀ l', Landed K.p l' → l' ≠ l → K.SameLeaf s s' l' := fun l' _ hne =>
      K.sameLeaf_store u hx hi l' (hnotA l') (hnotB l')
        (fun msg' ctr' he => hne (enc_inj (hxE.symm.trans he)).1.symm)
    have hCB : ∀ i', K.ContactB s' l i' = K.ContactB s l i' := fun i' => by
      rw [K.contactB_store u hx hi]
      exact Set.union_eq_left.2 fun v hv => absurd hv.1 (hnotB l i' v)
    have hAAeq : ∀ i', K.AAns s' l i' = K.AAns s l i' := fun i' => by
      rw [K.aAns_store u hx hi, if_neg (hnotA l i')]
    have hMk : ∀ i', K.Marker s' l i' ↔ K.Marker s l i' ∨ t ∈ K.markSet l i' := fun i' => by
      rw [K.marker_store u hx hi]
      exact ⟨fun h => h.imp_right fun h' => h'.2, fun h => h.imp_right fun h' => ⟨⟨msg, ctr, hxE⟩, h'⟩⟩
    have hmono : K.BadLeaf s l → K.BadLeaf s' l := K.badLeaf_store_of u hx hi
    have hbad : K.BadLeaf s' l → K.BadLeaf s l ∨ ∃ i, (K.ContactB s l i).Nonempty ∧ t ∈ K.markSet l i := by
      rintro (⟨i₀, hw⟩ | ⟨i₀, hne, hm⟩ | ⟨i₁, i₂, hne, h1, h2⟩)
      · rw [hCB, hAAeq] at hw
        exact Or.inl (Or.inl ⟨i₀, hw⟩)
      · rw [hCB] at hne
        rcases (hMk i₀).1 hm with hm | hm
        · exact Or.inl (Or.inr (Or.inl ⟨i₀, hne, hm⟩))
        · exact Or.inr ⟨i₀, hne, hm⟩
      · rw [hCB] at h1 h2
        exact Or.inl (Or.inr (Or.inr ⟨i₁, i₂, hne, h1, h2⟩))
    have harm : K.ArmedAt s' l → K.ArmedAt s l ∨ t ∈ K.markAll l := by
      rintro ⟨hn, hr⟩
      have hn' : ¬K.BadLeaf s l := fun h => hn (hmono h)
      rcases hr with ⟨i₀, hm⟩ | ⟨i₀, hc⟩
      · rcases (hMk i₀).1 hm with hm | hm
        · exact Or.inl ⟨hn', Or.inl ⟨i₀, hm⟩⟩
        · exact Or.inr (K.markSet_subset l i₀ hm)
      · rw [hCB] at hc
        exact Or.inl ⟨hn', Or.inr ⟨i₀, hc⟩⟩
    have hFC : ∀ index tree leaf secret,
        K.FContact s' index tree leaf secret ↔ K.FContact s index tree leaf secret := by
      intro index tree leaf secret
      rw [K.fContact_store u hx hi]
      exact ⟨fun h => h.resolve_right fun h' => hnotF _ _ _ _ h'.1, Or.inl⟩
    obtain ⟨hRev, hTwo, hKF⟩ := K.fors_same hFC rfl
    have hreal := realized_store K.tg K.initial s x u hx hi
    rw [K.trunc_eq] at hreal
    have hD := K.done_le (s := s) (s' := s')
      (Fatal (K.tg.kind x) s.known t ∨ ∃ i, (K.ContactB s l i).Nonempty ∧ t ∈ K.markSet l i) (by
      rintro (hr | hw | hrev | htwo)
      · rcases hreal.1 hr with hr | hf
        · exact Or.inl (Or.inl hr)
        · exact Or.inr (Or.inl hf)
      · rcases K.wotsBad_of_same l hsame hw with hw | ⟨-, hb⟩
        · exact Or.inl (Or.inr (Or.inl hw))
        · rcases hbad hb with hb | hm
          · exact Or.inl (Or.inr (Or.inl ⟨l, hl, hb⟩))
          · exact Or.inr (Or.inr hm)
      · exact Or.inl (Or.inr (Or.inr (Or.inl (hRev.1 hrev))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (hTwo.1 htwo)))))
    have hP := K.pend_store u hx hi
    have hU := K.ua_le_of_subset (K.uaSet_store_of_not u hx hi fun l' i' _ => hnotA l' i')
    have hV := K.vrate_le hρ (s := s) (s' := s') (t ∈ K.markAll l) fun ha => by
      rcases K.armed_of_same l hsame ha with ha | ⟨hl', ha⟩
      · exact Or.inl ha
      · rcases harm ha with ha | hm
        · exact Or.inl ⟨l, hl', ha⟩
        · exact Or.inr hm
    have hC := K.contactCount_of_same l hsame 0 fun _ => by rw [add_zero]; exact K.leafCount_le_of hCB hmono
    have hR := K.rate_le (dK := 0) hV hC (by rw [hKF, add_zero])
    have := K.pot_le (cr := 0) (dU := 0) y hD hP (by rw [add_zero, add_zero]; exact hU) hR
    refine this.trans (add_le_add le_rfl ?_)
    simp only [mul_zero, add_zero]
    refine add_le_add ?_ le_rfl
    have hdD : (if ¬K.Bad s ∧ (Fatal (K.tg.kind x) s.known t ∨ ∃ i, (K.ContactB s l i).Nonempty ∧
        t ∈ K.markSet l i) then (1 : ℝ≥0∞) else 0) ≤ (if ¬K.Bad s ∧ Fatal (K.tg.kind x) s.known t then 1 else 0) +
        (if K.Bad s then 0 else ∑ i, if (K.ContactB s l i).Nonempty ∧ t ∈ K.markSet l i then 1 else 0) := by
      by_cases hb : K.Bad s
      · simp [hb]
      · simp only [hb, not_false_eq_true, true_and, if_false]
        exact ite_or_le _ _
    calc _ ≤ ((if ¬K.Bad s ∧ Fatal (K.tg.kind x) s.known t then 1 else 0) +
          (if K.Bad s then 0 else ∑ i, if (K.ContactB s l i).Nonempty ∧ t ∈ K.markSet l i then 1 else 0)) + PI :=
          add_le_add hdD le_rfl
      _ = _ := by ring

/-! ### Inputs one step below the word -/

/-- **One step below the word.** A frontier answer is a two-edge event when the payload is an
observed answer, a WOTS event at a marked or second chain, and otherwise a new contact at a
clean leaf, arming the state. An observed payload uses up one credit. -/
theorem step_B (hρ : K.ρ ≤ 2) (y : ℕ) {s : St} {x : HashInput} (hx : s.cache x = none)
    (hi : K.initial x = none) {l : Index} {i : ChainIndex} {v : Digest} (hl : Landed K.p l)
    (hB : K.IsB l i v x) (hk : K.tg.kind x = .none) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y r.2 + (if v ∈ K.AAns s l i then ν / 2 else 0) ≤ K.pot y s +
      ν * (if K.BadLeaf s l ∨ v ∈ K.AAns s l i ∨ K.Marker s l i ∨ ∃ i', i' ≠ i ∧ (K.ContactB s l i').Nonempty
        then (if K.Bad s then 0 else 1)
        else ((y : ℝ≥0∞) * ν) * ((if K.Armed s then 0 else ENNReal.ofReal (2 - K.ρ)) + 64)) := by
  set BL := K.BadLeaf s l ∨ v ∈ K.AAns s l i ∨ K.Marker s l i ∨ ∃ i', i' ≠ i ∧ (K.ContactB s l i').Nonempty
    with hBL
  set c : ℝ≥0∞ := if BL then (if K.Bad s then 0 else 1)
    else ((y : ℝ≥0∞) * ν) * ((if K.Armed s then 0 else ENNReal.ofReal (2 - K.ρ)) + 64) with hc
  have h := K.mean_store y hx (if v ∈ K.AAns s l i then ν / 2 else 0)
    (fun t => if t = K.front l i then c else 0) (fun u => ?_)
  · refine h.trans (le_of_eq ?_)
    rw [meanD_ite_eq _ (fun t => t = K.front l i) (fun t => Iff.rfl)]
  · set s' := s.store x u with hs'
    set t := truncateHash u with ht
    have hnotA : ∀ l' i', ¬K.IsA l' i' x := fun l' i' hA => isA_not_isB hA hB
    have hnotE : ∀ l' msg ctr, x ≠ Wots.encodingInput K.p topLayer rootTree l' msg ctr :=
      fun l' msg ctr => isB_ne_enc hB l' msg ctr
    have hnotF : ∀ index tree leaf secret, x ≠ forsLeafInput K.p index tree leaf secret := isB_ne_fors hB
    have hsame : ∀ l', Landed K.p l' → l' ≠ l → K.SameLeaf s s' l' := fun l' _ hne =>
      K.sameLeaf_store u hx hi l' (hnotA l') (fun i' v' hB' => hne (isB_unique hB' hB).1) (hnotE l')
    have hAAeq : ∀ i', K.AAns s' l i' = K.AAns s l i' := fun i' => by
      rw [K.aAns_store u hx hi, if_neg (hnotA l i')]
    have hMk : ∀ i', K.Marker s' l i' ↔ K.Marker s l i' := fun i' => by
      rw [K.marker_store u hx hi]
      exact ⟨fun h => h.resolve_right fun ⟨⟨msg, ctr, he⟩, _⟩ => hnotE l msg ctr he, Or.inl⟩
    have hCBne : ∀ i', i' ≠ i → K.ContactB s' l i' = K.ContactB s l i' := fun i' hne => by
      rw [K.contactB_store u hx hi]
      exact Set.union_eq_left.2 fun w hw => absurd (isB_unique hw.1 hB).2.1 hne
    have hCBi : K.ContactB s' l i = K.ContactB s l i ∪ {w | w = v ∧ t = K.front l i} := by
      rw [K.contactB_store u hx hi]
      congr 1
      ext w
      simp only [Set.mem_setOf_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨(isB_unique h1 hB).2.2, h2⟩, fun ⟨h1, h2⟩ => ⟨h1 ▸ hB, h2⟩⟩
    have hvCB : v ∉ K.ContactB s l i := fun h => not_mem_bPay hx hB (K.contactB_subset_bPay l i h)
    have hmono : K.BadLeaf s l → K.BadLeaf s' l := K.badLeaf_store_of u hx hi
    have hFC : ∀ index tree leaf secret,
        K.FContact s' index tree leaf secret ↔ K.FContact s index tree leaf secret := by
      intro index tree leaf secret
      rw [K.fContact_store u hx hi]
      exact ⟨fun h => h.resolve_right fun h' => hnotF _ _ _ _ h'.1, Or.inl⟩
    obtain ⟨hRev, hTwo, hKF⟩ := K.fors_same hFC rfl
    have hreal := realized_store_of_none K.tg K.initial s x u hx hi hk
    have hP : K.pend s' ≤ K.pend s + 0 := by rw [add_zero, K.pend_store_none u hx hi hk]
    have hUsub : K.UAset s' ⊆ K.UAset s := K.uaSet_store_of_not u hx hi fun l' i' _ => hnotA l' i'
    have hU : ν / 2 * ((K.UAset s').encard : ℝ≥0∞) + (if v ∈ K.AAns s l i then ν / 2 else 0) ≤
        ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + 0 := by
      split_ifs with hobs
      · obtain ⟨y₁, u₁, hA₁, hfr₁, ht₁⟩ := hobs
        refine (K.ua_strict hUsub (y := y₁) ?_ ?_).trans (le_of_eq (add_zero _).symm)
        · exact ⟨l, i, u₁, hl, hA₁, hfr₁, ht₁ ▸ not_mem_bPay hx hB⟩
        · rintro ⟨l₂, i₂, u₂, -, hA₂, hfr₂, hnot⟩
          obtain ⟨rfl, rfl⟩ := isA_unique hA₁ hA₂
          have hfr₁' := K.fr_store_of u hx hi hfr₁
          have hu : u₂ = u₁ := Option.some.inj (hfr₂.1.symm.trans hfr₁'.1)
          apply hnot
          rw [K.bPay_store u hx hi, hu, ht₁]
          exact Or.inr hB
      · rw [add_zero, add_zero]
        exact K.ua_le_of_subset hUsub
    by_cases hfront : t = K.front l i
    · have hCBi' : K.ContactB s' l i = insert v (K.ContactB s l i) := by
        rw [hCBi]
        ext w
        simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, hfront, and_true]
        exact or_comm
      have hbl : K.BadLeaf s' l ↔ BL := by
        constructor
        · rintro (⟨i₀, w, hw1, hw2⟩ | ⟨i₀, hne, hm⟩ | ⟨i₁, i₂, hne, h1, h2⟩)
          · rw [hAAeq] at hw2
            by_cases hii : i₀ = i
            · rw [hii] at hw1 hw2
              rw [hCBi'] at hw1
              rcases hw1 with rfl | hw1
              · exact Or.inr (Or.inl hw2)
              · exact Or.inl (Or.inl ⟨i, w, hw1, hw2⟩)
            · rw [hCBne i₀ hii] at hw1
              exact Or.inl (Or.inl ⟨i₀, w, hw1, hw2⟩)
          · rw [hMk] at hm
            by_cases hii : i₀ = i
            · rw [hii] at hm
              exact Or.inr (Or.inr (Or.inl hm))
            · rw [hCBne i₀ hii] at hne
              exact Or.inl (Or.inr (Or.inl ⟨i₀, hne, hm⟩))
          · by_cases h1i : i₁ = i
            · rw [h1i] at hne
              rw [hCBne i₂ (Ne.symm hne)] at h2
              exact Or.inr (Or.inr (Or.inr ⟨i₂, Ne.symm hne, h2⟩))
            · by_cases h2i : i₂ = i
              · rw [hCBne i₁ h1i] at h1
                exact Or.inr (Or.inr (Or.inr ⟨i₁, h1i, h1⟩))
              · rw [hCBne i₁ h1i] at h1
                rw [hCBne i₂ h2i] at h2
                exact Or.inl (Or.inr (Or.inr ⟨i₁, i₂, hne, h1, h2⟩))
        · rintro (hb | hobs | hm | ⟨i', hne, h'⟩)
          · exact hmono hb
          · exact Or.inl ⟨i, v, by rw [hCBi']; exact Set.mem_insert _ _, by rw [hAAeq]; exact hobs⟩
          · exact Or.inr (Or.inl ⟨i, ⟨v, by rw [hCBi']; exact Set.mem_insert _ _⟩, (hMk i).2 hm⟩)
          · exact Or.inr (Or.inr ⟨i, i', Ne.symm hne, ⟨v, by rw [hCBi']; exact Set.mem_insert _ _⟩,
              by rw [hCBne i' hne]; exact h'⟩)
      by_cases hBLc : BL
      · have hb' : K.BadLeaf s' l := hbl.2 hBLc
        have hD := K.done_le (s := s) (s' := s') True (fun _ => Or.inr trivial)
        have hV := K.vrate_le_self hρ (s := s) (s' := s') fun ha => by
          rcases K.armed_of_same l hsame ha with ha | ⟨-, hn, -⟩
          · exact ha
          · exact absurd hb' hn
        have hC := K.contactCount_of_same l hsame 0 fun _ => by
          rw [add_zero]
          unfold leafCount
          rw [if_pos hb']
          exact bot_le
        have hR := K.rate_le (dV := 0) (dK := 0) (by rw [add_zero]; exact hV) hC (by rw [hKF, add_zero])
        have := K.pot_le y hD hP hU hR
        refine this.trans (add_le_add le_rfl (le_of_eq ?_))
        rw [if_pos hfront, hc, if_pos hBLc]
        by_cases hb : K.Bad s <;> simp [hb]
      · have hnb' : ¬K.BadLeaf s' l := fun h => hBLc (hbl.1 h)
        have hnb : ¬K.BadLeaf s l := fun h => hBLc (Or.inl h)
        have hD := K.done_le (s := s) (s' := s') False (by
          rintro (hr | hw | hrev | htwo)
          · exact Or.inl (Or.inl (hreal.1 hr))
          · rcases K.wotsBad_of_same l hsame hw with hw | ⟨-, hb⟩
            · exact Or.inl (Or.inr (Or.inl hw))
            · exact absurd hb hnb'
          · exact Or.inl (Or.inr (Or.inr (Or.inl (hRev.1 hrev))))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (hTwo.1 htwo)))))
        have hV := K.vrate_le hρ (s := s) (s' := s') True fun _ => Or.inr trivial
        have hleaf : K.leafCount s' l = K.leafCount s l + 1 := by
          unfold leafCount
          rw [if_neg hnb', if_neg hnb, Fintype.sum_eq_add_sum_compl i,
            Fintype.sum_eq_add_sum_compl i (f := fun i₀ => ((K.ContactB s l i₀).encard : ℝ≥0∞)), hCBi',
            Set.encard_insert_of_notMem hvCB, ENat.toENNReal_add, ENat.toENNReal_one,
            Finset.sum_congr rfl fun i₀ hi₀ => by rw [hCBne i₀ (by simpa using hi₀)]]
          ring
        have hC := K.contactCount_of_same l hsame 1 fun _ => le_of_eq hleaf
        have hR := K.rate_le (dK := 0) hV hC (by rw [hKF, add_zero])
        have := K.pot_le y hD hP hU hR
        refine this.trans (add_le_add le_rfl (le_of_eq ?_))
        rw [if_pos hfront, hc, if_neg hBLc]
        by_cases ha : K.Armed s <;> simp [ha]
    · have hCBi' : K.ContactB s' l i = K.ContactB s l i := by
        rw [hCBi]
        ext w
        simp [hfront]
      have hsameAll : ∀ l', Landed K.p l' → K.SameLeaf s s' l' := fun l' hl' => by
        by_cases hll : l' = l
        · rw [hll]
          refine ⟨fun i' => ?_, hAAeq, hMk⟩
          by_cases hii : i' = i
          · rw [hii]
            exact hCBi'
          · exact hCBne i' hii
        · exact hsame l' hl' hll
      obtain ⟨hW, hA, hC⟩ := K.wots_of_allSame hsameAll
      have hD := K.done_le (s := s) (s' := s') False (by
        rintro (hr | hw | hrev | htwo)
        · exact Or.inl (Or.inl (hreal.1 hr))
        · exact Or.inl (Or.inr (Or.inl (hW.1 hw)))
        · exact Or.inl (Or.inr (Or.inr (Or.inl (hRev.1 hrev))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (hTwo.1 htwo)))))
      have hR : K.rate s' ≤ K.rate s + 0 := by rw [add_zero, K.rate_eq_of hA hC hKF]
      have := K.pot_le y hD hP hU hR
      refine this.trans (add_le_add le_rfl (le_of_eq ?_))
      rw [if_neg hfront]
      simp

end Ctx

end LeanSphincs.Security.PotentialA
