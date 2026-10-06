import LeanSphincs.BridgeEventsA
import LeanSphincs.BridgeForsNear
import LeanSphincs.BridgeForsAssemblyOnce

/-! FORS contacts made while the leaf secret was unknown. A FORS leaf query at an unexposed secret
records the guess `(ftsSecret P, secret)` and is answered by the outside oracle; it is a contact
when its cached answer truncates to the known leaf value. Contacts appear only at such queries on
fresh inputs, each with probability at most `2^-128`; every other step, and every computation that
never queries a FORS leaf input (the signer), keeps them. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Contacts -/

section Defs

variable (parameter : PublicParameter) (K : HiddenReveal.Knowledge Coordinate)

/-- A recorded FORS guess whose cached leaf answer truncates to the known leaf value. -/
def IsContact (s : State) (g : Coordinate × Digest) : Prop :=
  ∃ index tree leaf ans, g.1 = .ftsSecret index tree leaf ∧
    s.cache (HiddenBridge.forsLeafInput parameter index tree leaf g.2) = some ans ∧
    K (.ftsValue index tree leaf) = some (truncateHash ans)

/-- **The contacts of a state.** -/
noncomputable def contacts (s : State) : Finset (Coordinate × Digest) :=
  s.guesses.toFinset.filter (IsContact parameter K s)

/-- A contact made while the secret of the leaf was unknown (the spec's `GRContact`). -/
def GRContact (s : State) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : Prop :=
  ∃ secret ans, s.cache (HiddenBridge.forsLeafInput parameter index tree leaf secret) = some ans ∧
    (Coordinate.ftsSecret index tree leaf, secret) ∈ s.guesses ∧
    K (.ftsValue index tree leaf) = some (truncateHash ans)

omit [Params] in
theorem mem_contacts_of_GR {s : State} {index : Index} {tree : FtsTree} {leaf : FtsLeaf}
    (h : GRContact parameter K s index tree leaf) :
    ∃ secret, (Coordinate.ftsSecret index tree leaf, secret) ∈ contacts parameter K s := by
  obtain ⟨secret, ans, hc, hg, hK⟩ := h
  exact ⟨secret, Finset.mem_filter.2 ⟨List.mem_toFinset.2 hg, index, tree, leaf, ans, rfl, hc, hK⟩⟩

/-- Some input of any public parameter at a FORS leaf. -/
def IsFLInput (x : HashInput) : Prop :=
  ∃ (parameter' : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (payload : HashInput),
    x = tweakableHashInput parameter' (.ftsLeaf index tree leaf) payload

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- FORS rows parse only from FORS leaf inputs. -/
def FtsRows : Prop :=
  ∀ x a v index tree leaf, model.parse x = some (a, v) → model.incoming a = .ftsSecret index tree leaf →
    x = HiddenBridge.forsLeafInput parameter index tree leaf v

/-- **The contact invariant.** Recorded FORS guesses have cached inputs; a cached FORS row input whose
secret is unknown was guessed. -/
structure CInv (s : State) : Prop where
  guessed : ∀ index tree leaf v, (Coordinate.ftsSecret index tree leaf, v) ∈ s.guesses →
    s.cache (HiddenBridge.forsLeafInput parameter index tree leaf v) ≠ none
  cached : ∀ x a v index tree leaf, model.parse x = some (a, v) → model.incoming a = .ftsSecret index tree leaf →
    s.cache x ≠ none → s.known (.ftsSecret index tree leaf) = none →
      (Coordinate.ftsSecret index tree leaf, v) ∈ s.guesses

end Defs

section Basic

variable {parameter : PublicParameter} {K : HiddenReveal.Knowledge Coordinate}

omit [Params] in
theorem isContact_mono {s s' : State} (hext : Extends s s') {g : Coordinate × Digest}
    (h : IsContact parameter K s g) : IsContact parameter K s' g := by
  obtain ⟨i, t, l, ans, hg, hc, hK⟩ := h
  exact ⟨i, t, l, ans, hg, hext.1 _ _ hc, hK⟩

omit [Params] in
/-- Contacts only grow. -/
theorem contacts_mono {s s' : State} (hext : Extends s s') : contacts parameter K s ⊆ contacts parameter K s' := by
  intro g hg
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.1 hg
  exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 (hext.2.2 g (List.mem_toFinset.1 hmem)), isContact_mono hext hc⟩

omit [Params] in
/-- A new cache entry away from the guessed FORS inputs keeps the contacts. -/
theorem isContact_store_iff {s : State}
    (hg : ∀ i t l v, (Coordinate.ftsSecret i t l, v) ∈ s.guesses →
      s.cache (HiddenBridge.forsLeafInput parameter i t l v) ≠ none)
    {x : HashInput} (hx : s.cache x = none) (u : HashOutput) {g : Coordinate × Digest} (hgm : g ∈ s.guesses) :
    IsContact parameter K (s.store x u) g ↔ IsContact parameter K s g := by
  have hne : ∀ i t l, g.1 = .ftsSecret i t l → HiddenBridge.forsLeafInput parameter i t l g.2 ≠ x := by
    intro i t l hc heq
    have h := hg i t l g.2 (by rw [← hc]; exact hgm)
    rw [heq, hx] at h
    exact h rfl
  constructor
  · rintro ⟨i, t, l, ans, hc, hcache, hK⟩
    refine ⟨i, t, l, ans, hc, ?_, hK⟩
    rwa [store_cache_ne s x _ (hne i t l hc) u] at hcache
  · rintro ⟨i, t, l, ans, hc, hcache, hK⟩
    refine ⟨i, t, l, ans, hc, ?_, hK⟩
    rwa [store_cache_ne s x _ (hne i t l hc) u]

omit [Params] in
theorem contacts_store {s : State}
    (hg : ∀ i t l v, (Coordinate.ftsSecret i t l, v) ∈ s.guesses →
      s.cache (HiddenBridge.forsLeafInput parameter i t l v) ≠ none)
    {x : HashInput} (hx : s.cache x = none) (u : HashOutput) :
    contacts parameter K (s.store x u) = contacts parameter K s := by
  unfold contacts
  exact Finset.filter_congr fun g hgm => isContact_store_iff hg hx u (List.mem_toFinset.1 hgm)

omit [Params] in
theorem contacts_record_of_mem {s : State} {g0 : Coordinate × Digest} (h : g0 ∈ s.guesses) :
    contacts parameter K (s.record g0) = contacts parameter K s := by
  unfold contacts
  have hfin : (s.record g0).guesses.toFinset = s.guesses.toFinset := by
    show (g0 :: s.guesses).toFinset = _
    rw [List.toFinset_cons, Finset.insert_eq_of_mem (List.mem_toFinset.2 h)]
  rw [hfin]
  rfl

omit [Params] in
theorem contacts_record_of_not {s : State} {g0 : Coordinate × Digest} (h : ¬IsContact parameter K s g0) :
    contacts parameter K (s.record g0) = contacts parameter K s := by
  unfold contacts
  show (g0 :: s.guesses).toFinset.filter (IsContact parameter K s) = _
  rw [List.toFinset_cons, Finset.filter_insert, if_neg h]

omit [Params] in
/-- After a recorded guess and a fresh entry, every contact is old or the guess. -/
theorem contacts_record_store_sub {s : State}
    (hg : ∀ i t l v, (Coordinate.ftsSecret i t l, v) ∈ s.guesses →
      s.cache (HiddenBridge.forsLeafInput parameter i t l v) ≠ none)
    {x : HashInput} (hx : s.cache x = none) (g0 : Coordinate × Digest) (u : HashOutput) :
    ∀ g ∈ contacts parameter K ((s.record g0).store x u), g ∈ contacts parameter K s ∨ g = g0 := by
  intro g hg'
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.1 hg'
  have hmem' : g = g0 ∨ g ∈ s.guesses := by
    have : g ∈ g0 :: s.guesses := List.mem_toFinset.1 hmem
    exact List.mem_cons.1 this
  rcases hmem' with h | h
  · exact Or.inr h
  · left
    refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 h, ?_⟩
    have hc' : IsContact parameter K (s.store x u) g := hc
    exact (isContact_store_iff hg hx u h).1 hc'

end Basic

/-! ### One ordinary query -/

section Step

variable {parameter : PublicParameter} {K : HiddenReveal.Knowledge Coordinate} {A : Type}
  {model : HiddenRows.Model HashInput HashOutput A Coordinate}

omit [Params] in
/-- The support of one ordinary step: an outside read, a recorded guess, or an exposure. -/
theorem ordinaryStep_shape (bytes : HashInput) (s : State) (r : HashOutput × State)
    (hr : r ∈ support (ordinaryStep model bytes s.known s)) :
    ((∀ a v, model.parse bytes = some (a, v) → s.known (model.incoming a) ≠ none) ∧
      (r.2 = s ∨ (s.cache bytes = none ∧ r.2 = s.store bytes r.1))) ∨
    (∃ a v, model.parse bytes = some (a, v) ∧ s.known (model.incoming a) = none ∧
      ((s.cache bytes ≠ none ∧ r.2 = s.record (model.incoming a, v)) ∨
        (s.cache bytes = none ∧ r.2 = (s.record (model.incoming a, v)).store bytes r.1))) ∨
    (∃ c val, r.2 = s.expose c val) := by
  cases hp : model.parse bytes with
  | none =>
      simp only [ordinaryStep, hp] at hr
      left
      exact ⟨fun a v h => (by cases h), readOutside_support bytes s r hr⟩
  | some query =>
      obtain ⟨a, v⟩ := query
      cases hk : s.known (model.incoming a) with
      | none =>
          simp only [ordinaryStep, hp, hk] at hr
          right; left
          refine ⟨a, v, rfl, hk, ?_⟩
          cases hc : s.cache bytes with
          | some out =>
              have hc' : (s.record (model.incoming a, v)).cache bytes = some out := hc
              rw [readOutside_cached bytes _ out hc', support_pure, Set.mem_singleton_iff] at hr
              left
              exact ⟨by simp, by rw [hr]⟩
          | none =>
              have hc' : (s.record (model.incoming a, v)).cache bytes = none := hc
              rw [readOutside_fresh bytes _ hc', support_map] at hr
              obtain ⟨u, _, rfl⟩ := hr
              right
              exact ⟨rfl, rfl⟩
      | some canonical =>
          by_cases heq : v = canonical
          · simp only [ordinaryStep, hp, hk, if_pos heq] at hr
            right; right
            rw [support_map] at hr
            obtain ⟨res, hres, rfl⟩ := hr
            exact ⟨_, _, sampleCoordinate_expose _ s res hres⟩
          · simp only [ordinaryStep, hp, hk, if_neg heq] at hr
            left
            refine ⟨fun a' v' h => ?_, readOutside_support bytes s r hr⟩
            cases h
            rw [hk]
            exact Option.some_ne_none _

omit [Params] in
theorem cache_ne_of_extends {s s' : State} (hext : Extends s s') {x : HashInput} (h : s.cache x ≠ none) :
    s'.cache x ≠ none := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 h
  rw [hext.1 x u hu]
  exact Option.some_ne_none _

omit [Params] in
theorem known_none_of_expose {s : State} {c y : Coordinate} {val : Digest}
    (h : (s.expose c val).known y = none) : s.known y = none := by
  by_cases hy : y = c
  · subst hy
    simp [DebtState.expose, QueryCache.cacheQuery_self] at h
  · have h' : (s.expose c val).known y = s.known y := by
      simp only [DebtState.expose]
      convert QueryCache.cacheQuery_of_ne (cache := s.known) val hy
    rwa [h'] at h

omit [Params] in
/-- **One ordinary query.** The invariant is kept, contacts only grow, and a new contact is the
guess of this query, at an unknown secret, on a fresh input, whose answer truncates to the known
leaf value. -/
theorem ordinary_contacts (hrows : FtsRows parameter model) (bytes : HashInput) (s : State)
    (hinv : CInv parameter model s) (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model bytes s.known s)) :
    CInv parameter model r.2 ∧ contacts parameter K s ⊆ contacts parameter K r.2 ∧
      ∀ g ∈ contacts parameter K r.2, g ∉ contacts parameter K s →
        ∃ a i t l, model.parse bytes = some (a, g.2) ∧ model.incoming a = g.1 ∧ g.1 = .ftsSecret i t l ∧
          s.known g.1 = none ∧ s.cache bytes = none ∧ K (.ftsValue i t l) = some (truncateHash r.1) := by
  rcases ordinaryStep_shape bytes s r hr with ⟨hother, hr2 | ⟨hc, hr2⟩⟩ | ⟨a, v, hp, hk, ⟨hc, hr2⟩ | ⟨hc, hr2⟩⟩ |
      ⟨c, val, hr2⟩
  · rw [hr2]
    exact ⟨hinv, Finset.Subset.refl _, fun g hg hn => absurd hg hn⟩
  · have hext := extends_store s bytes r.1 hc
    have hcon := contacts_store (K := K) hinv.guessed hc r.1
    rw [hr2]
    refine ⟨⟨fun i t l v hv => cache_ne_of_extends hext (hinv.guessed i t l v hv), fun x a v i t l hp hi hx hk => ?_⟩,
      by rw [hcon], fun g hg hn => absurd (hcon ▸ hg) hn⟩
    by_cases hxb : x = bytes
    · subst hxb
      exact absurd (hi ▸ hk) (hother a v hp)
    · rw [show (s.store bytes r.1).cache x = s.cache x from store_cache_ne s bytes x hxb r.1] at hx
      exact hinv.cached x a v i t l hp hi hx hk
  · -- a guess on a cached input
    rw [hr2]
    have hguess : ∀ i t l, model.incoming a = .ftsSecret i t l →
        s.cache (HiddenBridge.forsLeafInput parameter i t l v) ≠ none := by
      intro i t l hi
      rw [← hrows bytes a v i t l hp hi]
      exact hc
    refine ⟨⟨fun i t l v' hv => ?_, fun x a' v' i t l hp' hi hx hk' => List.mem_cons_of_mem _
      (hinv.cached x a' v' i t l hp' hi hx hk')⟩, ?_, ?_⟩
    · rcases List.mem_cons.1 hv with hv | hv
      · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
        subst h2
        exact hguess i t l h1.symm
      · exact hinv.guessed i t l v' hv
    · by_cases hF : ∃ i t l, model.incoming a = .ftsSecret i t l
      · obtain ⟨i, t, l, hi⟩ := hF
        rw [contacts_record_of_mem (by rw [hi]; exact hinv.cached bytes a v i t l hp hi hc (hi ▸ hk))]
      · rw [contacts_record_of_not (fun ⟨i, t, l, _, h1, _⟩ => hF ⟨i, t, l, h1⟩)]
    · intro g hg hn
      by_cases hF : ∃ i t l, model.incoming a = .ftsSecret i t l
      · obtain ⟨i, t, l, hi⟩ := hF
        rw [contacts_record_of_mem (by rw [hi]; exact hinv.cached bytes a v i t l hp hi hc (hi ▸ hk))] at hg
        exact absurd hg hn
      · rw [contacts_record_of_not (fun ⟨i, t, l, _, h1, _⟩ => hF ⟨i, t, l, h1⟩)] at hg
        exact absurd hg hn
  · -- a guess on a fresh input
    have hext : Extends s r.2 := by
      rw [hr2]
      exact (extends_record s _).trans (extends_store _ bytes r.1 hc)
    refine ⟨⟨fun i t l v' hv => ?_, fun x a' v' i t l hp' hi hx hk' => ?_⟩, contacts_mono hext, ?_⟩
    · rw [hr2] at hv ⊢
      rcases List.mem_cons.1 hv with hv | hv
      · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
        rw [h2, ← hrows bytes a v i t l hp h1.symm]
        simp [DebtState.store, DebtState.record, QueryCache.cacheQuery_self]
      · exact cache_ne_of_extends (extends_store _ bytes r.1 hc) (hinv.guessed i t l v' hv)
    · rw [hr2] at hx hk' ⊢
      by_cases hxb : x = bytes
      · subst hxb
        rw [hp] at hp'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
        rw [hi]
        exact List.mem_cons_self ..
      · have hx' : s.cache x ≠ none := by
          have := store_cache_ne (s.record (model.incoming a, v)) bytes x hxb r.1
          rw [this] at hx
          exact hx
        exact List.mem_cons_of_mem _ (hinv.cached x a' v' i t l hp' hi hx' hk')
    · intro g hg hn
      rw [hr2] at hg
      rcases contacts_record_store_sub hinv.guessed hc _ r.1 g hg with h | rfl
      · exact absurd h hn
      · obtain ⟨i, t, l, ans, h1, hcache, hK⟩ := Finset.mem_filter.1 hg |>.2
        have hb := hrows bytes a v i t l hp h1
        have hans : ans = r.1 := by
          simp only at hcache
          rw [← hb] at hcache
          simp [DebtState.store, QueryCache.cacheQuery_self] at hcache
          exact hcache.symm
        subst hans
        exact ⟨a, i, t, l, hp, rfl, h1, hk, hc, hK⟩
  · rw [hr2]
    refine ⟨⟨hinv.guessed, fun x a v i t l hp hi hx hk => hinv.cached x a v i t l hp hi hx
      (known_none_of_expose hk)⟩, Finset.Subset.refl _, fun g hg hn => absurd hg hn⟩

omit [Params] in
/-- **New contacts in expectation.** One ordinary query creates at most `2^-128` contacts on
average. -/
theorem ordinary_contacts_mean (hrows : FtsRows parameter model) (bytes : HashInput) (s : State)
    (hinv : CInv parameter model s) :
    ∑' r, Pr[= r | ordinaryStep model bytes s.known s] *
        ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  by_cases hF : ∃ a v i t l, model.parse bytes = some (a, v) ∧ model.incoming a = .ftsSecret i t l ∧
      s.known (.ftsSecret i t l) = none ∧ s.cache bytes = none
  · obtain ⟨a, v, i, t, l, hp, hi, hk, hc⟩ := hF
    have hk' : s.known (model.incoming a) = none := by rw [hi]; exact hk
    have hstep : ordinaryStep model bytes s.known s = (fun u => (u, (s.record (model.incoming a, v)).store bytes u)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput) := by
      simp only [ordinaryStep, hp, hk']
      exact readOutside_fresh bytes _ hc
    have hpt : ∀ r ∈ support (ordinaryStep model bytes s.known s),
        ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) ≤
          if K (.ftsValue i t l) = some (truncateHash r.1) then 1 else 0 := by
      intro r hr
      have hnew := (ordinary_contacts (K := K) hrows bytes s hinv r hr).2.2
      have hsub : contacts parameter K r.2 \ contacts parameter K s ⊆ {(Coordinate.ftsSecret i t l, v)} := by
        intro g hg
        obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.1 hg
        obtain ⟨a', i', t', l', hp', hi', -, -, -, -⟩ := hnew g hg1 hg2
        rw [hp] at hp'
        obtain ⟨rfl, hv⟩ := Prod.mk.inj (Option.some.inj hp')
        rw [Finset.mem_singleton]
        exact Prod.ext (by rw [← hi', hi]) hv.symm
      by_cases hval : K (.ftsValue i t l) = some (truncateHash r.1)
      · rw [if_pos hval]
        exact_mod_cast le_trans (Finset.card_le_card hsub) (Finset.card_singleton _).le
      · rw [if_neg hval]
        have hempty : contacts parameter K r.2 \ contacts parameter K s = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun g hg => ?_
          obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.1 hg
          obtain ⟨a', i', t', l', hp', hi', hg', -, -, hK⟩ := hnew g hg1 hg2
          rw [hp] at hp'
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hp')
          rw [← hi', hi] at hg'
          obtain ⟨rfl, rfl, rfl⟩ := Coordinate.ftsSecret.inj hg'
          exact hval hK
        rw [hempty]
        simp
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model bytes s.known s] *
          (if K (.ftsValue i t l) = some (truncateHash r.1) then 1 else 0) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model bytes s.known s)
          · exact mul_le_mul_right (hpt r hr) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ = ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if K (.ftsValue i t l) = some (truncateHash u) then 1 else 0) := by
          rw [hstep, tsum_probOutput_map_mul]
      _ ≤ _ := by
          cases hKv : K (.ftsValue i t l) with
          | none => simp
          | some w =>
              have h := probEvent_uniform_truncateHash_eq w
              rw [probEvent_eq_tsum_ite, card_digest, Nat.cast_pow, Nat.cast_ofNat] at h
              rw [← h]
              refine le_of_eq (tsum_congr fun u => ?_)
              by_cases hu : truncateHash u = w
              · simp [hu]
              · have hu' : ¬some w = some (truncateHash u) := fun h' => hu (Option.some.inj h').symm
                simp [hu, hu']
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun r => ?_) bot_le
    by_cases hr : r ∈ support (ordinaryStep model bytes s.known s)
    · have hnew := (ordinary_contacts (K := K) hrows bytes s hinv r hr).2.2
      have hempty : contacts parameter K r.2 \ contacts parameter K s = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun g hg => ?_
        obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.1 hg
        obtain ⟨a', i', t', l', hp', hi', hg', hk, hc, -⟩ := hnew g hg1 hg2
        exact hF ⟨a', g.2, i', t', l', hp', hi'.trans hg', hg' ▸ hk, hc⟩
      rw [hempty]
      simp
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

end Step

/-! ### Computations that query no FORS leaf input -/

section Avoid

variable {parameter : PublicParameter} {K : HiddenReveal.Knowledge Coordinate} {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  {model : HiddenRows.Model HashInput HashOutput A Coordinate}

omit [Params] in
theorem isFLInput_forsLeafInput (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (secret : Digest) : IsFLInput (HiddenBridge.forsLeafInput parameter index tree leaf secret) :=
  ⟨parameter, index, tree, leaf, _, rfl⟩

omit [Params] in
/-- **Avoiding computations.** A computation that queries no FORS leaf input keeps the invariant
and the contacts. -/
theorem interp_contacts_avoid (hrows : FtsRows parameter model) {α : Type}
    (computation : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α)
    (h : Avoids IsFLInput computation) :
    ∀ budget (s : State), CInv parameter model s → ∀ out ∈ support (interp tg initial model computation budget s),
      CInv parameter model out.2 ∧ contacts parameter K out.2 = contacts parameter K s := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget s hinv out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact ⟨hinv, rfl⟩
  | query_bind input next ih =>
      intro budget s hinv out hout
      obtain ⟨hin, hnext⟩ := (avoids_query_bind IsFLInput input next).1 h
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        have hstep : CInv parameter model result.2 ∧ contacts parameter K result.2 = contacts parameter K s := by
          rcases input with (draw | (bytes | coordinate)) | amount
          · change result ∈ support ((fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hresult
            rw [support_map] at hresult
            obtain ⟨v, _, rfl⟩ := hresult
            exact ⟨hinv, rfl⟩
          · rw [costStep_ordinary] at hresult
            obtain ⟨hinv', hsub, hnew⟩ := ordinary_contacts (K := K) hrows bytes s hinv result hresult
            refine ⟨hinv', Finset.Subset.antisymm (fun g hg => ?_) hsub⟩
            by_contra hn
            obtain ⟨a, i, t, l, hp, hi, hg1, -⟩ := hnew g hg hn
            exact hin bytes rfl (hrows bytes a g.2 i t l hp (hi.trans hg1) ▸
              isFLInput_forsLeafInput parameter i t l g.2)
          · change result ∈ support (sampleCoordinate coordinate s) at hresult
            rw [sampleCoordinate_expose _ s result hresult]
            exact ⟨⟨hinv.guessed, fun x a v i t l hp hi hx hk => hinv.cached x a v i t l hp hi hx
              (known_none_of_expose hk)⟩, rfl⟩
          · change result ∈ support (pure ((), s) : ProbComp _) at hresult
            rw [support_pure, Set.mem_singleton_iff] at hresult
            subst hresult
            exact ⟨hinv, rfl⟩
        obtain ⟨hinv', hc'⟩ := hstep
        obtain ⟨h1, h2⟩ := ih result.1 (hnext result.1) _ result.2 hinv' inner hinner
        exact ⟨h1, h2.trans hc'⟩
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact ⟨hinv, rfl⟩

omit [Params] in
/-- Revealed coordinates are exposed at the end of a run. -/
theorem interp_reveals_known {α : Type} (computation : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α) :
    ∀ budget (s : State), ∀ out ∈ support (interp tg initial model computation budget s),
      ∀ c ∈ out.1.2.1, out.2.known c ≠ none := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget s out hout c hc
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      cases hc
  | query_bind input next ih =>
      intro budget s out hout c hc
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        show inner.2.known c ≠ none
        change c ∈ HiddenBridge.revealed input ++ inner.1.2.1 at hc
        rcases List.mem_append.1 hc with hc | hc
        · rcases input with (draw | (bytes | coordinate)) | amount
          · cases hc
          · cases hc
          · simp only [HiddenBridge.revealed, List.mem_singleton] at hc
            subst hc
            change result ∈ support (sampleCoordinate _ s) at hresult
            have hexp := sampleCoordinate_expose _ s result hresult
            have hext := interp_extends tg initial model (next result.1) _ result.2 inner hinner
            have hres : result.2.known c = some result.1 := by
              rw [hexp]
              simp [DebtState.expose, QueryCache.cacheQuery_self]
            rw [hext.2.1 _ _ hres]
            exact Option.some_ne_none _
          · cases hc
        · exact ih result.1 _ result.2 inner hinner c hc
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        cases hc

end Avoid

/-! ### The signer queries no FORS leaf input -/

section Signer

omit [Params] in
theorem not_fl_tweakable (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hdomain : (hashDomainFields domain).tag ≠ 9) : ¬IsFLInput (tweakableHashInput parameter domain payload) := by
  rintro ⟨parameter', index, tree, leaf, payload', heq⟩
  have h := (tweakableInput_injective heq).1
  apply hdomain
  rw [h]
  rfl

theorem avoids_finishRestF (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) IsFLInput
      (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
  refine avoids_bind _ (avoids_liftHash _ _ (noQ_search _ _ _ _ _
    (fun payload => not_fl_tweakable _ _ payload (by simp [hashDomainFields, tweakFields])) _ _)) fun found => ?_
  rcases found with _ | ⟨counter, word⟩
  · exact avoids_pure _ _
  · refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_reveal _ _) fun _ => ?_
    refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_reveal _ _) fun _ => ?_
    exact avoids_bind _ (avoids_tick _ _) fun _ => avoids_pure _ _

/-- The signing walk queries no FORS leaf input. -/
theorem avoids_walkF (parameter : PublicParameter) (data : PublicData) (message : Message) :
    ∀ attempts ρ, Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) IsFLInput
      (signCostSourceWalk parameter data message attempts ρ) := by
  intro attempts
  induction attempts with
  | zero => intro ρ; exact avoids_pure _ _
  | succ attempts ih =>
      intro ρ
      rw [signCostSourceWalk_succ]
      refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun first => ?_⟩
      · cases hb
        exact not_fl_tweakable parameter (.message 0) _ (by simp [hashDomainFields, tweakFields]) hx
      · split_ifs
        · rw [finishCostSource_eq]
          refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun a => ?_⟩
          · cases hb
            exact not_fl_tweakable parameter (.message 0) _ (by simp [hashDomainFields, tweakFields]) hx
          refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun b => ?_⟩
          · cases hb
            exact not_fl_tweakable parameter (.message 1) _ (by simp [hashDomainFields, tweakFields]) hx
          exact avoids_finishRestF parameter data message ρ _
        · exact ih _

/-- **The signing loop queries no FORS leaf input.** -/
theorem avoids_loopF (parameter : PublicParameter) (data : PublicData) (message : Message) (attempts : ℕ) :
    Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) IsFLInput
      (signCostSourceLoop parameter data message attempts) := by
  unfold signCostSourceLoop
  exact avoids_bind _ (avoids_liftProb _ _) fun ρ => avoids_walkF parameter data message attempts ρ

end Signer

end LeanSphincs.Security.ForsPotential
