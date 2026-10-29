import FORS.SWRoute.StepsBase

/-! **The SW route: how one step changes its state predicates.** Recording a guess changes none
of them; a fresh answer changes only the predicates of its input's shape: the WOTS data of its key
(an input one or two steps below the word, or an encoding), the FORS contact of its query, or the
cached pairs (a digest block). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Shapes

variable (K : Ctx)

/-- A FORS leaf query always parses: every FORS leaf is an active row. -/
theorem parse_fleaf (f : FIn) :
    HiddenGraph.parse K.p (candidateActive K.p) (f.input K.p) = some (Address.fleaf f.index f.κ f.leaf, f.v) := by
  rw [← input_fleaf]
  exact parse_input _ _ _ trivial

theorem inputCoordinate_fleaf (f : FIn) : (Address.fleaf f.index f.κ f.leaf).inputCoordinate = f.inC := rfl

theorem outputCoordinate_fleaf (f : FIn) : (Address.fleaf f.index f.κ f.leaf).outputCoordinate = f.outC := rfl

theorem fin_input_inj {f g : FIn} (h : f.input K.p = g.input K.p) : f = g := fleaf_inj h

end Shapes

/-! ### Congruence of the route's predicates -/

section Congr

variable (K : Ctx) (root : Digest)

variable {K} in
theorem wContact_congr {s s' : St} (h : ∀ l, Retained K.p l → K.SameLeaf s s' l) :
    WContact K s' ↔ WContact K s := by
  unfold WContact
  constructor
  · rintro ⟨l, i, hl, hc⟩
    exact ⟨l, i, hl, by rwa [(h l hl).1 i] at hc⟩
  · rintro ⟨l, i, hl, hc⟩
    exact ⟨l, i, hl, by rwa [(h l hl).1 i]⟩

variable {K} in
theorem armedW_congr {s s' : St} (h : ∀ l, Retained K.p l → K.SameLeaf s s' l) :
    ArmedW K s' ↔ ArmedW K s := by
  unfold ArmedW
  constructor
  · rintro ⟨l, hl, ⟨i, hm⟩ | ⟨i, hc⟩⟩
    · exact ⟨l, hl, Or.inl ⟨i, ((h l hl).2.2 i).1 hm⟩⟩
    · exact ⟨l, hl, Or.inr ⟨i, by rwa [(h l hl).1 i] at hc⟩⟩
  · rintro ⟨l, hl, ⟨i, hm⟩ | ⟨i, hc⟩⟩
    · exact ⟨l, hl, Or.inl ⟨i, ((h l hl).2.2 i).2 hm⟩⟩
    · exact ⟨l, hl, Or.inr ⟨i, by rwa [(h l hl).1 i]⟩⟩

variable {K} in
theorem wotsBad_congr {s s' : St} (h : ∀ l, Retained K.p l → K.SameLeaf s s' l) :
    K.WotsBad s' ↔ K.WotsBad s := by
  constructor
  · rintro ⟨l, hl, hb⟩
    exact ⟨l, hl, (K.badLeaf_congr (h l hl)).1 hb⟩
  · rintro ⟨l, hl, hb⟩
    exact ⟨l, hl, (K.badLeaf_congr (h l hl)).2 hb⟩

variable {K} in
theorem fContact_congr {s s' : St} (h : ∀ f, FCk K s' f ↔ FCk K s f) : FContact K s' ↔ FContact K s := by
  unfold FContact
  simp only [h]

variable {K} in
theorem dead_congr {s s' : St} (hw : ∀ l, Retained K.p l → K.SameLeaf s s' l) (hf : ∀ f, FCk K s' f ↔ FCk K s f) :
    Dead K s' ↔ Dead K s := by
  unfold Dead
  rw [wContact_congr hw, fContact_congr hf]
  have hcb : ∀ (l : OtsKey) (i : ChainIndex) (v : Digest), Retained K.p l →
      (v ∈ K.ContactB s' l i ↔ v ∈ K.ContactB s l i) := fun l i v hl => by rw [(hw l hl).1 i]
  constructor
  · rintro (⟨l, i, v, l', i', v', hl, hl', h1, h2, hne⟩ | ⟨f, g, hne, h1, h2⟩ | h3)
    · exact Or.inl ⟨l, i, v, l', i', v', hl, hl', (hcb l i v hl).1 h1, (hcb l' i' v' hl').1 h2, hne⟩
    · exact Or.inr (Or.inl ⟨f, g, hne, (hf f).1 h1, (hf g).1 h2⟩)
    · exact Or.inr (Or.inr h3)
  · rintro (⟨l, i, v, l', i', v', hl, hl', h1, h2, hne⟩ | ⟨f, g, hne, h1, h2⟩ | h3)
    · exact Or.inl ⟨l, i, v, l', i', v', hl, hl', (hcb l i v hl).2 h1, (hcb l' i' v' hl').2 h2, hne⟩
    · exact Or.inr (Or.inl ⟨f, g, hne, (hf f).2 h1, (hf g).2 h2⟩)
    · exact Or.inr (Or.inr h3)

variable {K root} in
theorem nearContact_congr {s s' : St} (hf : ∀ f, FCk K s' f ↔ FCk K s f)
    (hn : ∀ I κ L, NearLeaf K root s' I κ L ↔ NearLeaf K root s I κ L)
    (hk : ∀ c, s'.known c = none ↔ s.known c = none) : NearContact K root s' ↔ NearContact K root s := by
  unfold NearContact
  simp only [hf, hn, ne_eq, hk]

variable {K root} in
theorem badR_congr {s s' : St} (hw : ∀ l, Retained K.p l → K.SameLeaf s s' l) (hf : ∀ f, FCk K s' f ↔ FCk K s f)
    (hn : ∀ I κ L, NearLeaf K root s' I κ L ↔ NearLeaf K root s I κ L)
    (hk : ∀ c, s'.known c = none ↔ s.known c = none) : BadR K root s' ↔ BadR K root s := by
  unfold BadR
  rw [wotsBad_congr hw, dead_congr hw hf, nearContact_congr hf hn hk]

variable {K} in
theorem expo_congr (ρ : ℝ) (flag : Bool) {s s' : St} (hw : ∀ l, Retained K.p l → K.SameLeaf s s' l)
    (hf : ∀ f, FCk K s' f ↔ FCk K s f) : expo K ρ flag s' = expo K ρ flag s := by
  unfold expo ArmedS
  rw [armedW_congr hw, fContact_congr hf, wContact_congr hw]

end Congr

/-! ### Recording a guess -/

section Record

variable (K : Ctx) (root : Digest) (s : St) (g : Coordinate × Digest)

theorem badR_record : BadR K root (s.record g) ↔ BadR K root s := Iff.rfl

theorem expo_record (ρ : ℝ) (flag : Bool) : expo K ρ flag (s.record g) = expo K ρ flag s := rfl

theorem pendA_record : pendA K (s.record g) = pendA K s := rfl

theorem nearMiss_record (f : FIn) : NearMiss K root (s.record g) f ↔ NearMiss K root s f := Iff.rfl

theorem survivesAt_record (f : FIn) : SurvivesAt K root (s.record g) f ↔ SurvivesAt K root s f := Iff.rfl

theorem nearContact_record : NearContact K root (s.record g) ↔ NearContact K root s := Iff.rfl

end Record

/-! ### Exposing a coordinate -/

section Expose

variable (K : Ctx) (root : Digest) (s : St) (c : Coordinate) (v : Digest)

theorem badW_expose' : BadW K (s.expose c v) ↔ BadW K s := Iff.rfl

theorem expo_expose (ρ : ℝ) (flag : Bool) : expo K ρ flag (s.expose c v) = expo K ρ flag s := rfl

theorem pendA_expose : pendA K (s.expose c v) = pendA K s := rfl

/-- Whether an exposure completes a FORS contact does not depend on the exposed value. -/
theorem nearContact_expose_iff (v' : Digest) :
    NearContact K root (s.expose c v) ↔ NearContact K root (s.expose c v') := by
  have hk : ∀ c', (s.expose c v).known c' = none ↔ (s.expose c v').known c' = none := by
    intro c'
    by_cases h : c' = c
    · subst h
      simp [DebtState.expose]
    · simp [DebtState.expose, h]
  have hn : ∀ I κ L, NearLeaf K root (s.expose c v) I κ L ↔ NearLeaf K root (s.expose c v') I κ L := by
    intro I κ L
    unfold NearLeaf
    simp only [ne_eq, hk]
    rfl
  unfold NearContact
  simp only [ne_eq, hk, hn]
  rfl

end Expose

/-! ### Storing a fresh answer -/

section Store

variable (K : Ctx) (root : Digest) {s : St} {x : HashInput} (u : HashOutput)

theorem fck_store (hx : s.cache x = none) (hi : K.initial x = none) (f : FIn) :
    FCk K (s.store x u) f ↔ FCk K s f ∨ (x = f.input K.p ∧ truncateHash u = K.F f.outC) := by
  unfold FCk
  simp only [K.fr_store u hx hi]
  constructor
  · rintro ⟨w, (hfr | ⟨hxe, rfl⟩), ht⟩
    · exact Or.inl ⟨w, hfr, ht⟩
    · exact Or.inr ⟨hxe.symm, ht⟩
  · rintro (⟨w, hfr, ht⟩ | ⟨rfl, ht⟩)
    · exact ⟨w, Or.inl hfr, ht⟩
    · exact ⟨u, Or.inr ⟨rfl, rfl⟩, ht⟩

theorem fck_store_of_not (hx : s.cache x = none) (hi : K.initial x = none) (hF : ∀ f : FIn, x ≠ f.input K.p)
    (f : FIn) : FCk K (s.store x u) f ↔ FCk K s f := by
  rw [fck_store K u hx hi]
  exact ⟨fun h => h.resolve_right fun h' => hF f h'.1, Or.inl⟩

theorem cachedDigest_store_of_not (hM : ¬ForsSigner.IsMsgInput x) (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    cachedDigest (s.store x u).cache parameter root message randomness =
      cachedDigest s.cache parameter root message randomness := by
  unfold cachedDigest
  congr 2
  funext call
  refine HiddenDebt.store_cache_ne s x _ ?_ u
  rintro rfl
  exact hM ⟨_, _, _, rfl⟩

theorem nearLeaf_store_of_not (hM : ¬ForsSigner.IsMsgInput x) (I : Index) (κ : FTree) (L : FLeaf) :
    NearLeaf K root (s.store x u) I κ L ↔ NearLeaf K root s I κ L := by
  unfold NearLeaf
  simp only [cachedDigest_store_of_not u hM]
  rfl

theorem known_store (c : Coordinate) : (s.store x u).known c = none ↔ s.known c = none := Iff.rfl

/-- A FORS leaf query is of no WOTS shape. -/
theorem sameLeaf_store_fleaf (hx : s.cache x = none) (hi : K.initial x = none) {f : FIn} (hxf : x = f.input K.p) :
    ∀ l, Retained K.p l → K.SameLeaf s (s.store x u) l := fun l _ =>
  K.sameLeaf_store u hx hi l (fun _ hA => Ctx.isA_ne_fleaf hA f hxf) (fun _ _ hB => Ctx.isB_ne_fleaf hB f hxf)
    (fun _ _ he => enc_ne_fleaf (he.symm.trans hxf))

/-- A digest block is of no WOTS shape. -/
theorem sameLeaf_store_msg (hx : s.cache x = none) (hi : K.initial x = none) (hM : ForsSigner.IsMsgInput x) :
    ∀ l, Retained K.p l → K.SameLeaf s (s.store x u) l := fun l _ =>
  K.sameLeaf_store u hx hi l
    (fun i hA => by obtain ⟨st, pay, -, rfl⟩ := hA; exact msg_ne_chain hM rfl)
    (fun i v hB => by obtain ⟨st, -, rfl⟩ := hB; exact msg_ne_chain hM rfl)
    (fun msg ctr he => msg_ne_enc hM he)

theorem not_msg_fleaf (f : FIn) : ¬ForsSigner.IsMsgInput (f.input K.p) := fun h => msg_ne_fleaf h rfl

theorem fleaf_not_msg {x : HashInput} (hM : ForsSigner.IsMsgInput x) (f : FIn) : x ≠ f.input K.p :=
  msg_ne_fleaf hM

end Store

end FORS.Security.SWRoute
