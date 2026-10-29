import FORS.SWRoute.Reveals

/-! **The release of the gated near potential.** The run invariant `JInv` of the SW route's near
potential: every known FORS secret was revealed, and every signed pair has all its FORS secrets
known. It holds at the start (no FORS secret is known), is kept by ordinary queries (no row outputs
a FORS secret), by fresh digest stores and by signing calls (a completed signature reveals every
secret of its pair, `sign_reveal_mem`). Under it, at an arming step (a FORS leaf query at a
near-missing cell, CORE-S's `ArmsAt`) the near potential's core is at least one (`release_coreG`):
the near pair is unsigned (its missing secret is unknown) and its realized near witness is at least
one (its other secrets are known, hence disclosed). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### A completed signature reveals its pair -/

section SignReveals

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (parameter : PublicParameter) (data : PublicData)
  (message : Message)

/-- The scan from a start: a completed signature caches its pair and reveals all its secrets. -/
theorem loop_reveal_mem (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data message ρ call) = none) :
    ∀ attempts budget (s : State) (ρ : Randomness),
      ∀ out ∈ support (interp tg initial model
          (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget s),
        ∀ sig, out.1.1 = some (some sig) →
          ∃ u, pcache parameter data message out.2 sig.randomness = some u ∧
            ∀ κ, Coordinate.fors (digestIndex (truncateMessageDigest u)) κ
              (digestLeaves (truncateMessageDigest u) κ) 0 ∈ out.1.2.1 := by
  intro attempts
  induction attempts with
  | zero =>
      intro budget s ρ out hout sig hsig
      change out ∈ support (interp tg initial model (pure none) budget s) at hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      cases hsig
  | succ attempts ih =>
      intro budget s ρ out hout sig hsig
      rw [signCostSourceLoop_succ, interp_ordinary] at hout
      split_ifs at hout with h1
      · rw [support_bind] at hout
        obtain ⟨res, _, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        simp only at hsig ho ⊢
        split_ifs at ho with hl
        · obtain ⟨u, hpc, hrev⟩ := finishCost_reveal_mem tg initial model parameter data message hparse ρ _ res.2 o ho
            sig hsig
          have hρ : sig.randomness = ρ := finish_randomness parameter data message ρ _
            (interp_result_mem tg initial model _ _ res.2 o ho _ hsig) sig rfl
          rw [hρ]
          exact ⟨u, hpc, hrev⟩
        · exact ih _ res.2 _ o ho sig hsig
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hsig
        cases hsig

/-- **A completed signature caches its pair and reveals every tree's secret at its leaf.** -/
theorem sign_reveal_mem (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data message ρ call) = none)
    (budget : ℕ) (s : State) (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data message) budget s))
    (sig : Signature) (hsig : out.1.1 = some (some sig)) :
    ∃ u, pcache parameter data message out.2 sig.randomness = some u ∧
      ∀ κ, Coordinate.fors (digestIndex (truncateMessageDigest u)) κ
        (digestLeaves (truncateMessageDigest u) κ) 0 ∈ out.1.2.1 := by
  unfold signCostSource at hout
  rw [interp_liftProb_bind, support_bind] at hout
  obtain ⟨ρ, _, hout⟩ := Set.mem_iUnion₂.1 hout
  exact loop_reveal_mem tg initial model parameter data message hparse _ budget s ρ out hout sig hsig

end SignReveals

/-! ### The invariant -/

section Inv

variable (parameter : PublicParameter) (data : PublicData)

/-- **The run invariant of the near potential's release**: known FORS secrets were revealed, and
signed pairs are cached with all their FORS secrets known. -/
def JInv (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) : Prop :=
  (∀ i κ l, s.known (Coordinate.fors i κ l 0) ≠ none → Coordinate.fors i κ l 0 ∈ R) ∧
  (∀ entry ∈ L, ∀ sig, entry.2 = some sig → ∃ u, pcache parameter data entry.1 s sig.randomness = some u ∧
    ∀ κ, s.known (Coordinate.fors (digestIndex (truncateMessageDigest u)) κ
      (digestLeaves (truncateMessageDigest u) κ) 0) ≠ none)

/-- The invariant grows with the state when no FORS secret becomes known. -/
theorem jInv_extends {s s' : State} (hext : Extends s s')
    (hk : ∀ i κ l, s'.known (Coordinate.fors i κ l 0) ≠ none → s.known (Coordinate.fors i κ l 0) ≠ none)
    {L : QueryLog SigningSpec} {R : List Coordinate} (hJ : JInv parameter data s L R) : JInv parameter data s' L R := by
  refine ⟨fun i κ l h => hJ.1 i κ l (hk i κ l h), fun entry he sig hsig => ?_⟩
  obtain ⟨u, hpc, hall⟩ := hJ.2 entry he sig hsig
  refine ⟨u, allSome_of_eq _ _ fun call => hext.1 _ _ (pcache_some parameter data entry.1 hpc call), fun κ => ?_⟩
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hall κ)
  rw [hext.2.1 _ _ hv]
  exact Option.some_ne_none _

theorem jInv_start (initial : HiddenOutside.Cache HashInput HashOutput) (known : HiddenReveal.Knowledge Coordinate)
    (hknown : ∀ i κ l, known (Coordinate.fors i κ l 0) = none) :
    JInv parameter data (DebtState.start initial known) [] [] :=
  ⟨fun i κ l h => absurd (hknown i κ l) h, fun _ he => by cases he⟩

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
include hout

/-- Ordinary queries keep the invariant. -/
theorem jInv_ordinary (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (x : HashInput)
    (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) (hJ : JInv parameter data s L R) :
    JInv parameter data r.2 L R := by
  refine jInv_extends parameter data (ordinaryStep_extends model x s r hr) (fun i κ l h => ?_) hJ
  rcases known_ordinary model x s r hr _ h with h' | ⟨a, ha⟩
  · exact h'
  · exact absurd ha.symm (hout a i κ l)

/-- Fresh digest stores keep the invariant. -/
theorem jInv_withPair (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (p : Pair)
    (u : DigestCall → HashOutput) (hfresh : ∀ call, s.cache (pblk parameter data p call) = none)
    (hJ : JInv parameter data s L R) : JInv parameter data (withPair parameter data s p u) L R := by
  have hext : Extends s (withPair parameter data s p u) := by
    refine ⟨fun y v hy => ?_, fun c v hc => ?_, fun g hg => ?_⟩
    · by_cases hyp : ∃ call, y = pblk parameter data p call
      · obtain ⟨call, rfl⟩ := hyp
        rw [hfresh call] at hy
        cases hy
      · push Not at hyp
        rw [withPair_other s p u y hyp]
        exact hy
    · rw [(withPair_known (parameter := parameter) (data := data) s p u).1]
      exact hc
    · rw [(withPair_known (parameter := parameter) (data := data) s p u).2]
      exact hg
  refine jInv_extends parameter data hext (fun i κ l h => ?_) hJ
  rwa [(withPair_known (parameter := parameter) (data := data) s p u).1] at h

/-- **Signing calls keep the invariant.** -/
theorem jInv_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) (budget : ℕ) (s : State)
    (L : QueryLog SigningSpec) (R : List Coordinate) (m : Message)
    (o1 : Run HashInput Coordinate (Option Signature) × State) (r : Option Signature)
    (ho1 : o1 ∈ support (interp tg initial model (signCostSource parameter data m) budget s)) (hr : o1.1.1 = some r)
    (hJ : JInv parameter data s L R) : JInv parameter data o1.2 (L ++ [⟨m, r⟩]) (R ++ o1.1.2.1) := by
  have hext := interp_extends tg initial model _ budget s o1 ho1
  refine ⟨fun i κ l h => ?_, fun entry he sig hsig => ?_⟩
  · rcases known_interp tg initial model _ budget s o1 ho1 _ h with h' | h' | ⟨a, ha⟩
    · exact List.mem_append_left _ (hJ.1 i κ l h')
    · exact List.mem_append_right _ h'
    · exact absurd ha.symm (hout a i κ l)
  · rcases List.mem_append.1 he with he | he
    · obtain ⟨u, hpc, hall⟩ := hJ.2 entry he sig hsig
      refine ⟨u, allSome_of_eq _ _ fun call => hext.1 _ _ (pcache_some parameter data entry.1 hpc call), fun κ => ?_⟩
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hall κ)
      rw [hext.2.1 _ _ hv]
      exact Option.some_ne_none _
    · rw [List.mem_singleton] at he
      subst he
      simp only at hsig
      subst hsig
      obtain ⟨u, hpc, hrev⟩ := sign_reveal_mem tg initial model parameter data m (fun ρ call => hparse (m, ρ) call)
        budget s o1 ho1 sig hr
      exact ⟨u, hpc, fun κ => interp_reveals_known tg initial model _ budget s o1 ho1 _ (hrev κ)⟩

end Inv

/-! ### The release -/

section Release

variable (K : PotentialA.Ctx) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- **The release.** At a FORS leaf query at a near-missing cell, the near pair is a cached landed
unsigned pair whose realized near witness is at least one, so the core of the near potential is at
least one. -/
theorem release_coreG (hw : wbar ≤ 1) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (n k : ℕ) (input : CostSpec.Domain)
    (hP : PInv K.p data s P) (hD : DInv R d) (hJ : JInv K.p data s L R) (harm : ArmsAt K data.root s input) :
    1 ≤ coreG K.p data witnessNear wbar b0 Fail s P Ms L d n k := by
  obtain ⟨f, -, ⟨message, randomness, digest, hcd, hland, hidx, hleaf, hother⟩, hmiss⟩ := harm
  set q : Pair := (message, randomness) with hq
  have hpb : HiddenBridge.cachedDigest s.cache K.p data.root message randomness =
      (pcache K.p data q.1 s q.2).map truncateMessageDigest := rfl
  rw [hpb] at hcd
  cases h0 : pcache K.p data q.1 s q.2 with
  | none =>
      rw [h0] at hcd
      cases hcd
  | some u =>
      rw [h0] at hcd
      have hdig : truncateMessageDigest u = digest := by simpa using hcd
      subst hdig
      have hlanded : LandedIn K.p data s q :=
        ⟨u firstCall, cached_of_pcache K.p data (p := q) h0 firstCall,
          by rwa [Concrete.digestIndex_truncate] at hland⟩
      have hqP := (hP.mem q).2 hlanded
      have hv : pview K.p data s q = Lifetime.localDigestView (truncateMessageDigest u) :=
        pview_of_pcache (q := q) h0
      -- the pair is unsigned: its secret at the missing tree is unknown
      have hun : Unsigned L q := by
        intro entry he sig hsig ⟨h1, h2⟩
        obtain ⟨u', hpc', hall⟩ := hJ.2 entry he sig hsig
        rw [h1, h2] at hpc'
        have huu : u' = u := Option.some_inj.1 (hpc'.symm.trans h0)
        subst huu
        apply hall f.κ
        rw [hidx, hleaf]
        exact hmiss
      -- the realized near witness is at least one
      have hnear : 1 ≤ witnessNear (pview K.p data s q) d := by
        rw [hv]
        have hsub : NearSub (Lifetime.localDigestView (truncateMessageDigest u)) f.κ d := by
          intro κ' hκ'
          have hk := hother κ' hκ'
          rw [← hidx] at hk
          obtain ⟨v, hvd, hv1, hv2⟩ := hD _ _ _ _ (hJ.1 _ _ _ hk)
          exact ⟨v, hvd, by rw [localDigestView_fst]; exact hv1, by rw [localDigestView_snd]; exact hv2⟩
        unfold witnessNear
        refine le_trans ?_ (Finset.single_le_sum (f := fun κ =>
          if NearSub (Lifetime.localDigestView (truncateMessageDigest u)) κ d then (1 : ℝ≥0∞) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ f.κ))
        rw [if_pos hsub]
      unfold coreG
      refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
      unfold candG
      rw [if_pos hun]
      split_ifs
      · exact le_rfl
      · exact hnear.trans (base_le_candValueG wbar witnessNear_props hw s Ms L d _ _ q)

end Release

end FORS.Security.SWRoute
