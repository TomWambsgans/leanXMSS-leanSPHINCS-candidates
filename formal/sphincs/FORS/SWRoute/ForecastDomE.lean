import FORS.SWRoute.ForecastDomD

/-! **The domination of the own-cell forecast, part E: the coin bounds and the one-index groups.**

* `grpAll_cov_vE`: with at most `patCapN(|B|)` selectable pairs matching the leaves on every
  nonempty `B`, the groups cover `S` with chance at most `coinV(|S \ covered|)`;
* `grpAll_count_le`: the groups add to the count at one index at most a Poisson count of rate
  `(number of selectable pairs at the index) / 2^128`, for good one-index functions. -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base FORS.Base.Domination FORS.Base.H0 FORS.Security.H0Avg ForsPrice Concrete GraphView
  ForsPotential FORS.LoopWalk

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Cover

variable (parameter : PublicParameter) (data : PublicData) (s : State) (excl : Pair → Prop)
  (I : Fin (2 ^ subtreeHeight)) (ℓ : FTree → FLeaf)

theorem sum_sum_ite_eq {X : Finset Message} (P : Pair → Prop) (h : Pair → ℝ≥0∞) :
    (∑ m ∈ X, ∑ ρ : Randomness, if P (m, ρ) then h (m, ρ) else 0) =
      ∑ g ∈ (X ×ˢ (Finset.univ : Finset Randomness)).filter P, h g := by
  rw [Finset.sum_filter, Finset.sum_product]

theorem covT_add (e X : Multiset View) : covT I ℓ (e + X) = covT I ℓ e ∪ covT I ℓ X := by
  ext κ'
  simp only [Finset.mem_union, mem_covT, Multiset.mem_add]
  constructor
  · rintro ⟨x, hx | hx, h1, h2⟩
    · exact Or.inl ⟨x, hx, h1, h2⟩
    · exact Or.inr ⟨x, hx, h1, h2⟩
  · rintro (⟨x, hx, h1, h2⟩ | ⟨x, hx, h1, h2⟩)
    · exact ⟨x, Or.inl hx, h1, h2⟩
    · exact ⟨x, Or.inr hx, h1, h2⟩

/-- The pairs among the selectable pairs of `Ms` at `I` that match `ℓ` on every tree of `B`. -/
noncomputable def matchSet (Ms : List Message) (B : Finset FTree) : Finset Pair :=
  (Ms.toFinset ×ˢ (Finset.univ : Finset Randomness)).filter fun g =>
    HitP parameter data s excl g ∧ (pview parameter data s g).1 = I ∧ ∀ κ' ∈ B, (pview parameter data s g).2 κ' = ℓ κ'

/-- **The coin bound of the groups covering leaves.** -/
theorem grpAll_cov_vE (hH : totalHeight = subtreeHeight) (b a cf q : ℕ) (Ms : List Message) (hnd : Ms.Nodup)
    (hcap : ∀ B : Finset FTree, B.Nonempty → (matchSet parameter data s excl I ℓ Ms B).card ≤ patCapN b a cf q B.card)
    (S : Finset FTree) :
    ∀ t e, (S \ covT I ℓ e).card = t → grpAll parameter data s excl Ms (covI I ℓ S) e ≤ vE b a cf q t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro e he
    rcases t with _ | t
    · rw [vE_zero]
      exact grpAll_le_one s excl (covI_le_one I ℓ S) Ms e
    · set U := S \ covT I ℓ e with hU
      have hUne : U.Nonempty := by rw [← Finset.card_pos, he]; omega
      obtain ⟨κ0, hκ0U⟩ := hUne
      have hκ0S : κ0 ∈ S := (Finset.mem_sdiff.1 hκ0U).1
      have hκ0e : κ0 ∉ covT I ℓ e := (Finset.mem_sdiff.1 hκ0U).2
      set ε := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hε
      set Z := (Ms.toFinset ×ˢ (Finset.univ : Finset Randomness)).filter
        (MatchP parameter data s excl I ℓ κ0) with hZ
      set Bg : Pair → Finset FTree := fun g => U.filter fun κ' => (pview parameter data s g).2 κ' = ℓ κ' with hBg
      have hstep := grpAll_cov_le parameter data s excl I ℓ hH S κ0 hκ0S Ms hnd e hκ0e
      rw [sum_sum_ite_eq (MatchP parameter data s excl I ℓ κ0)
        (fun g => ε * grpAll parameter data s excl Ms (covI I ℓ S) (e + {pview parameter data s g}))] at hstep
      -- each matching pair: the uncovered set shrinks by `Bg g`
      have hκ0B : ∀ g ∈ Z, κ0 ∈ Bg g := fun g hg =>
        Finset.mem_filter.2 ⟨hκ0U, (Finset.mem_filter.1 hg).2.2.2⟩
      have hsd : ∀ g ∈ Z, (S \ covT I ℓ (e + {pview parameter data s g})).card = t + 1 - (Bg g).card := by
        intro g hg
        have hI : (pview parameter data s g).1 = I := (Finset.mem_filter.1 hg).2.2.1
        have hset : S \ covT I ℓ (e + {pview parameter data s g}) = U \ Bg g := by
          ext κ'
          simp only [covT_add_single, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and, not_or, hBg, hU, hI]
          tauto
        rw [hset, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), he]
      have hIH : ∀ g ∈ Z, grpAll parameter data s excl Ms (covI I ℓ S) (e + {pview parameter data s g}) ≤
          vE b a cf q (t + 1 - (Bg g).card) := by
        intro g hg
        have hpos : 0 < (Bg g).card := Finset.card_pos.2 ⟨κ0, hκ0B g hg⟩
        exact ih _ (by omega) _ (hsd g hg)
      -- group the pairs by `Bg g`
      set T := (U.erase κ0).powerset.image (insert κ0) with hT
      have hmaps : ∀ g ∈ Z, Bg g ∈ T := by
        intro g hg
        refine Finset.mem_image.2 ⟨(Bg g).erase κ0, Finset.mem_powerset.2 ?_, Finset.insert_erase (hκ0B g hg)⟩
        exact Finset.erase_subset_erase κ0 (Finset.filter_subset _ _)
      have hcount : ∀ B ∈ T, (Z.filter fun g => Bg g = B).card ≤ patCapN b a cf q B.card := by
        intro B hB
        obtain ⟨B', _, rfl⟩ := Finset.mem_image.1 hB
        refine le_trans (Finset.card_le_card ?_) (hcap _ ⟨κ0, Finset.mem_insert_self _ _⟩)
        intro g hg
        obtain ⟨hgZ, hgB⟩ := Finset.mem_filter.1 hg
        obtain ⟨hgX, hM, hI, _⟩ := Finset.mem_filter.1 hgZ
        refine Finset.mem_filter.2 ⟨hgX, hM, hI, fun κ' hκ' => ?_⟩
        rw [← hgB] at hκ'
        exact (Finset.mem_filter.1 hκ').2
      have hinj : Set.InjOn (insert κ0) ((U.erase κ0).powerset : Set (Finset FTree)) := by
        intro A hA A' hA' hAA
        have hA0 : κ0 ∉ A := fun h => by
          have := Finset.mem_powerset.1 hA h; simp at this
        have hA0' : κ0 ∉ A' := fun h => by
          have := Finset.mem_powerset.1 hA' h; simp at this
        rw [← Finset.erase_insert hA0, ← Finset.erase_insert hA0', hAA]
      have hcardU : (U.erase κ0).card = t := by rw [Finset.card_erase_of_mem hκ0U, he]; rfl
      calc grpAll parameter data s excl Ms (covI I ℓ S) e
          ≤ ∑ g ∈ Z, ε * grpAll parameter data s excl Ms (covI I ℓ S) (e + {pview parameter data s g}) := hstep
        _ ≤ ∑ g ∈ Z, ε * vE b a cf q (t + 1 - (Bg g).card) :=
            Finset.sum_le_sum fun g hg => mul_le_mul_left' (hIH g hg) ε
        _ = ∑ B ∈ T, ∑ g ∈ Z.filter (fun g => Bg g = B), ε * vE b a cf q (t + 1 - (Bg g).card) :=
            (Finset.sum_fiberwise_of_maps_to hmaps _).symm
        _ = ∑ B ∈ T, ((Z.filter fun g => Bg g = B).card : ℝ≥0∞) * (ε * vE b a cf q (t + 1 - B.card)) := by
            refine Finset.sum_congr rfl fun B _ => ?_
            rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const,
              nsmul_eq_mul]
        _ ≤ ∑ B ∈ T, (patCapN b a cf q B.card : ℝ≥0∞) * (ε * vE b a cf q (t + 1 - B.card)) :=
            Finset.sum_le_sum fun B hB => mul_le_mul_right' (by exact_mod_cast hcount B hB) _
        _ = ∑ B' ∈ (U.erase κ0).powerset, (patCapN b a cf q (B'.card + 1) : ℝ≥0∞) *
              (ε * vE b a cf q (t - B'.card)) := by
            rw [Finset.sum_image hinj]
            refine Finset.sum_congr rfl fun B' hB' => ?_
            have hB'0 : κ0 ∉ B' := fun h => by
              have := Finset.mem_powerset.1 hB' h; simp at this
            rw [Finset.card_insert_of_notMem hB'0, show t + 1 - (B'.card + 1) = t - B'.card by omega]
        _ = ∑ j ∈ Finset.range (t + 1), (t.choose j : ℝ≥0∞) *
              ((patCapN b a cf q (j + 1) : ℝ≥0∞) * (ε * vE b a cf q (t - j))) := by
            rw [Finset.sum_powerset_apply_card (fun j => (patCapN b a cf q (j + 1) : ℝ≥0∞) *
              (ε * vE b a cf q (t - j))), hcardU]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [nsmul_eq_mul]
        _ = vE b a cf q (t + 1) := by
            rw [vE_succ]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring

/-! ### The groups at one index -/

/-- The selectable pairs of `Ms` at index `I`. -/
noncomputable def hitsAt (Ms : List Message) : Finset Pair :=
  (Ms.toFinset ×ˢ (Finset.univ : Finset Randomness)).filter fun g =>
    HitP parameter data s excl g ∧ (pview parameter data s g).1 = I

theorem countAt_add (e X : Multiset View) (l : Fin (2 ^ subtreeHeight)) :
    countAt (e + X) l = countAt e l + countAt X l := by
  unfold countAt; rw [Multiset.filter_add, Multiset.card_add]

theorem countAt_single (x : View) (l : Fin (2 ^ subtreeHeight)) :
    countAt {x} l = if x.1 = l then 1 else 0 := by
  unfold countAt; rw [Multiset.filter_singleton]; split_ifs <;> simp

theorem countAt_zero' (l : Fin (2 ^ subtreeHeight)) : countAt (0 : Multiset View) l = 0 := by
  simp [countAt]

theorem card_randomnessE :(Fintype.card Randomness : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
  rw [card_randomness, Nat.cast_pow, Nat.cast_ofNat]

/-- **The groups at one index**: a Poisson count of rate `|hits at I| / 2^128`. -/
theorem grpAll_count_le (hH : totalHeight = subtreeHeight) {G : ℕ → ℝ≥0∞} (hG : Good1 G) :
    ∀ (Ms : List Message), Ms.Nodup → ∀ e,
      grpAll parameter data s excl Ms (fun e => G (countAt e I)) e ≤
        pois1 (((hitsAt parameter data s excl I Ms).card : ℝ≥0) / 2 ^ 128) G (countAt e I)
  | [], _, e => by
      simp only [grpAll]
      have : hitsAt parameter data s excl I [] = ∅ := by simp [hitsAt]
      rw [this, Finset.card_empty, Nat.cast_zero, zero_div]
      exact le_pois1 hG.mono 0 _
  | m :: Ms, hnd, e => by
      rw [List.nodup_cons] at hnd
      set rM : ℝ≥0 := ((hitsAt parameter data s excl I Ms).card : ℝ≥0) / 2 ^ 128 with hrM
      set P := pois1 rM G with hP
      have hPg : Good1 P := hG.pois1 rM
      set A := (Finset.univ : Finset Randomness).filter fun ρ =>
        HitP parameter data s excl (m, ρ) ∧ (pview parameter data s (m, ρ)).1 = I with hA
      set pa : ℝ≥0 := (A.card : ℝ≥0) / 2 ^ 128 with hpa
      have hAle : A.card ≤ 2 ^ 128 := by
        rw [← card_randomness]; exact Finset.card_le_univ _
      have hpa1 : pa ≤ 1 := by
        rw [hpa, div_le_one (by positivity)]; exact_mod_cast hAle
      -- the count after one randomizer
      have hcnt : ∀ ρ, countAt (e + gx parameter data s excl m ρ) I =
          countAt e I + if ρ ∈ A then 1 else 0 := by
        intro ρ
        rw [countAt_add, gx_eq]
        have hx : countAt (if HitP parameter data s excl (m, ρ) then {pview parameter data s (m, ρ)} else 0) I =
            if ρ ∈ A then 1 else 0 := by
          by_cases h1 : HitP parameter data s excl (m, ρ)
          · rw [if_pos h1, countAt_single]
            by_cases h2 : (pview parameter data s (m, ρ)).1 = I
            · rw [if_pos h2, if_pos (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩)]
            · rw [if_neg h2, if_neg (fun h => h2 (Finset.mem_filter.1 h).2.2)]
          · rw [if_neg h1, if_neg (fun h => h1 (Finset.mem_filter.1 h).2.1), countAt_zero']
        rw [hx]
      have hsum : ∑ ρ, P (countAt e I + if ρ ∈ A then 1 else 0) =
          (A.card : ℝ≥0∞) * P (countAt e I + 1) + ((2 ^ 128 - A.card : ℕ) : ℝ≥0∞) * P (countAt e I) := by
        have hs1 : ∑ ρ ∈ Finset.univ.filter (fun ρ => ρ ∈ A), P (countAt e I + if ρ ∈ A then 1 else 0) =
            ∑ ρ ∈ Finset.univ.filter (fun ρ => ρ ∈ A), P (countAt e I + 1) :=
          Finset.sum_congr rfl fun ρ hρ => by rw [if_pos (Finset.mem_filter.1 hρ).2]
        have hs2 : ∑ ρ ∈ Finset.univ.filter (fun ρ => ρ ∉ A), P (countAt e I + if ρ ∈ A then 1 else 0) =
            ∑ ρ ∈ Finset.univ.filter (fun ρ => ρ ∉ A), P (countAt e I) :=
          Finset.sum_congr rfl fun ρ hρ => by rw [if_neg (Finset.mem_filter.1 hρ).2, add_zero]
        have h1 : (Finset.univ.filter fun ρ => ρ ∈ A) = A := by
          ext ρ; rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
        have h2 : (Finset.univ.filter fun ρ => ρ ∉ A).card = 2 ^ 128 - A.card := by
          rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), h1, Finset.card_univ,
            card_randomness]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ρ => ρ ∈ A), hs1, hs2,
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, h1, h2]
      have hpaE : ((pa : ℝ≥0) : ℝ≥0∞) = (A.card : ℝ≥0∞) * (Fintype.card Randomness : ℝ≥0∞)⁻¹ := by
        rw [hpa, ENNReal.coe_div (by positivity), ENNReal.coe_natCast, ENNReal.coe_pow, ENNReal.coe_ofNat,
          card_randomnessE, div_eq_mul_inv]
      have h1pa : 1 - ((pa : ℝ≥0) : ℝ≥0∞) =
          ((2 ^ 128 - A.card : ℕ) : ℝ≥0∞) * (Fintype.card Randomness : ℝ≥0∞)⁻¹ := by
        rw [hpaE, ENNReal.natCast_sub, card_randomnessE,
          ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)),
          Nat.cast_pow, Nat.cast_ofNat, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (pow_ne_top ofNat_ne_top)]
      calc grpAll parameter data s excl (m :: Ms) (fun e => G (countAt e I)) e
          = (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
              ∑ ρ, grpAll parameter data s excl Ms (fun e => G (countAt e I)) (e + gx parameter data s excl m ρ) := by
            rw [grpAll, grpM_eq parameter data hH, freshAvg_univ_eq]
        _ ≤ (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ ρ, P (countAt e I + if ρ ∈ A then 1 else 0) := by
            refine mul_le_mul_left' (Finset.sum_le_sum fun ρ _ => ?_) _
            rw [← hcnt]
            exact grpAll_count_le hH hG Ms hnd.2 _
        _ = (1 - ((pa : ℝ≥0) : ℝ≥0∞)) * P (countAt e I) + ((pa : ℝ≥0) : ℝ≥0∞) * P (countAt e I + 1) := by
            rw [hsum, h1pa, hpaE]; ring
        _ ≤ pois1 pa P (countAt e I) := bern_le_pois1 hPg pa hpa1 _
        _ = pois1 (pa + rM) G (countAt e I) := pois1_pois1 pa rM G _
        _ = _ := by
            have hdisj : Disjoint (A.image fun ρ => (m, ρ)) (hitsAt parameter data s excl I Ms) := by
              rw [Finset.disjoint_left]
              intro g hg hg'
              obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.1 hg
              have := (Finset.mem_product.1 (Finset.mem_filter.1 hg').1).1
              exact hnd.1 (List.mem_toFinset.1 this)
            have hun : hitsAt parameter data s excl I (m :: Ms) =
                (A.image fun ρ => (m, ρ)) ∪ hitsAt parameter data s excl I Ms := by
              ext g
              constructor
              · intro hg
                obtain ⟨hgX, hH1, hI1⟩ := Finset.mem_filter.1 hg
                obtain ⟨hm, -⟩ := Finset.mem_product.1 hgX
                rcases List.mem_cons.1 (List.mem_toFinset.1 hm) with h1 | h1
                · have hg' : g = (m, g.2) := Prod.ext h1 rfl
                  refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨g.2, Finset.mem_filter.2
                    ⟨Finset.mem_univ _, ?_⟩, hg'.symm⟩)
                  rw [← hg']; exact ⟨hH1, hI1⟩
                · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_product.2
                    ⟨List.mem_toFinset.2 h1, Finset.mem_univ _⟩, hH1, hI1⟩)
              · intro hg
                rcases Finset.mem_union.1 hg with h | h
                · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 h
                  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hρ
                  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨List.mem_toFinset.2 List.mem_cons_self,
                    Finset.mem_univ _⟩, h1, h2⟩
                · obtain ⟨hgX, h1, h2⟩ := Finset.mem_filter.1 h
                  obtain ⟨hm, -⟩ := Finset.mem_product.1 hgX
                  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨List.mem_toFinset.2
                    (List.mem_cons_of_mem _ (List.mem_toFinset.1 hm)), Finset.mem_univ _⟩, h1, h2⟩
            have hrate : pa + rM = ((hitsAt parameter data s excl I (m :: Ms)).card : ℝ≥0) / 2 ^ 128 := by
              rw [hun, Finset.card_union_of_disjoint hdisj,
                Finset.card_image_of_injective _ (fun ρ ρ' h => (Prod.mk.inj h).2), hpa, hrM, Nat.cast_add,
                add_div]
            rw [hrate]

end Cover

end FORS.Security.SWRoute
