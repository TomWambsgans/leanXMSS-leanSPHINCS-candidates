import FORS.SWRoute.StepsBudget
import FORS.SWRoute.Steps

/-! **The SW route: helpers of the class steps.** The payments of a step by its input shape, the
means over a fresh answer, the two-valued means over a truncated answer, the step of a state in the
bad set, and the closing inequality of a step with a guess factor. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Payments by input shape -/

section Pay

variable (K : Ctx) (root : Digest)

/-- The ordinary query of a FORS leaf input. -/
abbrev flq (f : FIn) : CostSpec.Domain := .inl (.inr (.inl (f.input K.p)))

theorem flq_inj {f g : FIn} (h : flq K f = flq K g) : f = g := by
  simp only [flq, Sum.inl.injEq, Sum.inr.injEq] at h
  exact fleaf_inj h

theorem payF_flq (hdig : K.tg.digest = ForsSigner.IsMsgInput) (s : St) (f : FIn) :
    payF K root s (flq K f) = 0 := by
  show (if K.tg.digest (f.input K.p) then weightA K root s else 0) = 0
  rw [hdig, if_neg (not_msg_fleaf K f)]

theorem payK_flq (s : St) (f : FIn) (s' : St) : payK K root s (flq K f) s' = 0 := by
  unfold payK
  rw [if_neg]
  rintro ⟨h, -⟩
  exact h ⟨f, rfl⟩

theorem payC_flq (s : St) (f : FIn) :
    payC K root s (flq K f) = if SurvivesAt K root s f then weightA K root s else 0 := by
  unfold payC
  by_cases hs : SurvivesAt K root s f
  · rw [if_pos ⟨f, rfl, hs⟩, if_pos hs]
  · rw [if_neg hs, if_neg]
    rintro ⟨g, hg, hs'⟩
    exact hs (flq_inj K hg ▸ hs')

theorem armsAt_flq (s : St) (f : FIn) : ArmsAt K root s (flq K f) ↔ NearMiss K root s f := by
  unfold ArmsAt
  constructor
  · rintro ⟨g, hg, hn⟩
    exact flq_inj K hg ▸ hn
  · intro hn
    exact ⟨f, rfl, hn⟩

theorem payC_of_not (s : St) (input : CostSpec.Domain) (h : ¬IsFLQ K input) : payC K root s input = 0 := by
  unfold payC
  rw [if_neg]
  rintro ⟨f, hf, -⟩
  exact h ⟨f, hf⟩

theorem armsAt_of_not (s : St) (input : CostSpec.Domain) (h : ¬IsFLQ K input) : ¬ArmsAt K root s input := by
  rintro ⟨f, hf, -⟩
  exact h ⟨f, hf⟩

theorem nextFlag_of_not (flag : Bool) (s : St) (input : CostSpec.Domain) (h : ¬IsFLQ K input) :
    nextFlag K root flag s input = flag := by
  unfold nextFlag
  rw [decide_eq_false (armsAt_of_not K root s input h), Bool.or_false]

theorem payA_of_not (flag : Bool) (s : St) (input : CostSpec.Domain) (h : ¬IsFLQ K input) :
    payA K root flag s input = 0 := by
  unfold payA
  rw [if_neg (fun h' => armsAt_of_not K root s input h h'.2)]

theorem payA_flq_of_not (flag : Bool) (s : St) (f : FIn) (h : ¬NearMiss K root s f) :
    payA K root flag s (flq K f) = 0 := by
  unfold payA
  rw [if_neg (fun h' => h ((armsAt_flq K root s f).1 h'.2))]

theorem nextFlag_flq_of_not (flag : Bool) (s : St) (f : FIn) (h : ¬NearMiss K root s f) :
    nextFlag K root flag s (flq K f) = flag := by
  unfold nextFlag
  rw [decide_eq_false (fun h' => h ((armsAt_flq K root s f).1 h')), Bool.or_false]

theorem nextFlag_flq_of_nearMiss (flag : Bool) (s : St) (f : FIn) (h : NearMiss K root s f) :
    nextFlag K root flag s (flq K f) = true := by
  unfold nextFlag
  rw [decide_eq_true ((armsAt_flq K root s f).2 h), Bool.or_true]

theorem isFLQ_ordinary_iff (x : HashInput) : IsFLQ K (.inl (.inr (.inl x))) ↔ ∃ f : FIn, x = f.input K.p := by
  unfold IsFLQ
  constructor
  · rintro ⟨f, hf⟩
    simp only [Sum.inl.injEq, Sum.inr.injEq] at hf
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem payF_ordinary (s : St) (x : HashInput) :
    payF K root s (.inl (.inr (.inl x))) = if K.tg.digest x then weightA K root s else 0 := rfl

theorem payF_draw (s : St) (n : ℕ) : payF K root s (.inl (.inl n)) = 0 := rfl

theorem payF_reveal (s : St) (c : Coordinate) : payF K root s (.inl (.inr (.inr c))) = 0 := rfl

theorem payF_tick (s : St) (n : ℕ) : payF K root s (.inr n) = 0 := rfl

theorem not_isFLQ_draw (n : ℕ) : ¬IsFLQ K (.inl (.inl n)) := by
  rintro ⟨f, hf⟩
  cases hf

theorem not_isFLQ_reveal (c : Coordinate) : ¬IsFLQ K (.inl (.inr (.inr c))) := by
  rintro ⟨f, hf⟩
  cases hf

theorem not_isFLQ_tick (n : ℕ) : ¬IsFLQ K (.inr n) := by
  rintro ⟨f, hf⟩
  cases hf

end Pay

/-! ### Means -/

section Means

theorem tsum_readOutside_fresh (s0 : St) (x : HashInput) (hx : s0.cache x = none) (F : HashOutput × St → ℝ≥0∞) :
    ∑' r, Pr[= r | readOutside x s0] * F r = ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * F (u, s0.store x u) := by
  rw [readOutside_fresh x s0 hx, tsum_probOutput_map_mul]

/-- The same, for the cost step of an ordinary query (its range is the hash output). -/
theorem tsum_costStep_fresh {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (s s0 : St)
    (x : HashInput) (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s0) (hx : s0.cache x = none)
    (F : CostSpec.Range (.inl (.inr (.inl x))) × St → ℝ≥0∞) :
    ∑' r, Pr[= r | costStep model (.inl (.inr (.inl x))) s] * F r =
      ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * F (u, s0.store x u) := by
  rw [hcs]
  exact tsum_readOutside_fresh s0 x hx F

theorem meanD_le_of_pointwise (F : HashOutput → ℝ≥0∞) (G : Digest → ℝ≥0∞) (h : ∀ u, G (truncateHash u) ≤ F u) :
    meanD G ≤ ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * F u := by
  rw [← mean_trunc]
  exact ENNReal.tsum_le_tsum fun u => mul_le_mul_right (h u) _

theorem tsum_le_const_of_pointwise {γ : Type} (μ : ProbComp γ) (F : γ → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ a, F a ≤ c) :
    ∑' a, Pr[= a | μ] * F a ≤ c := by
  calc ∑' a, Pr[= a | μ] * F a ≤ ∑' a, Pr[= a | μ] * c := ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _
    _ = (∑' a, Pr[= a | μ]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := mul_le_mul_left tsum_probOutput_le_one _
    _ = c := one_mul c

theorem tsum_le_const_of_support {γ : Type} (μ : ProbComp γ) (F : γ → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ a ∈ support μ, F a ≤ c) : ∑' a, Pr[= a | μ] * F a ≤ c := by
  calc ∑' a, Pr[= a | μ] * F a ≤ ∑' a, Pr[= a | μ] * c := ENNReal.tsum_le_tsum fun a => by
        by_cases ha : a ∈ support μ
        · exact mul_le_mul_right (h a ha) _
        · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul, zero_mul]
    _ = (∑' a, Pr[= a | μ]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := mul_le_mul_left tsum_probOutput_le_one _
    _ = c := one_mul c

theorem const_le_tsum_of_support {γ : Type} (μ : ProbComp γ) (hμ : ∑' a, Pr[= a | μ] = 1) (F : γ → ℝ≥0∞)
    (c : ℝ≥0∞) (h : ∀ a ∈ support μ, c ≤ F a) : c ≤ ∑' a, Pr[= a | μ] * F a := by
  calc c = (∑' a, Pr[= a | μ]) * c := by rw [hμ, one_mul]
    _ = ∑' a, Pr[= a | μ] * c := ENNReal.tsum_mul_right.symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun a => by
        by_cases ha : a ∈ support μ
        · exact mul_le_mul_right (h a ha) _
        · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul, zero_mul]

/-- **The two-valued mean** over a uniform digest. -/
theorem meanD_two (v : Digest) (a b : ℝ≥0∞) :
    meanD (fun t => if t = v then a else b) + ν * b = b + ν * a := by
  have h1 : meanD (fun t => if t = v then b else 0) = ν * b :=
    meanD_ite_eq v (fun t => t = v) (fun t => Iff.rfl) b
  have h2 : meanD (fun t => if t = v then a else 0) = ν * a :=
    meanD_ite_eq v (fun t => t = v) (fun t => Iff.rfl) a
  have hfun : (fun t => (if t = v then a else b) + (if t = v then b else 0)) =
      (fun t => b + (if t = v then a else 0)) := by
    funext t
    by_cases ht : t = v
    · simp [ht, add_comm]
    · simp [ht]
  rw [← h1, ← meanD_add, hfun, meanD_add, meanD_const, h2]

/-- **Closing a step with a guess factor**: from `Bb + c + g X ≤ g M + g X` and `g w ≤ W0`,
`(Bb + c) w ≤ W0 M`. -/
theorem finish_guess {Bb c g w W0 M X : ℝ≥0∞} (hW0 : g * w ≤ W0) (hR : Bb + c + g * X ≤ g * M + g * X)
    (hfin : g * X ≠ ⊤) : (Bb + c) * w ≤ W0 * M := by
  have h1 : Bb + c ≤ g * M := (ENNReal.add_le_add_iff_right hfin).1 hR
  calc (Bb + c) * w ≤ g * M * w := mul_le_mul_left h1 _
    _ = M * (g * w) := by ring
    _ ≤ M * W0 := mul_le_mul_right hW0 _
    _ = W0 * M := mul_comm _ _

end Means

/-! ### A state in the bad set -/

section Bad

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

theorem payF_le_weight (s : St) (input : CostSpec.Domain) : payF K root s input ≤ weightA K root s := by
  rcases input with (n | (x | c)) | n
  · exact bot_le
  · rw [payF_ordinary]; split_ifs <;> simp
  · exact bot_le
  · exact bot_le

theorem payC_le_weight (s : St) (input : CostSpec.Domain) : payC K root s input ≤ weightA K root s := by
  unfold payC; split_ifs <;> simp

/-- **A step from a state in the bad set** satisfies the step bound trivially. -/
theorem stepBound_of_badP (input : CostSpec.Domain) (s : St) (flag : Bool) (probes remaining probes' : ℕ)
    (hb : BadP K root s) : StepBound K root model ρ β δ cU input s flag probes remaining probes' := by
  unfold StepBound
  have hw : weightA K root s = 0 := weightA_of_badP K root hb
  have hF : payF K root s input = 0 := le_antisymm ((payF_le_weight K root s input).trans hw.le) bot_le
  have hC : payC K root s input = 0 := le_antisymm ((payC_le_weight K root s input).trans hw.le) bot_le
  have hP : ∑' r, Pr[= r | costStep model input s] * (weightA K root r.2 * pendA K r.2) = 0 := by
    refine le_antisymm (le_trans (tsum_le_const_of_support _ _ 0 fun r hr => ?_) le_rfl) bot_le
    rw [weightA_of_badP K root (badP_mono (extends_costStep model input s r hr) hb), zero_mul]
  rw [hw, hF, hC, hP]
  simp

/-- **Assembling the step bound of a fresh answer** (the state after the step is `s0.store x u`
for a uniform answer `u`): an arming bound, the payments as `c` times the weight, a pointwise bound
of the pending credit after the step, and the main inequality of the class. -/
theorem stepBound_fresh (s s0 : St) (x : HashInput)
    (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s0) (hx0 : s0.cache x = none)
    (flag : Bool) (p r0 p' : ℕ) (Bb c Padd : ℝ≥0∞)
    (harm : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s ≤
      Bb * weightA K root s + ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x))))
    (hpays : ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) + ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x))) ≤
      c * weightA K root s)
    (hP : ∀ u, weightA K root (s0.store x u) * pendA K (s0.store x u) ≤ weightA K root s * pendA K s + Padd)
    (hmain : (Bb + c) * weightA K root s + Padd ≤
      ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (budgetE (expo K ρ (nextFlag K root flag s (.inl (.inr (.inl x)))) (s0.store x u)) p' r0 * weightA K root (s0.store x u))) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) p' := by
  unfold StepBound
  rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl x))) = 1 from rfl, Nat.add_sub_cancel, tsum_costStep_fresh model s s0 x hcs hx0, tsum_costStep_fresh model s s0 x hcs hx0,
    tsum_costStep_fresh model s s0 x hcs hx0]
  set E := ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
    (budgetE (expo K ρ (nextFlag K root flag s (.inl (.inr (.inl x)))) (s0.store x u)) p' r0 * weightA K root (s0.store x u))
  have hPsum : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (weightA K root (s0.store x u) * pendA K (s0.store x u)) ≤ weightA K root s * pendA K s + Padd :=
    tsum_le_const_of_pointwise _ _ _ hP
  calc budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
        (ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) + ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x)))) +
        ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (weightA K root (s0.store x u) * pendA K (s0.store x u))
      ≤ (Bb * weightA K root s + ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x)))) + c * weightA K root s +
          (weightA K root s * pendA K s + Padd) := add_le_add (add_le_add harm hpays) hPsum
    _ = ((Bb + c) * weightA K root s + Padd) +
          (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x)))) := by ring
    _ ≤ E + (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x)))) := by gcongr
    _ ≤ _ := add_le_add le_rfl le_self_add

/-- **Assembling the step bound of a fresh answer, with released pending credit** `Prel`. -/
theorem stepBound_fresh' (s s0 : St) (x : HashInput)
    (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s0) (hx0 : s0.cache x = none)
    (flag : Bool) (p r0 p' : ℕ) (Bb c Padd Prel : ℝ≥0∞) (hrel : Prel ≠ ⊤)
    (harm : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s ≤
      Bb * weightA K root s + ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x))))
    (hpays : ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) +
      ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x))) ≤ c * weightA K root s)
    (hP : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (weightA K root (s0.store x u) * pendA K (s0.store x u)) + Prel ≤ weightA K root s * pendA K s + Padd)
    (hmain : (Bb + c) * weightA K root s + Padd ≤
      ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (budgetE (expo K ρ (nextFlag K root flag s (.inl (.inr (.inl x)))) (s0.store x u)) p' r0 *
          weightA K root (s0.store x u)) + Prel) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) p' := by
  unfold StepBound
  rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl x))) = 1 from rfl,
    Nat.add_sub_cancel, tsum_costStep_fresh model s s0 x hcs hx0, tsum_costStep_fresh model s s0 x hcs hx0,
    tsum_costStep_fresh model s s0 x hcs hx0]
  set E := ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
    (budgetE (expo K ρ (nextFlag K root flag s (.inl (.inr (.inl x)))) (s0.store x u)) p' r0 *
      weightA K root (s0.store x u))
  set EP := ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
    (weightA K root (s0.store x u) * pendA K (s0.store x u))
  set A := ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x)))
  set pays := ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) +
    ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x)))
  have key : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s + pays + EP + Prel ≤
      E + (weightA K root s * pendA K s + A) + Prel :=
    calc budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s + pays + EP + Prel
        ≤ (Bb * weightA K root s + A) + c * weightA K root s + (weightA K root s * pendA K s + Padd) := by
          rw [add_assoc _ EP]
          exact add_le_add (add_le_add harm hpays) hP
      _ = ((Bb + c) * weightA K root s + Padd) + (weightA K root s * pendA K s + A) := by ring
      _ ≤ (E + Prel) + (weightA K root s * pendA K s + A) := by gcongr
      _ = E + (weightA K root s * pendA K s + A) + Prel := by ring
  refine le_trans ((ENNReal.add_le_add_iff_right hrel).1 key) ?_
  exact add_le_add le_rfl le_self_add

/-- **The closing inequality with an added pending credit**: from `Bb + g ν/2 ≤ g B`, `g w ≤ W0`,
`W0 ≤ w`... in the form needed by an input two steps below the word. -/
theorem finish_credit {Bb g w W0 B h : ℝ≥0∞} (hW0 : g * w ≤ W0) (hR : Bb + g * h ≤ g * B) (hhB : h ≤ B)
    : Bb * w + W0 * h ≤ W0 * B := by
  obtain ⟨d, rfl⟩ : ∃ d, W0 = g * w + d := ⟨W0 - g * w, (add_tsub_cancel_of_le hW0).symm⟩
  calc Bb * w + (g * w + d) * h = (Bb + g * h) * w + d * h := by ring
    _ ≤ g * B * w + d * B := add_le_add (mul_le_mul_left hR _) (mul_le_mul_right hhB _)
    _ = (g * w + d) * B := by ring

/-- **Lifting a guess-factor inequality** from `g0` to any `g ∈ [g0, 1]`. -/
theorem lift_factor {Bb X Y g0 g : ℝ≥0∞} (hR : Bb + g0 * X ≤ g0 * Y) (hXY : X ≤ Y) (hg : g0 ≤ g) :
    Bb + g * X ≤ g * Y := by
  obtain ⟨d, rfl⟩ : ∃ d, g = g0 + d := ⟨g - g0, (add_tsub_cancel_of_le hg).symm⟩
  calc Bb + (g0 + d) * X = (Bb + g0 * X) + d * X := by ring
    _ ≤ g0 * Y + d * Y := add_le_add hR (mul_le_mul_right hXY _)
    _ = (g0 + d) * Y := by ring

end Bad

end FORS.Security.SWRoute
