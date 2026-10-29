import FORS.Reduction.SeedElimination

/-! **At most `signatureLimit` signing queries.** The SW route's potentials need an adversary program
that asks at most `N = signatureLimit` signatures on every path (`SignBound`). Any adversary can be
cut to one: the truncated adversary `truncSign adversary n` forwards its first `n` signing queries and
answers every later one itself with `none`, without asking the oracle. It asks at most `n` signatures,
it never repeats a request when the original does not, and it commutes with internalizing long hash
inputs.

On a path with at most `signatureLimit` signing queries the two adversaries run the same game. On a
path with more, the original loses, since its log then has more than `signatureLimit` entries and
`SigningTranscript.Valid` fails. So the truncated adversary wins the seed-free, budget-capped game at
least as often (`seedFree_internalize_le_trunc`). The budget is enforced by the interpreter (`cap`
aborts, and an aborted run does not win), so no cost comparison is needed.

The corollary `forgeAdvantage_le_seedFree_signBound` is `Det.forgeAdvantage_le_seedFree` for the
truncated memoizing adversary, which never repeats a request and asks at most `signatureLimit`
signatures (`truncMemo_noRepeat`, `truncMemo_signBound`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Internalize Short Memo ForsPotential GraphView Reduce DetValue

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Bounded signing queries -/

/-- The program asks at most `n` further signatures. -/
def SignBound {α : Type} (M : OracleComp (OracleWorld + SigningSpec) α) : ℕ → Prop :=
  OracleComp.construct (C := fun _ => ℕ → Prop) (fun _ _ => True)
    (fun input _ rec n => match input with
      | .inl _ => ∀ v, rec v n
      | .inr _ => 0 < n ∧ ∀ r, rec r (n - 1)) M

theorem signBound_sign {α : Type} (m : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α) (n : ℕ) :
    SignBound (liftM ((OracleWorld + SigningSpec).query (.inr m)) >>= next) n ↔
      0 < n ∧ ∀ r, SignBound (next r) (n - 1) :=
  Iff.rfl

theorem signBound_pure {α : Type} (a : α) (n : ℕ) :
    SignBound (pure a : OracleComp (OracleWorld + SigningSpec) α) n :=
  trivial

theorem signBound_world {α : Type} (t : OracleWorld.Domain)
    (next : OracleWorld.Range t → OracleComp (OracleWorld + SigningSpec) α) (n : ℕ) :
    SignBound (liftM ((OracleWorld + SigningSpec).query (.inl t)) >>= next) n ↔
      ∀ v, SignBound (next v) n :=
  Iff.rfl

/-- An adversary that asks at most `n` signatures, for every public key. -/
def _root_.FORS.Security.Adversary.SignBound (adversary : Adversary) (n : ℕ) : Prop :=
  ∀ pk, FORS.Security.SWRoute.SignBound (adversary.main pk) n

theorem signBound_mono {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (n n' : ℕ), n ≤ n' → SignBound M n → SignBound M n' := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro n n' _ _; exact trivial
  | query_bind t next ih =>
      intro n n' hn h
      rcases t with t | m
      · exact fun v => ih v n n' hn (h v)
      · exact ⟨lt_of_lt_of_le h.1 hn, fun r => ih r (n - 1) (n' - 1) (by omega) (h.2 r)⟩

theorem signBound_map {α β : Type} (g : α → β) :
    ∀ (M : OracleComp AdvSpec α) (n : ℕ), SignBound M n → SignBound (g <$> M) n := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro n _; exact trivial
  | query_bind t next ih =>
      intro n h
      rw [map_bind]
      rcases t with t | m
      · exact fun v => ih v n (h v)
      · exact ⟨h.1, fun r => ih r _ (h.2 r)⟩

/-! ### Internalizing keeps the bound -/

theorem signBound_liftWorld_bind {α β : Type} :
    ∀ (x : OracleComp OracleWorld α) (k : α → OracleComp AdvSpec β) (n : ℕ),
      (∀ a, SignBound (k a) n) → SignBound (liftWorld x >>= k) n := by
  intro x
  induction x using OracleComp.inductionOn with
  | pure a =>
      intro k n h
      simp only [liftWorld, simulateQ_pure, pure_bind]
      exact h a
  | query_bind t next ih =>
      intro k n h
      simp only [liftWorld, simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact fun v => ih v k n h

theorem signBound_map_liftWorld_bind {α β γ : Type} (f : α → β) (x : OracleComp OracleWorld α)
    (k : β → OracleComp AdvSpec γ) (n : ℕ) (h : ∀ a, SignBound (k (f a)) n) :
    SignBound ((f <$> liftWorld x) >>= k) n := by
  rw [bind_map_left]
  exact signBound_liftWorld_bind x _ n h

theorem signBound_internalize {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (n : ℕ) (cache : QueryCache HashSpec),
      SignBound M n → SignBound ((simulateQ internalImpl M).run cache) n := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a =>
      intro n cache _
      simp only [simulateQ_pure, StateT.run_pure]
      exact trivial
  | query_bind t next ih =>
      intro n cache h
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rcases t with (draw | input) | m
      · change SignBound ((forward (.inl (.inl draw))).run cache >>= _) n
        simp only [forward, StateT.run, bind_map_left]
        exact fun v => ih v n cache (h v)
      · change SignBound ((if IsShort input then forward (.inl (.inr input)) else privateRead input).run cache
          >>= _) n
        split_ifs with hs
        · simp only [forward, StateT.run, bind_map_left]
          exact fun v => ih v n cache (h v)
        · simp only [privateRead, StateT.run]
          cases hc : cache input with
          | some answer =>
              exact ih answer n cache (h answer)
          | none =>
              exact signBound_map_liftWorld_bind _ _ _ n fun v => ih v n _ (h v)
      · change SignBound ((forward (.inr m)).run cache >>= _) n
        simp only [forward, StateT.run, bind_map_left]
        exact ⟨h.1, fun r => ih r _ cache (h.2 r)⟩

theorem signBound_internalize_adversary (adversary : Adversary) (n : ℕ) (h : adversary.SignBound n) :
    (internalize adversary).SignBound n := by
  intro pk
  exact signBound_map _ _ n (signBound_internalize _ n ∅ (h pk))

/-! ### The truncation -/

/-- Forward the first `n` signing queries; answer every later one with `none`, without asking. -/
noncomputable def truncImpl : QueryImpl AdvSpec (StateT ℕ (OracleComp AdvSpec))
  | .inl t => fun n =>
      (fun answer => (answer, n)) <$> (liftM (AdvSpec.query (.inl t)) : OracleComp AdvSpec _)
  | .inr m => fun n =>
      match n with
      | 0 => pure ((none : Option Signature), 0)
      | k + 1 => (fun signature => (signature, k)) <$>
          (liftM (AdvSpec.query (.inr m)) : OracleComp AdvSpec _)

/-- The program cut after `n` signing queries. -/
noncomputable def truncSignProg {α : Type} (M : OracleComp AdvSpec α) (n : ℕ) : OracleComp AdvSpec α :=
  (simulateQ truncImpl M).run' n

/-- **The truncated adversary**: it forwards its first `n` signing queries and answers every later
one with `none` itself. -/
noncomputable def truncSign (adversary : Adversary) (n : ℕ) : Adversary :=
  ⟨fun publicKey => truncSignProg (adversary.main publicKey) n⟩

theorem truncImpl_world (t : OracleWorld.Domain) (n : ℕ) :
    (truncImpl (.inl t)).run n =
      (fun answer => (answer, n)) <$> (liftM (AdvSpec.query (.inl t)) : OracleComp AdvSpec _) := rfl

theorem truncImpl_sign_zero (m : Message) :
    (truncImpl (.inr m)).run 0 = pure ((none : Option Signature), 0) := rfl

theorem truncImpl_sign_succ (m : Message) (k : ℕ) :
    (truncImpl (.inr m)).run (k + 1) =
      (fun signature => (signature, k)) <$> (liftM (AdvSpec.query (.inr m)) : OracleComp AdvSpec _) := rfl

theorem trunc_run_query_bind {β : Type} (t : AdvSpec.Domain) (k : AdvSpec.Range t → OracleComp AdvSpec β)
    (n : ℕ) :
    (simulateQ truncImpl ((liftM (AdvSpec.query t) : OracleComp AdvSpec _) >>= k)).run n =
      (truncImpl t).run n >>= fun p => (simulateQ truncImpl (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem signBound_trunc {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (n : ℕ), SignBound ((simulateQ truncImpl M).run n) n := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a =>
      intro n
      simp only [simulateQ_pure, StateT.run_pure]
      exact trivial
  | query_bind t next ih =>
      intro n
      rw [trunc_run_query_bind]
      rcases t with t | m
      · rw [truncImpl_world, bind_map_left]
        exact fun v => ih v n
      · cases n with
        | zero =>
            rw [truncImpl_sign_zero, pure_bind]
            exact ih none 0
        | succ k =>
            rw [truncImpl_sign_succ, bind_map_left]
            exact ⟨Nat.succ_pos k, fun r => ih r k⟩

/-- **The truncated adversary asks at most `n` signatures.** -/
theorem truncSign_signBound (adversary : Adversary) (n : ℕ) : (truncSign adversary n).SignBound n := by
  intro pk
  change SignBound ((simulateQ truncImpl (adversary.main pk)).run' n) n
  rw [StateT.run'_eq]
  exact signBound_map _ _ n (signBound_trunc _ n)

theorem noRepeat_mono {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (S S' : List Message), (∀ m ∈ S, m ∈ S') → NoRepeat M S' →
      NoRepeat M S := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro S S' _ _; exact trivial
  | query_bind t next ih =>
      intro S S' hsub h
      rcases t with t | m
      · exact fun v => ih v S S' hsub (h v)
      · refine ⟨fun hm => h.1 (hsub m hm), fun r => ih r (S ++ [m]) (S' ++ [m]) ?_ (h.2 r)⟩
        intro m' hm'
        rcases List.mem_append.1 hm' with hm' | hm'
        · exact List.mem_append_left _ (hsub m' hm')
        · exact List.mem_append_right _ hm'

theorem noRepeat_trunc {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (n : ℕ) (S : List Message), NoRepeat M S →
      NoRepeat ((simulateQ truncImpl M).run n) S := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a =>
      intro n S _
      simp only [simulateQ_pure, StateT.run_pure]
      exact trivial
  | query_bind t next ih =>
      intro n S h
      rw [trunc_run_query_bind]
      rcases t with t | m
      · rw [truncImpl_world, bind_map_left]
        exact fun v => ih v n S (h v)
      · cases n with
        | zero =>
            rw [truncImpl_sign_zero, pure_bind]
            exact ih none 0 S
              (noRepeat_mono _ S (S ++ [m]) (fun m' hm' => List.mem_append_left _ hm') (h.2 none))
        | succ k =>
            rw [truncImpl_sign_succ, bind_map_left]
            exact ⟨h.1, fun r => ih r k _ (h.2 r)⟩

/-- **The truncated adversary never repeats a request** when the original does not. -/
theorem truncSign_noRepeat (adversary : Adversary) (n : ℕ) (h : adversary.NoRepeat) :
    (truncSign adversary n).NoRepeat := by
  intro pk
  change NoRepeat ((simulateQ truncImpl (adversary.main pk)).run' n) []
  rw [StateT.run'_eq]
  exact noRepeat_map _ _ [] (noRepeat_trunc _ n [] (h pk))

/-! ### Truncating commutes with internalizing -/

theorem trunc_liftWorld {α : Type} (x : OracleComp OracleWorld α) (n : ℕ) :
    (simulateQ truncImpl (liftWorld x)).run n = (fun a => (a, n)) <$> liftWorld x := by
  induction x using OracleComp.inductionOn with
  | pure a => simp [liftWorld]
  | query_bind t next ih =>
      have hlift : liftWorld ((liftM (OracleWorld.query t) : OracleComp OracleWorld _) >>= next) =
          (liftM (AdvSpec.query (.inl t)) : OracleComp AdvSpec _) >>= fun a => liftWorld (next a) := by
        rw [liftWorld, simulateQ_bind, simulateQ_spec_query]
        rfl
      rw [hlift, trunc_run_query_bind, truncImpl_world, bind_map_left, map_bind]
      exact bind_congr fun v => ih v

theorem trunc_privateRead (bytes : HashInput) (cache : QueryCache HashSpec) (n : ℕ) :
    (simulateQ truncImpl ((privateRead bytes).run cache)).run n =
      (fun p => (p, n)) <$> (privateRead bytes).run cache := by
  change (simulateQ truncImpl (privateRead bytes cache)).run n = _ <$> privateRead bytes cache
  unfold privateRead
  split
  · simp
  · rw [simulateQ_map, StateT.run_map, trunc_liftWorld, Functor.map_map, Functor.map_map]

theorem internal_trunc_comm {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (n : ℕ) (cache : QueryCache HashSpec),
      (simulateQ internalImpl ((simulateQ truncImpl M).run n)).run cache =
        (fun p => ((p.1.1, p.2), p.1.2)) <$>
          (simulateQ truncImpl ((simulateQ internalImpl M).run cache)).run n := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro n cache; simp
  | query_bind t next ih =>
      intro n cache
      rw [trunc_run_query_bind, internal_run_query_bind]
      rcases t with (draw | bytes) | m
      · rw [truncImpl_world, bind_map_left, internal_run_query_bind,
          internal_forward_run _ rfl, bind_map_left, bind_map_left, simulateQ_bind, StateT.run_bind,
          simulateQ_spec_query, truncImpl_world, bind_map_left, map_bind]
        exact bind_congr fun v => ih v n cache
      · by_cases hshort : IsShort bytes
        · have hint : internalImpl (.inl (.inr bytes)) = forward (.inl (.inr bytes)) := by
            simp only [internalImpl, hshort, ↓reduceIte]
          rw [truncImpl_world, bind_map_left, internal_run_query_bind,
            internal_forward_run _ hint, bind_map_left, bind_map_left, simulateQ_bind, StateT.run_bind,
            simulateQ_spec_query, truncImpl_world, bind_map_left, map_bind]
          exact bind_congr fun v => ih v n cache
        · have hint : internalImpl (.inl (.inr bytes)) = privateRead bytes := by
            simp only [internalImpl, hshort, ↓reduceIte]
          rw [truncImpl_world, bind_map_left, internal_run_query_bind, hint, simulateQ_bind,
            StateT.run_bind, trunc_privateRead, bind_map_left, map_bind]
          exact bind_congr fun p => ih p.1 n p.2
      · rw [internal_forward_run _ rfl, bind_map_left]
        cases n with
        | zero =>
            rw [truncImpl_sign_zero, pure_bind, ih none 0 cache, trunc_run_query_bind,
              truncImpl_sign_zero, pure_bind]
        | succ k =>
            rw [truncImpl_sign_succ, bind_map_left, internal_run_query_bind,
              internal_forward_run _ rfl, bind_map_left, trunc_run_query_bind,
              truncImpl_sign_succ, bind_map_left, map_bind]
            exact bind_congr fun v => ih v k cache

theorem internalize_truncSign_main (adversary : Adversary) (n : ℕ) (pk : PublicKey) :
    (internalize (truncSign adversary n)).main pk = (truncSign (internalize adversary) n).main pk := by
  change (simulateQ internalImpl ((simulateQ truncImpl (adversary.main pk)).run' n)).run' ∅ =
    (simulateQ truncImpl ((simulateQ internalImpl (adversary.main pk)).run' ∅)).run' n
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, internal_trunc_comm, Functor.map_map]

/-- **Internalizing the truncated adversary gives the truncated internalized adversary.** -/
theorem internalize_truncSign (adversary : Adversary) (n : ℕ) :
    internalize (truncSign adversary n) = truncSign (internalize adversary) n := by
  have hext : ∀ A B : Adversary, (∀ pk, A.main pk = B.main pk) → A = B := by
    rintro ⟨a⟩ ⟨b⟩ h
    congr 1
    funext pk
    exact h pk
  exact hext _ _ (internalize_truncSign_main adversary n)

/-! ### The truncated adversary wins at least as often -/

section Win

variable (g : HashInput → HashOutput) (c : HiddenGraph.Table)

/-- A log with more than `signatureLimit` entries loses, whatever comes after. -/
theorem advRand_invalid (parameter : PublicParameter) (data : PublicData)
    (M : OracleComp AdvSpec Forgery) (L : QueryLog SigningSpec) (hL : signatureLimit < L.length) (b : ℕ) :
    val g c (· = true) (advRand parameter data M L) b = 0 := by
  refine le_antisymm ?_ bot_le
  unfold advRand
  refine val_bind_le_of g c _ _ _ 0 b fun x _ b' _ => ?_
  unfold finishBool
  refine val_bind_le_of g c _ _ _ 0 b' fun v _ b'' _ => ?_
  rw [val_pure, if_neg]
  simp only [Bool.and_eq_true, decide_eq_true_eq, SigningTranscript.Valid, List.length_append]
  rintro ⟨⟨hvalid, -⟩, -⟩
  omega

/-- One adversary program against its truncation, with at least `signatureLimit - |L|` signing
queries left. -/
theorem advRand_le_trunc (parameter : PublicParameter) (data : PublicData) :
    ∀ (M : OracleComp AdvSpec Forgery) (n : ℕ) (L : QueryLog SigningSpec), signatureLimit ≤ L.length + n →
      ∀ b, val g c (· = true) (advRand parameter data M L) b ≤
        val g c (· = true) (advRand parameter data (Prod.fst <$> (simulateQ truncImpl M).run n) L) b := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro n L _ b
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact le_rfl
  | query_bind t next ih =>
      intro n L hn b
      rw [trunc_run_query_bind]
      rcases t with t | m
      · rw [truncImpl_world, bind_map_left, map_bind, advRand_world, advRand_world]
        exact val_bind_mono g c _ _ _ _ (fun v _ b' => ih v n L hn b') b
      · cases n with
        | zero =>
            rw [advRand_sign]
            refine le_trans (val_bind_le_of g c _ _ _ 0 b fun r _ b' _ =>
              le_of_eq (advRand_invalid g c parameter data _ _ ?_ b')) bot_le
            rw [List.length_append, List.length_singleton]
            omega
        | succ k =>
            rw [truncImpl_sign_succ, bind_map_left, map_bind, advRand_sign, advRand_sign]
            refine val_bind_mono g c _ _ _ _ (fun r _ b' => ih r k _ ?_ b') b
            rw [List.length_append, List.length_singleton]
            omega

/-- The game of an adversary against the game of its truncation after `n ≥ signatureLimit` signing
queries. -/
theorem costGame_le_trunc (parameter : PublicParameter) (data : PublicData) (adversary : Adversary)
    (n : ℕ) (hn : signatureLimit ≤ n) (b : ℕ) :
    val g c (· = true) (costGame parameter data adversary) b ≤
      val g c (· = true) (costGame parameter data (truncSign adversary n)) b := by
  unfold costGame
  refine val_bind_mono g c _ _ _ _ (fun _ _ b' => ?_) b
  rw [costRest_eq, costRest_eq]
  change _ ≤ val g c (· = true) (advRand parameter data
    ((simulateQ truncImpl (adversary.main ⟨data.root, parameter⟩)).run' n) []) b'
  rw [StateT.run'_eq]
  exact advRand_le_trunc g c parameter data _ n [] (by simpa using hn) b'

end Win

/-- **The truncated adversary wins the seed-free game at least as often**, for every truncation
point `n ≥ signatureLimit`. -/
theorem seedFree_le_trunc (adversary : Adversary) (q n : ℕ) (hn : signatureLimit ≤ n)
    (steps : Message → Randomness) :
    Pr[Win | seedFreeExperiment adversary q steps] ≤
      Pr[Win | seedFreeExperiment (truncSign adversary n) q steps] := by
  unfold seedFreeExperiment
  refine probEvent_bind_mono _ _ _ _ fun material => ?_
  refine probEvent_bind_mono _ _ _ _ fun answers => ?_
  refine probEvent_bind_mono _ _ _ _ fun table => ?_
  exact costGame_le_trunc (graphFn material answers table) (graphCoordinates material answers) _ _
    adversary n hn q

/-- **The win comparison for internalized adversaries**: internalizing, then running the seed-free
game, the truncated adversary wins at least as often. -/
theorem seedFree_internalize_le_trunc (adversary : Adversary) (q n : ℕ) (hn : signatureLimit ≤ n)
    (steps : Message → Randomness) :
    Pr[Win | seedFreeExperiment (internalize adversary) q steps] ≤
      Pr[Win | seedFreeExperiment (internalize (truncSign adversary n)) q steps] := by
  rw [internalize_truncSign]
  exact seedFree_le_trunc _ q n hn steps

/-! ### Seed elimination with at most `signatureLimit` signing queries -/

/-- The truncated memoizing adversary never repeats a request. -/
theorem truncMemo_noRepeat (adversary : Adversary) :
    (truncSign (Memo.memoAdv adversary) signatureLimit).NoRepeat :=
  truncSign_noRepeat _ _ (Memo.memoAdv_noRepeat adversary)

/-- The truncated memoizing adversary asks at most `signatureLimit` signatures. -/
theorem truncMemo_signBound (adversary : Adversary) :
    (truncSign (Memo.memoAdv adversary) signatureLimit).SignBound signatureLimit :=
  truncSign_signBound _ _

/-- **Seed elimination for the truncated memoizing adversary.** If the seed-free capped win of the
internalized, truncated memoizing adversary (`truncMemo_noRepeat`, `truncMemo_signBound`) is at most
`B` for every table of walk steps, the SUF-CMA advantage against `Seeded.sign` is at most `B` plus
`2 q / 2^256`. -/
theorem forgeAdvantage_le_seedFree_signBound (adversary : Adversary) (q : ℕ)
    (hbound : HasHashQueryBound adversary q) (B : ℝ≥0∞)
    (hB : ∀ steps, Pr[Win | seedFreeExperiment
      (internalize (truncSign (Memo.memoAdv adversary) signatureLimit)) q steps] ≤ B) :
    forgeAdvantage adversary ≤ B + 2 * (q / (2 : ℝ≥0∞) ^ 256) :=
  Det.forgeAdvantage_le_seedFree adversary q hbound B fun steps =>
    (seedFree_internalize_le_trunc _ q signatureLimit le_rfl steps).trans (hB steps)

/-- **Seed elimination from a bound for every adversary that never repeats a request and asks at
most `signatureLimit` signatures.** -/
theorem forgeAdvantage_le_of_signBound (adversary : Adversary) (q : ℕ)
    (hbound : HasHashQueryBound adversary q) (B : ℝ≥0∞)
    (hB : ∀ A : Adversary, A.NoRepeat → A.SignBound signatureLimit → ∀ steps,
      Pr[Win | seedFreeExperiment (internalize A) q steps] ≤ B) :
    forgeAdvantage adversary ≤ B + 2 * (q / (2 : ℝ≥0∞) ^ 256) :=
  forgeAdvantage_le_seedFree_signBound adversary q hbound B fun steps =>
    hB _ (truncMemo_noRepeat adversary) (truncMemo_signBound adversary) steps

end FORS.Security.SWRoute
