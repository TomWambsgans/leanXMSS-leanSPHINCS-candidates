import LeanForest.BridgeHeavyCert

/-! **Helpers for the certificates rebuilt from their scalars** (`Certificates/Build.lean`): the
entries of a Poisson table (`poisGo`) and the extension slope of a leaf table (`leafJ`).

**Covers checked option by option.** The chain of a cover reads only the threshold and the bound of
each option: `checkOptB` checks one option and these two numbers, `checkCoverQ` checks the rest of the
cover on the numbers alone, and together they give `checkCoverW` (`checkCoverW_of`). The kernel then
evaluates one option at a time. -/

namespace LeanForest.Security.H0

open LeanForest.Base.H0

/-! ### Tables -/

/-- The entries of a Poisson table after the first: `p (n + 1) = ⌈p n · m / ((n + 1) 2^64)⌉`. -/
def poisGo (m : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | k + 1, n, p =>
      ((p * m + ((n + 1) * 2 ^ 64 - 1)) / ((n + 1) * 2 ^ 64)) ::
        poisGo m k (n + 1) ((p * m + ((n + 1) * 2 ^ 64 - 1)) / ((n + 1) * 2 ^ 64))

/-- The extension slope of a leaf table with cap `cap`. -/
def leafJ (n1 : ℕ) (tab : List ℚ) (cap : ℚ) : ℚ :=
  max (max (tab.getD n1 0 - tab.getD (n1 - 1) 0) (cap - tab.getD n1 0)) 0

/-! ### Covers option by option -/

/-- The check of one option, with its threshold and its bound `p = (cthr, B)`. -/
def checkOptB (H b : ℕ) (t : PoisT) (o : OptF) (p : ℚ × ℚ) : Bool :=
  checkOptF H b t o && decide (o.cthr = p.1) && decide (o.B = p.2)

/-- `checkEntryF` on the thresholds and the bounds of the options. -/
def checkEntryQ (K N : ℕ) (ps : List (ℚ × ℚ)) (e : EntryF) : Bool :=
  match ps[e.2.2]? with
  | none => false
  | some p =>
      decide (2 * e.2.1 ≤ 2 ^ 128) && decide (p.1 ≤ ForestPotential.betaWQ e.2.1) &&
        decide ((e.2.1 : ℚ) * p.2 + ((e.2.1 : ℚ) + K + N) / 2 ^ 200 ≤
          ((e.1 : ℚ) / 2 ^ 128) ^ 2 + (K : ℚ) / 2 ^ 127)

/-- `chainF` on the thresholds and the bounds of the options. -/
def chainQ (K N qtop : ℕ) (ps : List (ℚ × ℚ)) : ℕ → List EntryF → Bool
  | last, [] => decide (qtop < last)
  | last, e :: rest => decide (e.1 ≤ last) && checkEntryQ K N ps e && chainQ K N qtop ps (e.2.1 + 1) rest

/-- The checks of a light cover that do not open its options. -/
def checkCoverQ (H b K N qstart : ℕ) (c : CoverW) (ps : List (ℚ × ℚ)) : Bool :=
  checkRate H b N c.qtop c.tab && checkPT c.tab && chainQ K N c.qtop ps qstart c.entries

/-- The checks of a heavy cover that do not open its options. -/
def checkCoverQH (H b K N qstart : ℕ) (c : CoverW) (ps : List (ℚ × ℚ)) : Bool :=
  checkRateH H b N c.qtop c.tab && checkPT c.tab && chainQ K N c.qtop ps qstart c.entries

theorem checkEntryQ_map (K N : ℕ) (opts : List OptF) (e : EntryF) :
    checkEntryQ K N (opts.map fun o => (o.cthr, o.B)) e = checkEntryF K N opts e := by
  unfold checkEntryQ checkEntryF
  rw [List.getElem?_map]
  cases opts[e.2.2]? <;> rfl

theorem chainQ_map (K N qtop : ℕ) (opts : List OptF) : ∀ (es : List EntryF) (last : ℕ),
    chainQ K N qtop (opts.map fun o => (o.cthr, o.B)) last es = chainF K N qtop opts last es
  | [], _ => rfl
  | e :: rest, last => by
      simp only [chainQ, chainF, checkEntryQ_map, chainQ_map K N qtop opts rest]

/-- Options checked one by one pass `checkOptF`, and `ps` lists their thresholds and bounds. -/
theorem checkOptB_all {H b : ℕ} {t : PoisT} : ∀ {opts : List OptF} {ps : List (ℚ × ℚ)},
    List.Forall₂ (fun o p => checkOptB H b t o p = true) opts ps →
      opts.all (checkOptF H b t) = true ∧ (opts.map fun o => (o.cthr, o.B)) = ps
  | _, _, .nil => ⟨rfl, rfl⟩
  | _, _, .cons (a := o) (b := p) h hs => by
      obtain ⟨h1, h2⟩ := checkOptB_all hs
      simp only [checkOptB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ho, hc⟩, hB⟩ := h
      refine ⟨by simp only [List.all_cons, ho, h1, Bool.and_self], ?_⟩
      simp only [List.map_cons, h2, hc, hB]

/-- **A light cover from its options checked one by one.** -/
theorem checkCoverW_of {H b K N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB H b c.tab o p = true) c.opts ps)
    (h : checkCoverQ H b K N qstart c ps = true) : checkCoverW H b K N qstart c = true := by
  obtain ⟨h1, h2⟩ := checkOptB_all ho
  simp only [checkCoverQ, Bool.and_eq_true] at h
  simp only [checkCoverW, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1, h.1.2⟩, h1⟩, by rw [← chainQ_map, h2]; exact h.2⟩

/-- **A heavy cover from its options checked one by one.** -/
theorem checkCoverH_of {H b K N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB H b c.tab o p = true) c.opts ps)
    (h : checkCoverQH H b K N qstart c ps = true) : checkCoverH H b K N qstart c = true := by
  obtain ⟨h1, h2⟩ := checkOptB_all ho
  simp only [checkCoverQH, Bool.and_eq_true] at h
  simp only [checkCoverH, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1, h.1.2⟩, h1⟩, by rw [← chainQ_map, h2]; exact h.2⟩

end LeanForest.Security.H0
