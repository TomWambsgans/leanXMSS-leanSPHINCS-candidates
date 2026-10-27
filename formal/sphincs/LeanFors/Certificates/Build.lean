import LeanFors.Certificates.Closing
import LeanFors.CoverBound.MomentTable

section

/-! **Helpers for the certificates rebuilt from their scalars** (`Certificates/Build.lean`): the
entries of a Poisson table (`poisGo`) and the extension slope of a leaf table (`leafJ`).

**Covers checked option by option.** The chain of a cover reads only the threshold and the bound of
each option: `checkOptB` checks one option and these two numbers, `checkCoverQ` checks the rest of the
cover on the numbers alone, and together they give `checkCoverW` (`checkCoverW_of`). The kernel then
evaluates one option at a time. -/

namespace LeanFors.Security.H0

open LeanFors.Base.H0

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
def checkOptB (H b k a : ℕ) (t : PoisT) (o : OptF) (p : ℚ × ℚ) : Bool :=
  checkOptF H b k a t o && decide (o.cthr = p.1) && decide (o.B = p.2)

/-- `checkEntryF` on the thresholds and the bounds of the options. -/
def checkEntryQ (K N : ℕ) (ps : List (ℚ × ℚ)) (e : EntryF) : Bool :=
  match ps[e.2.2]? with
  | none => false
  | some p =>
      decide (2 * e.2.1 ≤ 2 ^ 128) && decide (p.1 ≤ ForsPotential.betaWQ e.2.1) &&
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
theorem checkOptB_all {H b k a : ℕ} {t : PoisT} : ∀ {opts : List OptF} {ps : List (ℚ × ℚ)},
    List.Forall₂ (fun o p => checkOptB H b k a t o p = true) opts ps →
      opts.all (checkOptF H b k a t) = true ∧ (opts.map fun o => (o.cthr, o.B)) = ps
  | _, _, .nil => ⟨rfl, rfl⟩
  | _, _, .cons (a := o) (b := p) h hs => by
      obtain ⟨h1, h2⟩ := checkOptB_all hs
      simp only [checkOptB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ho, hc⟩, hB⟩ := h
      refine ⟨by simp only [List.all_cons, ho, h1, Bool.and_self], ?_⟩
      simp only [List.map_cons, h2, hc, hB]

/-- **A light cover from its options checked one by one.** -/
theorem checkCoverW_of {H b k a K N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB H b k a c.tab o p = true) c.opts ps)
    (h : checkCoverQ H b K N qstart c ps = true) : checkCoverW H b k a K N qstart c = true := by
  obtain ⟨h1, h2⟩ := checkOptB_all ho
  simp only [checkCoverQ, Bool.and_eq_true] at h
  simp only [checkCoverW, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1, h.1.2⟩, h1⟩, by rw [← chainQ_map, h2]; exact h.2⟩

/-- **A heavy cover from its options checked one by one.** -/
theorem checkCoverH_of {H b k a K N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB H b k a c.tab o p = true) c.opts ps)
    (h : checkCoverQH H b K N qstart c ps = true) : checkCoverH H b k a K N qstart c = true := by
  obtain ⟨h1, h2⟩ := checkOptB_all ho
  simp only [checkCoverQH, Bool.and_eq_true] at h
  simp only [checkCoverH, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1, h.1.2⟩, h1⟩, by rw [← chainQ_map, h2]; exact h.2⟩

end LeanFors.Security.H0

end

section

/-! **Certificates checked by construction.** `buildOpt` and `buildOptN` rebuild an option and a near
certificate from their scalars, computing the leaf tables in integers: the numerators over `2^P` of
the rounded-up bounds, from the numerators of the moment tables (`P1L`, `P2L`,
`CoverBound/MomentTable.lean`; the near table reads `P1L` alone), made convex (`convexZ`), and the
Poisson mean of a table as one integer sum. Their outputs pass `checkOptF` and `checkOptN` by construction (`checkOptF_build`,
`checkOptN_build`): the leaf tables are convex majorants of the bounds, the means and the bound are
rounded up. A Poisson table rebuilt by `poisOf` passes the steps of `checkPT` by construction
(`checkPT_poisOf`), and `expLow` is evaluated in integers (`expLow_eq`). The kernel then evaluates the
construction and a few scalar conditions (`buildOk`, `buildOkN`, `buildOkPT`), not the checkers on top
of it. -/

namespace LeanFors.Security.H0

open LeanFors.Base.H0

/-! ### Convex integer tables -/

theorem getD_eq_get {α : Type*} {l : List α} {n : ℕ} {d : α} (h : n < l.length) : l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- `convexGo` on numerators. -/
def convexGoZ : ℤ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | a, b, x :: xs => max x (2 * b - a) :: convexGoZ b (max x (2 * b - a)) xs

/-- The least convex increasing list above a list (from the left). -/
def convexZ : List ℤ → List ℤ
  | [] => []
  | [x] => [x]
  | x :: y :: xs => x :: max y x :: convexGoZ x (max y x) xs

theorem length_convexGoZ : ∀ (a b : ℤ) (xs : List ℤ), (convexGoZ a b xs).length = xs.length
  | _, _, [] => rfl
  | _, _, _ :: xs => by simp only [convexGoZ, List.length_cons, length_convexGoZ _ _ xs]

theorem length_convexZ : ∀ xs : List ℤ, (convexZ xs).length = xs.length
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: xs => by simp only [convexZ, List.length_cons, length_convexGoZ]

theorem le_convexGoZ : ∀ (a b : ℤ) (xs : List ℤ) (n : ℕ), n < xs.length →
    xs.getD n 0 ≤ (convexGoZ a b xs).getD n 0
  | _, _, [], _, h => absurd h (Nat.not_lt_zero _)
  | _, _, _ :: _, 0, _ => by simp only [convexGoZ, List.getD_cons_zero]; exact le_max_left _ _
  | _, _, _ :: xs, n + 1, h => by
      simp only [convexGoZ, List.getD_cons_succ]
      exact le_convexGoZ _ _ xs n (by simpa using h)

theorem le_convexZ : ∀ (xs : List ℤ) (n : ℕ), n < xs.length → xs.getD n 0 ≤ (convexZ xs).getD n 0
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | [_], 0, _ => le_rfl
  | [_], _ + 1, h => absurd h (by simp)
  | _ :: _ :: _, 0, _ => le_rfl
  | _ :: _ :: _, 1, _ => by
      simp only [convexZ, List.getD_cons_succ, List.getD_cons_zero]; exact le_max_left _ _
  | _ :: _ :: xs, n + 2, h => by
      simp only [convexZ, List.getD_cons_succ]
      exact le_convexGoZ _ _ xs n (by simpa using h)

/-- Increasing and convex, as `checkLeaf` reads it. -/
def LeafShape {α : Type*} [Zero α] [Add α] [Mul α] [OfNat α 2] [LE α] (l : List α) : Prop :=
  (∀ n < l.length - 1, l.getD n 0 ≤ l.getD (n + 1) 0) ∧
    (∀ n < l.length - 2, 2 * l.getD (n + 1) 0 ≤ l.getD n 0 + l.getD (n + 2) 0)

theorem shape_convexGoZ : ∀ (a b : ℤ) (xs : List ℤ), a ≤ b → LeafShape (a :: b :: convexGoZ a b xs)
  | a, b, [], hab => by
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · simp only [convexGoZ, List.length_cons, List.length_nil] at hn
        obtain rfl : n = 0 := by omega
        simpa using hab
      · simp only [convexGoZ, List.length_cons, List.length_nil] at hn
        omega
  | a, b, x :: xs, hab => by
      have hc : b ≤ max x (2 * b - a) := le_trans (by omega) (le_max_right _ _)
      have hc2 : 2 * b ≤ a + max x (2 * b - a) := by have := le_max_right x (2 * b - a); omega
      obtain ⟨ih1, ih2⟩ := shape_convexGoZ b (max x (2 * b - a)) xs hc
      simp only [convexGoZ]
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · cases n with
        | zero => simpa using hab
        | succ n =>
            have := ih1 n (by simp only [List.length_cons] at hn ⊢; omega)
            simpa only [List.getD_cons_succ] using this
      · cases n with
        | zero => simpa using hc2
        | succ n =>
            have := ih2 n (by simp only [List.length_cons] at hn ⊢; omega)
            simpa only [List.getD_cons_succ] using this

theorem shape_convexZ : ∀ xs : List ℤ, LeafShape (convexZ xs)
  | [] => ⟨fun n hn => by simp [convexZ] at hn, fun n hn => by simp [convexZ] at hn⟩
  | [_] => ⟨fun n hn => by simp [convexZ] at hn, fun n hn => by simp [convexZ] at hn⟩
  | x :: y :: xs => shape_convexGoZ x (max y x) xs (le_max_right _ _)

/-- The rationals of the numerators `ks` over `2^P`. -/
def overP (P : ℕ) (ks : List ℤ) : List ℚ := ks.map fun k : ℤ => (k : ℚ) / 2 ^ P

theorem length_overP (P : ℕ) (ks : List ℤ) : (overP P ks).length = ks.length := by simp [overP]

theorem getD_overP {P : ℕ} {ks : List ℤ} {n : ℕ} (h : n < ks.length) :
    (overP P ks).getD n 0 = (ks.getD n 0 : ℚ) / 2 ^ P := by
  rw [getD_eq_get (by rw [length_overP]; exact h), getD_eq_get h]
  simp [overP]

theorem shape_overP (P : ℕ) {ks : List ℤ} (h : LeafShape ks) : LeafShape (overP P ks) := by
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [length_overP] at hn
    rw [getD_overP (by omega), getD_overP (by omega)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h.1 n hn) hP.le
  · rw [length_overP] at hn
    rw [getD_overP (by omega), getD_overP (by omega), getD_overP (by omega), ← mul_div_assoc, ← add_div,
      div_le_div_iff_of_pos_right hP]
    exact_mod_cast h.2 n hn

theorem checkLeaf_overP {P n1 : ℕ} {ks : List ℤ} (hl : ks.length = n1 + 1) (h1 : 1 ≤ n1)
    (h0 : 0 ≤ (overP P (convexZ ks)).getD 0 0) (cap : ℚ) :
    checkLeaf (overP P (convexZ ks)) (leafJ n1 (overP P (convexZ ks)) cap) = true := by
  have hs := shape_overP P (shape_convexZ ks)
  have hl' : (overP P (convexZ ks)).length = n1 + 1 := by rw [length_overP, length_convexZ, hl]
  simp only [checkLeaf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨by omega, h0⟩, hs.1⟩, hs.2⟩, ?_⟩
  rw [hl', show n1 + 1 - 1 = n1 by omega, show n1 + 1 - 2 = n1 - 1 by omega]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

theorem le_leafJ (n1 : ℕ) (tab : List ℚ) (cap : ℚ) : cap ≤ tab.getD n1 0 + leafJ n1 tab cap := by
  have : cap - tab.getD n1 0 ≤ leafJ n1 tab cap := le_trans (le_max_right _ _) (le_max_left _ _)
  linarith

/-- A bound `f` below the numerators `ks` over `2^P` stays below the convex table. -/
theorem le_overP {P : ℕ} {ks : List ℤ} {n : ℕ} (h : n < ks.length) {f : ℚ} (hf : f ≤ (ks.getD n 0 : ℚ) / 2 ^ P) :
    f ≤ (overP P (convexZ ks)).getD n 0 := by
  rw [getD_overP (by rw [length_convexZ]; exact h)]
  exact le_trans hf (div_le_div_of_nonneg_right (by exact_mod_cast le_convexZ ks n h) (by positivity))

/-! ### Rounding up in integers

`cdivZ` and its two bounds are in `CoverBound/MomentBounds.lean`, with the moment numerators. -/

theorem min_overP (a b : ℤ) (P : ℕ) : ((min a b : ℤ) : ℚ) / 2 ^ P = min ((a : ℚ) / 2 ^ P) ((b : ℚ) / 2 ^ P) := by
  rw [Int.cast_min, min_div_div_right (by positivity)]

/-! ### Tables from the moment tables -/

/-- `f` on the first `n1 + 1` entries of two lists. -/
def zipTab {α β γ : Type*} (n1 : ℕ) (f : α → β → γ) (l : List α) (l' : List β) : List γ :=
  (List.zipWith f l l').take (n1 + 1)

theorem length_zipTab {α β γ : Type*} {n1 : ℕ} {f : α → β → γ} {l : List α} {l' : List β}
    (h : n1 + 1 ≤ l.length) (h' : n1 + 1 ≤ l'.length) : (zipTab n1 f l l').length = n1 + 1 := by
  simp [zipTab]; omega

theorem getD_zipTab {α β γ : Type*} {n1 n : ℕ} {f : α → β → γ} {l : List α} {l' : List β} {a : α} {b : β} {c : γ}
    (h : n1 + 1 ≤ l.length) (h' : n1 + 1 ≤ l'.length) (hn : n < n1 + 1) :
    (zipTab n1 f l l').getD n c = f (l.getD n a) (l'.getD n b) := by
  rw [getD_eq_get (by rw [length_zipTab h h']; exact hn), getD_eq_get (by omega), getD_eq_get (by omega)]
  simp [zipTab]

theorem getD_tab {L : List ℕ} {T : List ℚ} (hT : L.map (fun x : ℕ => (x : ℚ) / 2 ^ 128) = T) {n : ℕ}
    (hn : n < L.length) : T.getD n 0 = (L.getD n 0 : ℚ) / 2 ^ 128 := by
  rw [← hT, getD_eq_get (by simpa using hn), getD_eq_get hn]; simp

/-- `2^k` in `ℤ`, by the power in `ℕ`. -/
abbrev p2 (k : ℕ) : ℤ := ((2 ^ k : ℕ) : ℤ)

theorem p2_pos (k : ℕ) : 0 < p2 k := by unfold p2; exact_mod_cast Nat.two_pow_pos k

/-- A power of a moment-table entry, over one power of two. -/
theorem tab_pow (x : ℚ) (k : ℕ) : (x / 2 ^ 128) ^ k = x ^ k / 2 ^ (128 * k) := by
  rw [div_pow, ← pow_mul]

/-- The numerators of `gBound` over `2^191`, `n ≤ n1`, for `k` trees of height `a`. -/
def gZ (H k a n1 : ℕ) (c1 : ℚ) : List ℤ :=
  zipTab n1 (fun x y : ℕ => min (cdivZ (((x ^ k : ℕ) : ℤ) * 2 ^ 191) (p2 (H + 128 * k)))
    (cdivZ (((y ^ k : ℕ) * c1.den : ℕ) * 2 ^ 191) (p2 (2 * H + 128 * k) * 4 * c1.num))) (P1L a) (P2L a)

/-- The numerators of `hBound` over `2^128`, `n ≤ n1`, with `E = ⌈(eC - 1) 2^128⌉`. -/
def hZ (H k a n1 : ℕ) (θ A2 : ℚ) (E : ℤ) : List ℤ :=
  zipTab n1 (fun x y : ℕ => min E
    (cdivZ ((θ.num * A2.den * ((x ^ k : ℕ) : ℤ) * p2 H + A2.num * θ.den * ((y ^ k : ℕ) : ℤ)) * 2 ^ 128)
      (θ.den * A2.den * p2 (2 * H + 128 * k)))) (P1L a) (P2L a)

/-- The numerators of `nBound` over `2^191`, `n ≤ n1`. -/
def nZ (H k a n1 : ℕ) : List ℤ :=
  zipTab n1 (fun x _ : ℕ => cdivZ (((k * x ^ (k - 1) : ℕ) : ℤ) * 2 ^ 191) (p2 (H + 128 * (k - 1))))
    (P1L a) (P1L a)

theorem gZ_bound {H k a n1 n : ℕ} {o : OptF} (hc : 0 < o.c1) (hn1 : n1 ≤ 150) (hn : n < n1 + 1) :
    gBound H k a o n ≤ ((gZ H k a n1 o.c1).getD n 0 : ℚ) / 2 ^ 191 := by
  have l1 : n1 + 1 ≤ (P1L a).length := by rw [length_P1L]; omega
  have l2 : n1 + 1 ≤ (P2L a).length := by rw [length_P2L]; omega
  rw [gZ, getD_zipTab (a := 0) (b := 0) l1 l2 hn, min_overP, gBound, getD_tab (P1L_eq a) (by omega),
    getD_tab (P2L_eq a) (by omega)]
  have hu : 0 < o.c1.num := Rat.num_pos.mpr hc
  have hc1 : (o.c1 : ℚ) = o.c1.num / o.c1.den := (Rat.num_div_den o.c1).symm
  apply min_le_min
  · apply le_cdivZ_div (p2_pos _)
    unfold κQ; simp only [tab_pow]; push_cast; field_simp; ring
  · apply le_cdivZ_div (mul_pos (mul_pos (p2_pos _) (by norm_num)) hu)
    conv_lhs => rw [hc1]
    unfold κQ; simp only [tab_pow]; push_cast
    have : (0 : ℚ) < o.c1.num := by exact_mod_cast hu
    have : (0 : ℚ) < o.c1.den := by exact_mod_cast o.c1.den_pos
    field_simp; ring

theorem hZ_bound {H k a n1 n : ℕ} {o : OptF} {E : ℤ} (hE : o.eC - 1 ≤ (E : ℚ) / 2 ^ 128) (hn1 : n1 ≤ 150)
    (hn : n < n1 + 1) : hBound H k a o n ≤ ((hZ H k a n1 o.θ o.A2 E).getD n 0 : ℚ) / 2 ^ 128 := by
  have l1 : n1 + 1 ≤ (P1L a).length := by rw [length_P1L]; omega
  have l2 : n1 + 1 ≤ (P2L a).length := by rw [length_P2L]; omega
  rw [hZ, getD_zipTab (a := 0) (b := 0) l1 l2 hn, min_overP, hBound, getD_tab (P1L_eq a) (by omega),
    getD_tab (P2L_eq a) (by omega)]
  have hθ : (o.θ : ℚ) = o.θ.num / o.θ.den := (Rat.num_div_den o.θ).symm
  have hA : (o.A2 : ℚ) = o.A2.num / o.A2.den := (Rat.num_div_den o.A2).symm
  apply min_le_min hE
  apply le_cdivZ_div (mul_pos (mul_pos (by exact_mod_cast o.θ.den_pos) (by exact_mod_cast o.A2.den_pos)) (p2_pos _))
  conv_lhs => rw [hθ, hA]
  unfold κQ; simp only [tab_pow]; push_cast
  have : (0 : ℚ) < o.θ.den := by exact_mod_cast o.θ.den_pos
  have : (0 : ℚ) < o.A2.den := by exact_mod_cast o.A2.den_pos
  field_simp; ring

theorem nZ_bound {H k a n1 n : ℕ} (hn1 : n1 ≤ 150) (hn : n < n1 + 1) :
    nBound H k a n ≤ ((nZ H k a n1).getD n 0 : ℚ) / 2 ^ 191 := by
  have l1 : n1 + 1 ≤ (P1L a).length := by rw [length_P1L]; omega
  rw [nZ, getD_zipTab (a := 0) (b := 0) l1 l1 hn, nBound, getD_tab (P1L_eq a) (by omega)]
  apply le_cdivZ_div (p2_pos _)
  unfold κQ; simp only [tab_pow]; push_cast; field_simp; ring

/-! ### Means -/

/-- The mean `poisMean` of `leafQ` over the table `overP P ks`, the weights times the numerators
summed in integers. -/
def meanZ (t : PoisT) (P : ℕ) (ks : List ℤ) (J : ℚ) : ℚ :=
  ((List.zipWith (fun (p : ℕ) (k : ℤ) => (p : ℤ) * k) t.pm ks).sum : ℚ) / 2 ^ (t.P + P) +
    t.pb (t.n1 + 1) * ((overP P ks).getD t.n1 0 / (1 - t.r) + J / (1 - t.r) ^ 2)

theorem sum_map_div (l : List ℚ) (c : ℚ) : (l.map (· / c)).sum = l.sum / c := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, add_div]

theorem meanZ_eq {t : PoisT} {P : ℕ} {ks : List ℤ} (J : ℚ) (hk : ks.length = t.n1 + 1) (hp : 2 ≤ t.pm.length) :
    ((List.range (t.n1 + 1)).map fun n => t.pb n * (overP P ks).getD n 0).sum +
      t.pb (t.n1 + 1) * ((overP P ks).getD t.n1 0 / (1 - t.r) + J / (1 - t.r) ^ 2) = meanZ t P ks J := by
  have hn : t.pm.length = t.n1 + 2 := by unfold PoisT.n1; omega
  have hl : ((List.range (t.n1 + 1)).map fun n => t.pb n * (overP P ks).getD n 0) =
      ((List.zipWith (fun (p : ℕ) (k : ℤ) => (p : ℤ) * k) t.pm ks).map (fun z : ℤ => (z : ℚ))).map
        (· / 2 ^ (t.P + P)) := by
    apply List.ext_getElem
    · simp [hk, hn]
    · intro i h1 _
      have hi : i < t.n1 + 1 := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
      unfold PoisT.pb
      rw [getD_overP (by omega), getD_eq_get (show i < ks.length by omega),
        getD_eq_get (show i < t.pm.length by omega)]
      push_cast
      field_simp
      ring
  unfold meanZ
  rw [hl, sum_map_div, Int.cast_list_sum]

/-! ### The exponential series in integers -/

/-- `expLowGo` on numerators over `2^P`, for `u = un / ud`: the terms `k`, the partial sum `A`. -/
def expLowN (un ud P : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, k, A => A + k
  | r + 1, j, k, A => expLowN un ud P r (j + 1) (k * un / (ud * (j + 1))) (A + k)

theorem expLowGo_eq {u : ℚ} {un ud P : ℕ} (hu : u = (un : ℚ) / ud) (hd : 0 < ud) :
    ∀ (r j k A : ℕ), expLowGo u P r j ((k : ℚ) / 2 ^ P) ((A : ℚ) / 2 ^ P) =
      (expLowN un ud P r j k A : ℚ) / 2 ^ P
  | 0, _, k, A => by simp only [expLowGo, expLowN]; push_cast; ring
  | r + 1, j, k, A => by
      simp only [expLowGo, expLowN]
      rw [← expLowGo_eq hu hd r (j + 1) (k * un / (ud * (j + 1))) (A + k)]
      congr 1
      · unfold rdown
        have e : (k : ℚ) / 2 ^ P * u / ((j : ℚ) + 1) * 2 ^ P = ((k * un : ℕ) : ℚ) / ((ud * (j + 1) : ℕ) : ℚ) := by
          rw [hu]; push_cast; field_simp
        rw [e, Rat.floor_natCast_div_natCast, ← Int.natCast_div, Int.cast_natCast]
      · push_cast; ring

/-- **`expLow` in integers.** -/
theorem expLow_eq {u : ℚ} {un ud J P : ℕ} (hd : 0 < ud) (hu : u = (un : ℚ) / ud) :
    expLow u J P = (expLowN un ud P J 0 (2 ^ P) 0 : ℚ) / 2 ^ P := by
  unfold expLow
  rw [← expLowGo_eq hu hd]
  push_cast
  rw [div_self (by positivity), zero_div]

/-! ### Options -/

/-- The option with cap `c1`, Chernoff parameter `θ`, `s` squarings and threshold `cthr`. -/
def buildOpt (H b k a : ℕ) (t : PoisT) (c1 θ : ℚ) (s : ℕ) (cthr : ℚ) : OptF :=
  let eC := expUp (θ * c1) s t.P
  let A2 := rup ((eC - 1 - θ * c1) / c1 ^ 2) (2 * 127 + 64)
  let gk := convexZ (gZ H k a t.n1 c1)
  let hk := convexZ (hZ H k a t.n1 θ A2 ⌈(eC - 1) * 2 ^ 128⌉)
  let gt := overP 191 gk
  let ht := overP 128 hk
  let Jg := leafJ t.n1 gt (κQ H)
  let Jh := leafJ t.n1 ht (eC - 1)
  let Eg := rup (meanZ t 191 gk Jg) (64 + 127 + 2 * b)
  let Ee := rup (meanZ t 128 hk Jh) (64 + 2 * b)
  let L := (expLowN (θ * cthr).num.toNat (θ * cthr).den t.P t.J 0 (2 ^ t.P) 0 : ℚ) / 2 ^ t.P
  let B := rup (2 ^ b * Eg + sqUp t.P b (1 + Ee) / (L * eLowQ * θ)) (64 + 127)
  ⟨c1, θ, cthr, s, eC, A2, gt, Jg, ht, Jh, Eg, Ee, B⟩

/-- What `checkOptF` needs beyond the construction. -/
def buildOk (t : PoisT) (o : OptF) : Bool :=
  decide (0 < o.c1) && decide (0 < o.θ) && decide (0 ≤ o.cthr) && decide (o.θ * o.c1 < 2 ^ o.s) &&
    decide (1 ≤ t.n1) && decide (t.n1 ≤ 150) && decide (0 ≤ o.gt.getD 0 0) && decide (0 ≤ o.ht.getD 0 0) &&
    decide (0 ≤ o.Eg) && decide (0 ≤ o.Ee)

/-- **A built option passes `checkOptF`.** -/
theorem checkOptF_build {H b k a : ℕ} {t : PoisT} {c1 θ : ℚ} {s : ℕ} {cthr : ℚ}
    (h : buildOk t (buildOpt H b k a t c1 θ s cthr) = true) :
    checkOptF H b k a t (buildOpt H b k a t c1 θ s cthr) = true := by
  simp only [buildOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hn1⟩, hn⟩, hg0⟩, hh0⟩, hEg⟩, hEe⟩ := h
  set o := buildOpt H b k a t c1 θ s cthr with ho
  have hp : 2 ≤ t.pm.length := by unfold PoisT.n1 at hn1; omega
  have l1 : t.n1 + 1 ≤ (P1L a).length := by rw [length_P1L]; omega
  have l2 : t.n1 + 1 ≤ (P2L a).length := by rw [length_P2L]; omega
  have lgz : (gZ H k a t.n1 c1).length = t.n1 + 1 := length_zipTab l1 l2
  have lhz : (hZ H k a t.n1 θ o.A2 ⌈(o.eC - 1) * 2 ^ 128⌉).length = t.n1 + 1 := length_zipTab l1 l2
  have lg : (convexZ (gZ H k a t.n1 c1)).length = t.n1 + 1 := by rw [length_convexZ, lgz]
  have lh : (convexZ (hZ H k a t.n1 θ o.A2 ⌈(o.eC - 1) * 2 ^ 128⌉)).length = t.n1 + 1 := by
    rw [length_convexZ, lhz]
  have hE : o.eC - 1 ≤ (⌈(o.eC - 1) * 2 ^ 128⌉ : ℚ) / 2 ^ 128 := by
    rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _
  have p12 : ∀ n < t.n1 + 1, gBound H k a o n ≤ o.gt.getD n 0 := fun n hn' =>
    le_overP (lt_of_lt_of_eq hn' lgz.symm) (gZ_bound (o := o) h1 hn hn')
  have p13 : ∀ n < t.n1 + 1, hBound H k a o n ≤ o.ht.getD n 0 := fun n hn' =>
    le_overP (lt_of_lt_of_eq hn' lhz.symm) (hZ_bound (o := o) hE hn hn')
  have hL : expLow (o.θ * o.cthr) t.J t.P =
      (expLowN (θ * cthr).num.toNat (θ * cthr).den t.P t.J 0 (2 ^ t.P) 0 : ℚ) / 2 ^ t.P := by
    have h0 : 0 ≤ (θ * cthr).num := Rat.num_nonneg.mpr (mul_nonneg h2.le h3)
    refine expLow_eq (θ * cthr).den_pos ?_
    show θ * cthr = _
    rw [show (((θ * cthr).num.toNat : ℕ) : ℚ) = ((θ * cthr).num : ℚ) by exact_mod_cast Int.toNat_of_nonneg h0,
      Rat.num_div_den]
  have p18 : 2 ^ b * o.Eg + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B := by
    rw [hL]; exact le_rup _ _
  simp only [checkOptF, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, le_rfl⟩, le_rup _ _⟩, hn⟩,
    (length_overP _ _).trans lg⟩, (length_overP _ _).trans lh⟩,
    checkLeaf_overP lgz hn1 hg0 _⟩, checkLeaf_overP lhz hn1 hh0 _⟩, p12⟩, p13⟩,
    le_leafJ _ _ _⟩, le_leafJ _ _ _⟩, ?_⟩, ?_⟩, p18⟩, hEg⟩, hEe⟩
  · exact (meanZ_eq (P := 191) o.Jg lg hp).trans_le (le_rup _ _)
  · exact (meanZ_eq (P := 128) o.Jh lh hp).trans_le (le_rup _ _)

/-- The check of a built option with its threshold and its bound `p = (cthr, B)`. -/
theorem checkOptB_build {H b k a : ℕ} {t : PoisT} {c1 θ : ℚ} {s : ℕ} {cthr : ℚ} {p : ℚ × ℚ}
    (h : (buildOk t (buildOpt H b k a t c1 θ s cthr) && decide (cthr = p.1) &&
      decide ((buildOpt H b k a t c1 θ s cthr).B = p.2)) = true) :
    checkOptB H b k a t (buildOpt H b k a t c1 θ s cthr) p = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [checkOptB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨checkOptF_build h1, h2⟩, h3⟩

/-! ### Near certificates -/

/-- The near certificate of a Poisson table. -/
def buildOptN (H b k a : ℕ) (t : PoisT) : OptN :=
  let nk := convexZ (nZ H k a t.n1)
  let nt := overP 191 nk
  let Jn := leafJ t.n1 nt ((k : ℚ) * κQ H)
  ⟨nt, Jn, rup (meanZ t 191 nk Jn) (64 + 127 + 2 * b)⟩

/-- What `checkOptN` needs beyond the construction. -/
def buildOkN (t : PoisT) (o : OptN) : Bool :=
  decide (1 ≤ t.n1) && decide (t.n1 ≤ 150) && decide (0 ≤ o.nt.getD 0 0)

/-- **A built near certificate passes `checkOptN`.** -/
theorem checkOptN_build {H b k a : ℕ} {t : PoisT} (h : buildOkN t (buildOptN H b k a t) = true) :
    checkOptN H k a t (buildOptN H b k a t) = true := by
  simp only [buildOkN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn1, hn⟩, h0⟩ := h
  have hp : 2 ≤ t.pm.length := by unfold PoisT.n1 at hn1; omega
  have l1 : t.n1 + 1 ≤ (P1L a).length := by rw [length_P1L]; omega
  have lnz : (nZ H k a t.n1).length = t.n1 + 1 := length_zipTab l1 l1
  have ln : (convexZ (nZ H k a t.n1)).length = t.n1 + 1 := by rw [length_convexZ, lnz]
  simp only [checkOptN, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hn, (length_overP _ _).trans ln⟩, checkLeaf_overP lnz hn1 h0 _⟩,
    fun n hn' => le_overP (lt_of_lt_of_eq hn' lnz.symm) (nZ_bound hn hn')⟩, le_leafJ _ _ _⟩, ?_⟩
  exact (meanZ_eq (P := 191) _ ln hp).trans_le (le_rup _ _)

/-! ### Poisson tables -/

theorem le_ceilDiv (a d : ℕ) (hd : 0 < d) : a ≤ (a + (d - 1)) / d * d := by
  have h1 := Nat.div_add_mod (a + (d - 1)) d
  have h2 := Nat.mod_lt (a + (d - 1)) hd
  rw [Nat.mul_comm]
  omega

theorem length_poisGo (m : ℕ) : ∀ (k n p : ℕ), (poisGo m k n p).length = k
  | 0, _, _ => rfl
  | k + 1, n, _ => by simp only [poisGo, List.length_cons, length_poisGo m k (n + 1)]

/-- Each entry of a rebuilt table passes the step of `checkPT` to the next. -/
theorem poisGo_step (m : ℕ) : ∀ (k n p i : ℕ), i < k →
    (p :: poisGo m k n p).getD i 0 * m ≤ (p :: poisGo m k n p).getD (i + 1) 0 * ((n + i + 1) * 2 ^ 64)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, p, 0, _ => by
      simp only [poisGo, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      exact le_ceilDiv _ _ (by positivity)
  | k + 1, n, p, i + 1, h => by
      have := poisGo_step m k (n + 1) ((p * m + ((n + 1) * 2 ^ 64 - 1)) / ((n + 1) * 2 ^ 64)) i (by omega)
      simp only [poisGo, List.getD_cons_succ] at this ⊢
      rwa [show n + (i + 1) + 1 = n + 1 + i + 1 by omega]

/-- The Poisson table of rate `m / 2^64` with entries `0, …, n1 + 1`, precision `P`, `J + 1` terms
of the exponential series and first weight `p0` (with `p0 ≥ 2^P / expLow μ̄ J P` given instead of
computed: `checkPT` checks it). -/
def poisOf (m P J n1 p0 : ℕ) : PoisT := ⟨m, P, J, p0 :: poisGo m (n1 + 1) 0 p0⟩

/-- What `checkPT` needs beyond the construction: the first weight, through `expLowN`. -/
def buildOkPT (t : PoisT) : Bool :=
  decide (2 ^ t.P * 2 ^ t.P ≤ t.pm.getD 0 0 * expLowN t.m (2 ^ 64) t.P t.J 0 (2 ^ t.P) 0) && decide (t.r < 1)

/-- **A rebuilt Poisson table passes `checkPT`.** -/
theorem checkPT_poisOf {m P J n1 p0 : ℕ} (h : buildOkPT (poisOf m P J n1 p0) = true) :
    checkPT (poisOf m P J n1 p0) = true := by
  simp only [buildOkPT, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [checkPT, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, fun n hn => ?_⟩, h.2⟩
  · show 2 ≤ (_ :: poisGo _ _ _ _).length
    simp only [List.length_cons, length_poisGo]; omega
  · rw [expLow_eq (by positivity) (show (poisOf m P J n1 p0).mu = (m : ℚ) / ((2 ^ 64 : ℕ) : ℚ) by
      simp only [PoisT.mu, poisOf, Nat.cast_pow, Nat.cast_ofNat])]
    have h1 : ((2 ^ (poisOf m P J n1 p0).P * 2 ^ (poisOf m P J n1 p0).P : ℕ) : ℚ) ≤
        (((poisOf m P J n1 p0).pm.getD 0 0 * expLowN (poisOf m P J n1 p0).m (2 ^ 64) (poisOf m P J n1 p0).P
          (poisOf m P J n1 p0).J 0 (2 ^ (poisOf m P J n1 p0).P) 0 : ℕ) : ℚ) := by exact_mod_cast h.1
    push_cast at h1
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    exact h1
  · have hl : (poisOf m P J n1 p0).pm.length = n1 + 2 := by
      show (_ :: poisGo _ _ _ _).length = _
      simp only [List.length_cons, length_poisGo]
    have := poisGo_step m (n1 + 1) 0 p0 n (by omega)
    rw [show 0 + n + 1 = n + 1 by omega] at this
    exact this

/-- **A light cover from its options and its table checked separately.** -/
theorem checkCoverW_of_pt {H b k a K N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB H b k a c.tab o p = true) c.opts ps) (hpt : checkPT c.tab = true)
    (h : (checkRate H b N c.qtop c.tab && chainQ K N c.qtop ps qstart c.entries) = true) :
    checkCoverW H b k a K N qstart c = true := by
  simp only [Bool.and_eq_true] at h
  exact checkCoverW_of ps ho (by simp only [checkCoverQ, h.1, hpt, h.2, Bool.and_self])

/-- **A heavy cover from its options and its table checked separately.** -/
theorem checkCoverH_of_pt {H b k a K N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB H b k a c.tab o p = true) c.opts ps) (hpt : checkPT c.tab = true)
    (h : (checkRateH H b N c.qtop c.tab && chainQ K N c.qtop ps qstart c.entries) = true) :
    checkCoverH H b k a K N qstart c = true := by
  simp only [Bool.and_eq_true] at h
  exact checkCoverH_of ps ho (by simp only [checkCoverQH, h.1, hpt, h.2, Bool.and_self])

end LeanFors.Security.H0

end
