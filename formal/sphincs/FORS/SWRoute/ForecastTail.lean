import FORS.CoverBound.NearOption

/-! **The tail of the own-cell near forecast: the predicate `ForecastTail`.** The route charges
`ν m` of a surviving FORS leaf query's near cost in `cU`; the rest, `ν (min(1, Π_c) - m)⁺`, is paid by
an additive term `x Pb` (`ν · XS m ≤ x Pb`, WP-F). `ForecastTail m q Pb` is the numeric statement
behind it: for a cap `n0`, a rate `μ` at least the rate of the one-coin future, and Chernoff
parameters `θ_D`,
  `(1 - m)⁺ · ( 2^b E_μ[(n - (n0 - 1))⁺]
              + Σ_{D < n0} k 2^a 2^b (μ^D / D!) e^{-θ_D (m - fresh_D - 2^-10)} Γ_D^q + 2^-99 ) ≤ Pb`.

* The first term forecasts an index with at least `n0` disclosed views (the light failure,
  `ForecastLight.lean`).
* The `D`-term is a union over the cells `c` and the sets `Q` of `D` views disclosed at the cell's
  index (`E[C(n_I, D)] ≤ μ^D / D!`) of a Chernoff bound for the cached part of the forecast at `c`
  relative to `Q`: every cached pair at `c` with `r ≥ 1` trees other than `κ` missing from `Q` weighs
  at most `φ(r) = E_{j ~ Pois(μ)}[(j / 2^a)^r] = T_r(μ) / 2^(a r)` (Touchard), and a uniform view opens
  `c` with `r` missing trees with chance at most `2^-(b+a) C(k-1, r) (D / 2^a)^(k-1-r)`
  (`ForecastCells.lean`), so the exponential moment of the cached part over `q` new pairs is at most
  `Γ_D^q`, `Γ_D = 1 + 2^-(b+a) Σ_{1 ≤ r < k} C(k-1, r) (D / 2^a)^(k-1-r) (e^{θ_D φ(r)} - 1)`.
* `fresh_D = q 2^-(b+a) E_{j ~ Pois(μ)}[((D + j) / 2^a)^(k-1)]` bounds the fresh part of the forecast at
  a state with `D` distinct views disclosed at the index; `2^-10` is the allowance for the coins of
  the cached pairs (a signature using a cached pair) in the forecast; `2^-99` covers the failure of
  the cell-count events.
* `(1 - m)⁺`: the excess form (`(min(1, Π_c) - m)⁺ ≤ (1 - m)⁺ 1[Π_c > m]`).

The rational checker and its soundness are in `ForecastCert.lean`. -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Security FORS.Security.H0 FORS.Base.H0 ForsPrice

set_option linter.unusedSectionVars false

/-! ### Closed forms (generic in the field, so that the rational checker and the real statement
share them) -/

/-- The binomial coefficient through factorials. -/
def chooseK {K : Type} [DivisionRing K] (n j : ℕ) : K := (n.factorial : K) / (j.factorial * (n - j).factorial)

/-- The Touchard polynomials `T_0, …` at `μ` (`T_{n+1} = μ Σ_{i ≤ n} C(n, i) T_i`), built iteratively:
`s` more steps after `T_0 … T_n` in `L`. -/
def touchardGo {K : Type} [DivisionRing K] (μ : K) : ℕ → ℕ → List K → List K
  | 0, _, L => L
  | s + 1, n, L => touchardGo μ s (n + 1)
      (L ++ [μ * ((List.range (n + 1)).map fun i => chooseK n i * L.getD i 0).sum])

/-- `T_r(μ) = E_{j ~ Pois(μ)}[j^r]`. -/
def touchard {K : Type} [DivisionRing K] (μ : K) (r : ℕ) : K := (touchardGo μ r 0 [1]).getD r 0

/-- **The per-pair weight** at `r` missing trees: `φ(r) = T_r(μ) / 2^(a r)`. -/
def phiK {K : Type} [DivisionRing K] (a : ℕ) (μ : K) (r : ℕ) : K := touchard μ r / 2 ^ (a * r)

/-- **The fresh part** at `D` distinct disclosed views: `q 2^-(b+a) Σ_{i < k} C(k-1, i) D^(k-1-i) T_i(μ) / 2^(a(k-1))`. -/
def freshK {K : Type} [DivisionRing K] (b k a : ℕ) (μ : K) (q D : ℕ) : K :=
  (q : K) / 2 ^ (b + a) *
    (((List.range k).map fun i => chooseK (k - 1) i * (D : K) ^ (k - 1 - i) * touchard μ i).sum / 2 ^ (a * (k - 1)))

/-- **The mean pair factor** `Γ_D` at Chernoff parameter `θ` and weights `φ`. -/
noncomputable def gammaR (b k a : ℕ) (θ : ℝ) (φ : ℕ → ℝ) (D : ℕ) : ℝ :=
  1 + ((List.range k).map fun j => if 1 ≤ j then
    chooseK (k - 1) j * ((D : ℝ) / 2 ^ a) ^ (k - 1 - j) * (Real.exp (θ * φ j) - 1) else 0).sum / 2 ^ (b + a)

/-- The allowance for the coins of the cached pairs in the forecast. -/
noncomputable def coinSlack : ℝ := 1 / 2 ^ 10

/-- **The tail sum** (before the excess factor). -/
noncomputable def tailSum (b k a : ℕ) (n0 : ℕ) (μ : ℝ≥0) (θ : ℕ → ℝ) (m : ℝ) (q : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ b * poisMean μ (fun n => ((n - (n0 - 1) : ℕ) : ℝ≥0∞)) +
    ∑ D ∈ Finset.range n0, (k : ℝ≥0∞) * 2 ^ a * 2 ^ b * ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) *
      ENNReal.ofReal (Real.exp (-(θ D * (m - freshK b k a (μ : ℝ) q D - coinSlack)))) *
      ENNReal.ofReal (gammaR b k a (θ D) (phiK a (μ : ℝ)) D) ^ q +
    ENNReal.ofReal (1 / 2 ^ 99)

/-- **The tail predicate** of the SW route at cap `m`, budget `q` and per-unit tail `Pb`. -/
def ForecastTail (m : ℝ) (q : ℕ) (Pb : ℝ) : Prop :=
  ∃ (n0 : ℕ) (μ : ℝ≥0) (θ : ℕ → ℝ),
    1 ≤ n0 ∧
    (signatureLimit : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * wbarOf q).toReal / 2 ^ subtreeHeight ≤ μ ∧
    (∀ D, 0 ≤ θ D) ∧
    ENNReal.ofReal (1 - m) * tailSum subtreeHeight forsTrees forsHeight n0 μ θ m q ≤ ENNReal.ofReal Pb

end FORS.Security.SWRoute
