import LeanSphincs.H0Bound

/-! The H-term bound for the six lifetimes. Each parameter set has a rational certificate: a
cover of all budgets `0 ≤ q ≤ 2^127` by intervals, each checked by the kernel (`decide +kernel`,
exact rational arithmetic, no `native_decide`). The statements are generic in `[Params]` with the
subtree height and the signature limit as hypotheses; for an instance whose fields are literals,
both hypotheses are `rfl`. -/

open ENNReal

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice

set_option exponentiation.threshold 4000

/-- **(a)** The fair-share hypotheses of the grinding signer at every budget `q' ≤ 2^127`
(any parameter set). -/
theorem h0_fair [Params] (q' : ℕ) (hq : 2 * q' ≤ 2 ^ 128) :
    ForsPotential.Fair ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹ (q' + 2 ^ 32) :=
  fair_of q' hq

/-- **(b)** for any parameter set whose certificate checks. -/
theorem h0_bound_of_cover [Params] (b N : ℕ) (cover : List Entry) (hcov : checkCover b N cover = true)
    (hb : subtreeHeight = b) (hN : signatureLimit = N) (q' : ℕ) (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * creations Finset.univ landing (fun I => virtual Finset.univ
          ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹
          (ForsPotential.excess (HiddenDebt.baseline q')) signatureLimit I 0) q' [] +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  have hq127 : q' ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  obtain ⟨c, -, h1, h2, h3⟩ := checkCover_sound b N cover hcov q' hq127
  exact bound_of_entry b N hb hN c h3 q' h1 h2

/-- Certificate for `full` (subtree height 26, 540000000 signatures). -/
def cover_full : List Entry := [
    (0, 107295178558560072632100802961, 5, 138, 148434069796563071717),
    (107295178558560072632100802962, 13205697364738223225301817519437524536, 5, 138, 154427084801525917422),
    (13205697364738223225301817519437524537, 141529951136128670190519715453103117575, 4, 130, 254132742923954606616),
    (141529951136128670190519715453103117576, 166495408744953076258264087380307879750, 1, 80, 290640316835556533290),
    (166495408744953076258264087380307879751, 170141183460469231731687303715884105728, 1, 80, 296868139499520000001)]

set_option maxRecDepth 100000 in
theorem cover_full_ok : checkCover 26 540000000 cover_full = true := by decide +kernel

/-- **(b)** for `Lifetimes.full` (subtree height 26, 540000000 signatures). -/
theorem h0_bound_full [Params] (hb : subtreeHeight = 26) (hN : signatureLimit = 540000000) (q' : ℕ)
    (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * creations Finset.univ landing (fun I => virtual Finset.univ
          ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹
          (ForsPotential.excess (HiddenDebt.baseline q')) signatureLimit I 0) q' [] +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  h0_bound_of_cover 26 540000000 cover_full cover_full_ok hb hN q' hq

/-- Certificate for `pruned20` (subtree height 20, 10650000 signatures). -/
def cover_pruned20 : List Entry := [
    (0, 3893926689066376949106902, 4, 139, 187356781373032543966),
    (3893926689066376949106903, 326706358392772599108349598, 4, 139, 187356781373210281939),
    (326706358392772599108349599, 2275064036162739204788051401384, 4, 139, 187356782625662682830),
    (2275064036162739204788051401385, 13205697364738223225301820731143497368, 4, 138, 194921298149481602434),
    (13205697364738223225301820731143497369, 143071111258933163793427965448032504776, 3, 131, 323278754096926825887),
    (143071111258933163793427965448032504777, 168308424877071660585620408967917532943, 1, 80, 370720169966454980955),
    (168308424877071660585620408967917532944, 170141183460469231731687303715884105728, 1, 80, 374713562746060800001)]

set_option maxRecDepth 100000 in
theorem cover_pruned20_ok : checkCover 20 10650000 cover_pruned20 = true := by decide +kernel

/-- **(b)** for `Lifetimes.pruned20` (subtree height 20, 10650000 signatures). -/
theorem h0_bound_pruned20 [Params] (hb : subtreeHeight = 20) (hN : signatureLimit = 10650000) (q' : ℕ)
    (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * creations Finset.univ landing (fun I => virtual Finset.univ
          ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹
          (ForsPotential.excess (HiddenDebt.baseline q')) signatureLimit I 0) q' [] +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  h0_bound_of_cover 20 10650000 cover_pruned20 cover_pruned20_ok hb hN q' hq

/-- Certificate for `pruned14` (subtree height 14, 185000 signatures). -/
def cover_pruned14 : List Entry := [
    (0, 37371977707383687980073, 4, 138, 208291482765885462876),
    (37371977707383687980074, 55792914340881973897864, 4, 138, 208291482765885474152),
    (55792914340881973897865, 78053153034565107368800, 4, 138, 208291482765885487778),
    (78053153034565107368801, 116526155382803039758280, 4, 138, 208291482765885511328),
    (116526155382803039758281, 213709911250252303767142, 4, 138, 208291482765885570815),
    (213709911250252303767143, 631224769161565109011935, 4, 138, 208291482765885826382),
    (631224769161565109011936, 5216567126386629074239776, 4, 138, 208291482765888633132),
    (5216567126386629074239777, 352438011812110858734001995, 4, 138, 208291482766101172119),
    (352438011812110858734001996, 1608713207604309675039788435974, 4, 138, 208291483750600763257),
    (1608713207604309675039788435975, 8845621946008041886907800921140751508, 4, 138, 213850515489489561479),
    (8845621946008041886907800921140751509, 154339506117684383390148781058133964003, 2, 132, 381181178233259524115),
    (154339506117684383390148781058133964004, 170141183460469231731687303715884105728, 1, 80, 416582965531770880001)]

set_option maxRecDepth 100000 in
theorem cover_pruned14_ok : checkCover 14 185000 cover_pruned14 = true := by decide +kernel

/-- **(b)** for `Lifetimes.pruned14` (subtree height 14, 185000 signatures). -/
theorem h0_bound_pruned14 [Params] (hb : subtreeHeight = 14) (hN : signatureLimit = 185000) (q' : ℕ)
    (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * creations Finset.univ landing (fun I => virtual Finset.univ
          ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹
          (ForsPotential.excess (HiddenDebt.baseline q')) signatureLimit I 0) q' [] +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  h0_bound_of_cover 14 185000 cover_pruned14 cover_pruned14_ok hb hN q' hq

/-- Certificate for `pruned13` (subtree height 13, 93000 signatures). -/
def cover_pruned13 : List Entry := [
    (0, 29448760505317819344393, 4, 138, 209417382672728082124),
    (29448760505317819344394, 47426944081703384916371, 4, 138, 209417382672728093188),
    (47426944081703384916372, 75557863725914323419137, 4, 138, 209417382672728110501),
    (75557863725914323419138, 146284693157640062574549, 4, 138, 209417382672728154027),
    (146284693157640062574550, 466104621531212159033121, 4, 138, 209417382672728350852),
    (466104621531212159033122, 4482646466679690002268333, 4, 138, 209417382672730822721),
    (4482646466679690002268334, 410140875523898904758740898, 4, 138, 209417382672980473873),
    (410140875523898904758740899, 3433445713873922324227318593295, 4, 138, 209417384785747403526),
    (3433445713873922324227318593296, 17125670689343129364093801722672146187, 4, 137, 220515444925806159908),
    (17125670689343129364093801722672146188, 162927755463683233669387287224634487334, 2, 132, 401799773147926694231),
    (162927755463683233669387287224634487335, 170141183460469231731687303715884105728, 1, 80, 418834765345456128001)]

set_option maxRecDepth 100000 in
theorem cover_pruned13_ok : checkCover 13 93000 cover_pruned13 = true := by decide +kernel

/-- **(b)** for `Lifetimes.pruned13` (subtree height 13, 93000 signatures). -/
theorem h0_bound_pruned13 [Params] (hb : subtreeHeight = 13) (hN : signatureLimit = 93000) (q' : ℕ)
    (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * creations Finset.univ landing (fun I => virtual Finset.univ
          ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹
          (ForsPotential.excess (HiddenDebt.baseline q')) signatureLimit I 0) q' [] +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  h0_bound_of_cover 13 93000 cover_pruned13 cover_pruned13_ok hb hN q' hq

/-- Certificate for `pruned12` (subtree height 12, 47000 signatures). -/
def cover_pruned12 : List Entry := [
    (0, 18088614546627827380718, 4, 138, 211669182486413323252),
    (18088614546627827380719, 26425978863243489462775, 4, 138, 211669182486413328439),
    (26425978863243489462776, 35787528458784578588486, 4, 138, 211669182486413334262),
    (35787528458784578588487, 50611208110226258753115, 4, 138, 211669182486413343483),
    (50611208110226258753116, 82396434656777346015107, 4, 138, 211669182486413363254),
    (82396434656777346015108, 189707776326813539665500, 4, 138, 211669182486413430006),
    (189707776326813539665501, 922167497395701782356289, 4, 138, 211669182486413885625),
    (922167497395701782356290, 21555374498566658790375376, 4, 138, 211669182486426720302),
    (21555374498566658790375377, 11650471504470018995140633135, 4, 138, 211669182493660369206),
    (11650471504470018995140633136, 3403449890130522778806537552404091, 4, 138, 211671299588947447040),
    (3403449890130522778806537552404092, 92770138104229969497572137101952384169, 3, 136, 291004976865347193880),
    (92770138104229969497572137101952384170, 170141183460469231731687303715884105728, 1, 80, 423338364972826624001)]

set_option maxRecDepth 100000 in
theorem cover_pruned12_ok : checkCover 12 47000 cover_pruned12 = true := by decide +kernel

/-- **(b)** for `Lifetimes.pruned12` (subtree height 12, 47000 signatures). -/
theorem h0_bound_pruned12 [Params] (hb : subtreeHeight = 12) (hN : signatureLimit = 47000) (q' : ℕ)
    (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * creations Finset.univ landing (fun I => virtual Finset.univ
          ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹
          (ForsPotential.excess (HiddenDebt.baseline q')) signatureLimit I 0) q' [] +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  h0_bound_of_cover 12 47000 cover_pruned12 cover_pruned12_ok hb hN q' hq

/-- Certificate for `pruned10` (subtree height 10, 33 signatures). -/
def cover_pruned10 : List Entry := [
    (0, 2475880078570760549798248448, 4, 126, 594475150817230849),
    (2475880078570760549798248449, 85070591730234615865843651892301791232, 4, 130, 792633534417207297),
    (85070591730234615865843651892301791233, 170141183460469231731687303715884105728, 1, 80, 1188950301625810945)]

set_option maxRecDepth 100000 in
theorem cover_pruned10_ok : checkCover 10 33 cover_pruned10 = true := by decide +kernel

/-- **(b)** for `Lifetimes.pruned10` (subtree height 10, 33 signatures). -/
theorem h0_bound_pruned10 [Params] (hb : subtreeHeight = 10) (hN : signatureLimit = 33) (q' : ℕ)
    (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * creations Finset.univ landing (fun I => virtual Finset.univ
          ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹
          (ForsPotential.excess (HiddenDebt.baseline q')) signatureLimit I 0) q' [] +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  h0_bound_of_cover 10 33 cover_pruned10 cover_pruned10_ok hb hN q' hq

end LeanSphincs.Security.H0
