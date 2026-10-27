import LeanFors.CoverBound.MomentTable

/-! **No half-cover moment.** The forest FTS needed a second per-tree moment for half-covered
codewords. FORS needs none: a tree is covered or it is not (`CoverBound/NearMoment`), so the near
bound of `CoverBound/NearOption` reads the first moment table alone (`CoverBound/MomentTable`).
This module is left without content and can be dropped with its import in `LeanFors.lean`. -/
