/-
The two light elliptic-torsion aliases: the `n²`-cardinality of the `n`-torsion of
an elliptic curve over an algebraically closed field, and its form at `K := F`.

Canonical sources: the pinned FLT `aa2d8b3` `Theorems/` wrappers

* `Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean`,
* `Theorems/Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean`

with their `S_` files `P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean`
and `P2M/Sol/S_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean`.  The
statements are transcribed verbatim from the wrappers, including the `⁄` notation
for the base change (`(W⁄K).Point`, which resolves to
`WeierstrassCurve.Affine.Point (W⁄K)`).  Only the proof bodies are adapted: each is
one line over the already-ported `FLTForHuman.Elliptic.card_torsion_of_isAlgClosed`
(`Elliptic/TorsionCard.lean`), which spells the base change `W.baseChange K` and is
definitionally the same term.

Assumes from lower modules: `FLTForHuman/Elliptic/TorsionCard.lean` (the count
`card_torsion_of_isAlgClosed`).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean>
-/
import FLTForHuman.Elliptic.TorsionCard

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

/-- The pin's `WeierstrassCurve.card_torsion_of_isAlgClosed_light`
(`Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean:9`), the
pinned `S_` file's one-line `solution`. -/
theorem card_torsion_of_isAlgClosed_light {F : Type*} {K : Type*} [Field F] [Field K]
    [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
  FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W hn

/-- The pin's `WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed`
(`Theorems/Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean:8`): the
same count at `K := F`.  This is the copy gateway 2 consumes. -/
theorem card_torsionBy_eq_sq_of_isAlgClosed {F : Type*} [Field F] [DecidableEq F]
    [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) = n ^ 2 :=
  card_torsion_of_isAlgClosed_light (F := F) (K := F) W hn

end WeierstrassCurve
