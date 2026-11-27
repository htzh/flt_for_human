/-
The height-one spectrum's norm sum converges past `σ = 1`.

`NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt`: for a number field `F` and
`σ > 1`, `∑_{v} |N v.asIdeal|^{-σ}` is summable over the height-one spectrum of `𝓞 F`. It is the
convergence half of the Euler-product estimate — the leaf the zeta module consumes (41 project
citers), and the one place the ideal-counting and the prime-norm-summation meet.

Home `NumberTheory/NumberField/`, beside `PrimeNormSums.lean` and `CompletedDedekindZeta/`.

## The rows

* `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` — 69 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.lean>

spec-pin: Theorems/Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.lean
spec-pin: P2M/Sol/S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.lean

## Port notes (order AF107F)

* **Substitution — the order's suspect twin, and it is the same statement.** The port already
  proves this at `NumberField.TateGlobal.summable_absNorm_rpow_neg`
  (`FLTForHuman/NumberTheory/NumberField/TateGlobal/PlaceSum.lean:121`):
  `Summable fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)` for
  `1 < σ`. The pin's statement spells the same cast `((Ideal.absNorm v.asIdeal : ℕ) : ℝ)`, so
  the two are the same term. A second copy of the statement lives at
  `AutomorphicForm.LocalIntertwining.FiniteAdeleAssembly.summable_absNorm_rpow_neg`. So this
  module **imports** the port's copy and the row is one line; the pin's 58-line p-series proof is
  not re-proved. `port_advise` cannot see this pair (it matches the pin's names), so the order's
  "already in the port" number undercounts by these 58 lines.
  Consequence for the manager: `NumberTheory/NumberField/HeightOneSpectrumSummable` now sits
  above `NumberField/TateGlobal` in the import order (the `NumberTheory` name is the subject, the
  `TateGlobal` module is where the proof lives). No cycle: nothing outside `tmp/` imported this
  module.
* **Surface = the pin's.** 1 declaration, 1 public / 0 private, against the pin's 2 entries
  (`Theorems/Thm_…` + `S_…`'s `solution`: the same statement twice). 2 − 1 = 1.
* **`check_port`**: 1 ok, 0 mismatch, 0 missing, 0 own, 0 kw.
* **Axioms**: subset of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe (recorded, never installed)**: passes the whole downward ladder —
  40000 / 20000 / 10000 / 5000 / **1000** all pass; module floor passes at 1000 as well.
-/

import FLTForHuman.NumberTheory.NumberField.TateGlobal.PlaceSum
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open NumberField IsDedekindDomain

set_option autoImplicit false

theorem NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  NumberField.TateGlobal.summable_absNorm_rpow_neg hσ
