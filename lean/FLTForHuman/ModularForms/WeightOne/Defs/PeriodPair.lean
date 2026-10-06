/-
  The standard period pair `(τ, 1)` and the period-lattice vocabulary —
  root-level re-exports of `FLTForHuman/Elliptic/PeriodPair/Lattice.lean`.

  The mathematics lives once, at the pin's `PeriodPair.*` names, in
  `Elliptic/PeriodPair/Lattice.lean` (`periodPairOfTau`, `smulPeriodPair`,
  `smulLatticeEquiv`, `mem_smulPeriodPair_lattice`,
  `weierstrassP_smulPeriodPair`, `periodPair_eq_of_ω`, …).  This module keeps the
  root-level spellings the weight-one packages already import, via `export` (so
  the root names *are* the home's declarations, not copies), and every use site
  compiles untouched.

  Direction: `WeightOne → Elliptic/PeriodPair`.  Nothing under
  `ModularForms/WeightOne/` is imported here.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_frickeFunction_modularity_package.lean
-/
import FLTForHuman.Elliptic.PeriodPair.Lattice

export PeriodPair (periodPairOfTau periodPairOfTau_ω₁ periodPairOfTau_ω₂
  smulPeriodPair smulPeriodPair_ω₁ smulPeriodPair_ω₂ mem_smulPeriodPair_lattice
  smulLatticeEquiv smulLatticeEquiv_coe weierstrassP_smulPeriodPair periodPair_eq_of_ω)
