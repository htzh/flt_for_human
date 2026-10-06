/-
  Cross-module wire test for P-SET-1 and P-SET-2 (the `PeriodPair` uniformization
  core and the `j`-line).

  A `spec/` probe, not a library module.  It imports the new modules
  (`Basic.lean`, `Discriminant.lean`, `Uniformization.lean`, `JLine.lean`,
  `ModularForms/JInvariant.lean`) and each zone is a real, executed composition;
  deleting any one module makes this file fail (the concrete pair `L` needs `Basic`,
  `L_discriminantNeZero` needs `Discriminant`, zone 3 needs `Uniformization`, and
  zone 4 needs `JLine` and `JInvariant`).

  Zones (no `#check`, no `sorry`):

  * zone 1 — the dictionary at the concrete lattice `(I, 1)` (`UpperHalfPlane.I`):
    `weierstrassCurve_a₄` through the `simp` set, `jLattice` through
    `jLattice_eq_c₄_pow_three_div_Δ`, and the index/quotient vocabulary at `L = L`
    (`sublatticeIndex` is `1`; the `sublatticeQuotient` is trivial);
  * zone 2 — `PeriodPair.discriminant_ne_zero` at `(I, 1)`, fed through
    `DiscriminantNeZero.weierstrassCurve_Δ_ne_zero`;
  * zone 3 — `PeriodPair.isUniformization_toPoint` with `h` discharged from
    `discriminant_ne_zero`: the additivity conjunct gives a concrete `toPoint`
    identity, the surjectivity conjunct gives a preimage of `0`, and the kernel
    conjunct is exercised non-vacuously at `z = 0`;
  * zone 4 (P-SET-2, the `j`-line) — `PeriodPair.jLattice_ofTau` at `(I, 1)` feeding
    the neutral `ModularForm.j`, the pin's `jLattice_ofTau_eq` spelling,
    `PeriodPair.jLattice_surjective` at a concrete value, and
    `ModularForm.j_surjective` directly.  Deleting `JLine.lean` breaks the first
    three, deleting `ModularForms/JInvariant.lean` breaks the fourth and the first.
-/
import FLTForHuman.Elliptic.PeriodPair.Basic
import FLTForHuman.Elliptic.PeriodPair.Discriminant
import FLTForHuman.Elliptic.PeriodPair.Uniformization
import FLTForHuman.Elliptic.PeriodPair.JLine
import FLTForHuman.ModularForms.JInvariant

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open scoped PeriodPair UpperHalfPlane

namespace PeriodPairConsumer

open PeriodPair

/-- The concrete period pair `(I, 1)` on the upper half plane. -/
noncomputable def L : PeriodPair := PeriodPair.ofTau UpperHalfPlane.I

/-- The discriminant of `L` is nonzero, through the new headline. -/
theorem L_discriminantNeZero : L.DiscriminantNeZero := PeriodPair.discriminant_ne_zero L

-- Zone 1: the dictionary at `(I, 1)`.

example : L.weierstrassCurve.a₄ = -L.g₂ / 4 := by
  simp only [PeriodPair.weierstrassCurve_a₄]

example : L.jLattice = L.weierstrassCurve.c₄ ^ 3 / L.weierstrassCurve.Δ :=
  PeriodPair.jLattice_eq_c₄_pow_three_div_Δ L

example : PeriodPair.sublatticeIndex L L = 1 := by
  rw [PeriodPair.sublatticeIndex, AddSubgroup.addSubgroupOf_self, AddSubgroup.index_top]

example : Subsingleton (L.sublatticeQuotient L) := by
  have h : Subsingleton (L.lattice.toAddSubgroup ⧸
      L.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup) := by
    rw [AddSubgroup.addSubgroupOf_self]
    simp
  exact h

-- Zone 2: the discriminant headline feeds the curve's `Δ ≠ 0`.

example : L.weierstrassCurve.Δ ≠ 0 :=
  L_discriminantNeZero.weierstrassCurve_Δ_ne_zero

-- Zone 3: the uniformization headline, `h` discharged from the discriminant theorem.

example : L.IsUniformization L_discriminantNeZero :=
  PeriodPair.isUniformization_toPoint L L_discriminantNeZero

example (z w : ℂ) :
    L.toPoint L_discriminantNeZero (z + w)
      = L.toPoint L_discriminantNeZero z + L.toPoint L_discriminantNeZero w :=
  (PeriodPair.isUniformization_toPoint L L_discriminantNeZero).1 z w

example (z : ℂ) :
    L.toPoint L_discriminantNeZero (z + 0) = L.toPoint L_discriminantNeZero z := by
  rw [(PeriodPair.isUniformization_toPoint L L_discriminantNeZero).1 z 0,
    PeriodPair.toPoint_zero L L_discriminantNeZero, add_zero]

example : ∃ z : ℂ, L.toPoint L_discriminantNeZero z = 0 :=
  (PeriodPair.isUniformization_toPoint L L_discriminantNeZero).2.1 0

example : (0 : ℂ) ∈ L.lattice :=
  (PeriodPair.isUniformization_toPoint L L_discriminantNeZero).2.2 0
    (PeriodPair.toPoint_zero L L_discriminantNeZero)

-- Zone 4: the `j`-line (`JLine.lean` and the neutral `ModularForm.j_surjective`).

example : L.jLattice = ModularForm.j UpperHalfPlane.I :=
  PeriodPair.jLattice_ofTau UpperHalfPlane.I

example : L.jLattice = 1728 * ModularForm.E₄ UpperHalfPlane.I ^ 3
      / (ModularForm.E₄ UpperHalfPlane.I ^ 3 - ModularForm.E₆ UpperHalfPlane.I ^ 2) :=
  PeriodPair.jLattice_ofTau_eq UpperHalfPlane.I

/-- `jLattice_surjective` non-vacuously: `0` is a `j`-invariant. -/
example : ∃ L' : PeriodPair, L'.DiscriminantNeZero ∧ L'.jLattice = 0 :=
  PeriodPair.jLattice_surjective 0

/-- The generic `j`-surjectivity, from `ModularForms/JInvariant.lean`. -/
example : ∃ τ : ℍ, ModularForm.j τ = (1728 : ℂ) :=
  ModularForm.j_surjective 1728

#print axioms PeriodPair.jLattice_ofTau
#print axioms PeriodPair.jLattice_surjective

#print axioms PeriodPair.discriminant_ne_zero
#print axioms PeriodPair.isUniformization_toPoint

end PeriodPairConsumer

end
