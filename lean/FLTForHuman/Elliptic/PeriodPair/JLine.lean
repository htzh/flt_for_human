/-
  The `PeriodPair` `j`-line: the `j`-invariant of `ofTau τ` and its surjectivity.

  `PeriodPair.jLattice = 1728 g₂³ / (g₂³ − 27 g₃²)` is the `j`-invariant of the
  Weierstrass curve attached to a lattice, and `PeriodPair.JSurjective` says every
  complex number is realised by some lattice.  The two pin nodes are

  * `PeriodPair.jLattice_ofTau`      (`(ofTau τ).jLattice = E₄ τ ^ 3 / Δ τ`), and
  * `PeriodPair.jLattice_surjective` (`PeriodPair.JSurjective`).

  Statements are transcribed verbatim from the `Theorems/` wrappers, pinned
  `anthropics/fermats-last-theorem@aa2d8b3`:

  * <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_jLattice_ofTau.lean>
    (proof from `P2M/Sol/S_PeriodPair_jLattice_ofTau.lean`),
  * <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_jLattice_surjective.lean>
    (proof from `P2M/Sol/S_PeriodPair_jLattice_surjective.lean`).

  Dedup note (playbook §2.4, §5).  The pin's `S_` file for `jLattice_surjective`
  proves `j`-surjectivity itself, by the `E₄³ − c·Δ` pencil argument
  (`kwQepw115c_jH_surjective` and its ~45-declaration `kwQepw*` scaffolding).  The
  port already has that theorem as the third conjunct of the landed
  `WLight.levelOne_hauptmodul_package`, exported generically as
  `ModularForm.j_surjective` (`FLTForHuman/ModularForms/JInvariant.lean`).  The
  pin's pencil block is therefore **not re-proved**; `jLattice_surjective` is three
  lines from it.  Likewise the pin's `kw_discriminant_ofTau_eq` / `kw_g₂_ofTau` /
  `kw_g₃_ofTau` are the landed `ofTau_discriminant_eq` / `g₂_ofTau` / `g₃_ofTau`
  (`Elliptic/PeriodPair/Discriminant.lean`), and its `kw_E4cube*` q-expansion block
  is mathlib's `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`.

  Assumes `FLTForHuman.Elliptic.PeriodPair.Discriminant` (the `ofTau` invariants and
  the discriminant headline) and `FLTForHuman.ModularForms.JInvariant` (the generic
  level-one `j`-surjectivity).  This module is the bridge between the lattice theory
  and the level-one modular-forms theory; it is a leaf, so importing upward is a
  diamond, not a cycle.
-/
import FLTForHuman.Elliptic.PeriodPair.Discriminant
import FLTForHuman.ModularForms.JInvariant

open scoped UpperHalfPlane
open ModularForm

noncomputable section

namespace PeriodPair

open UpperHalfPlane

/-- The pin's `kw_discriminant_ofTau_eq`: `g₂³ − 27 g₃²` of `ofTau τ` in terms of
`E₄³ − E₆²`.  (A `have` here rather than a promoted lemma: `Discriminant.lean` keeps
the same identity `private` as `ofTau_discriminant_eq`, and the j-line is its only
other consumer.) -/
private theorem ofTau_discriminant_eq (τ : ℍ) :
    (ofTau τ).g₂ ^ 3 - 27 * (ofTau τ).g₃ ^ 2
      = (64 * (Real.pi : ℂ) ^ 12 / 27)
        * (ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2) := by
  rw [g₂_ofTau, g₃_ofTau]
  ring

/-- The pin's `kw_jLattice_ofTau_eq`: `jLattice` of `ofTau τ` in the
`1728 g₂³ / (g₂³ − 27 g₃²)` spelling, from the landed `g₂_ofTau` / `g₃_ofTau`. -/
theorem jLattice_ofTau_eq (τ : ℍ) :
    (ofTau τ).jLattice = 1728 * E₄ τ ^ 3 / (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  have hK : (64 * (Real.pi : ℂ) ^ 12 / 27) ≠ 0 :=
    div_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 12 (by exact_mod_cast Real.pi_ne_zero)))
      (by norm_num)
  unfold jLattice
  rw [ofTau_discriminant_eq, g₂_ofTau, mul_pow,
    show (4 * (Real.pi : ℂ) ^ 4 / 3) ^ 3 = 64 * (Real.pi : ℂ) ^ 12 / 27 by ring,
    show (1728 : ℂ) * (64 * (Real.pi : ℂ) ^ 12 / 27 * ModularForm.E₄ τ ^ 3)
        = 64 * (Real.pi : ℂ) ^ 12 / 27 * (1728 * ModularForm.E₄ τ ^ 3) by ring,
    mul_div_mul_left _ _ hK]

/-- `PeriodPair.jLattice_ofTau`.  Statement verbatim from
`Theorems/Thm_PeriodPair_jLattice_ofTau.lean`; the RHS is `ModularForm.j τ`. -/
theorem jLattice_ofTau (τ : ℍ) :
    (PeriodPair.ofTau τ).jLattice = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  rw [jLattice_ofTau_eq, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, div_div_eq_mul_div]
  ring

/-- `PeriodPair.jLattice_surjective`.  Statement verbatim from
`Theorems/Thm_PeriodPair_jLattice_surjective.lean`: every complex number is the
`j`-invariant of a lattice. -/
theorem jLattice_surjective : PeriodPair.JSurjective := by
  intro c
  obtain ⟨τ, hτ⟩ := ModularForm.j_surjective c
  exact ⟨ofTau τ, discriminant_ne_zero (ofTau τ), by rw [jLattice_ofTau]; exact hτ⟩

end PeriodPair
