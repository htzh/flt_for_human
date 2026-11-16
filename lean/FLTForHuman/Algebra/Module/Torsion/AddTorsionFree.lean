/-
  Additive torsion-freeness of a vector space over a characteristic-zero field.

  `IsAddTorsionFree M` is the additive-group form of `Module.IsTorsionFree ℤ M`: no nonzero
  `n : ℕ` kills an element (`n • a = n • b → a = b`). The mathematics is one line — over a field
  of characteristic zero, `a = (n : ℂ)⁻¹ • (n • a)` — and is entirely generic in the carrier: the
  only hypothesis is the `ℂ`-module structure.

  Why it is stated here rather than found by instance search. Mathlib has the `ℚ` form
  (`IsAddTorsionFree.of_module_rat`) and the bridge into the `ℤ` form
  (`IsAddTorsionFree M → IsTorsionFree ℤ M`, `Mathlib/Algebra/Module/Torsion/Free.lean`), but
  neither closes the `ℂ` case: `Module ℚ M` is not an instance for a `ℂ`-module (the `ℚ`-structure
  would be a restriction of scalars), and the one-step pullback that would do it,
  `Module.IsTorsionFree.comap` at `algebraMap ℤ ℂ`, is a lemma rather than an instance.

  The consumers are the lattice-freeness proofs of the Hecke layer
  (`ModularForms/HeckeFiniteness/Lattice.lean`, `…/Finiteness.lean`): each needs the
  ambient cusp-form space torsion-free as a `ℤ`-module to pass
  `Module.free_of_finite_type_torsion_free'` — a finitely generated torsion-free module over the
  PID `ℤ` is free — and so to conclude that the integral lattice is a free `ℤ`-module, hence that
  its endomorphism ring is a finitely generated `ℤ`-module.

  Assumes: mathlib `v4.34.0` only. The statement is the port's, not the pin's, so the module
  carries no `spec-pin:` wire.
-/
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false

/-- A `ℂ`-vector space has no additive torsion: `n • a = n • b` with `n ≠ 0` forces `a = b`.

The `ℤ`-multiple of a `ℂ`-scalar action is the `ℂ`-scalar action of the cast integer
(`Nat.cast_smul_eq_nsmul`), and a nonzero `ℂ`-scalar acts injectively on a `ℂ`-module. -/
theorem IsAddTorsionFree.of_module_complex (V : Type*) [AddCommGroup V] [Module ℂ V] :
    IsAddTorsionFree V := by
  refine ⟨fun n hn a b hab ↦ ?_⟩
  have h : (n : ℂ) • a = (n : ℂ) • b := by
    simpa only [Nat.cast_smul_eq_nsmul] using hab
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
