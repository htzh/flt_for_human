/-
Divisors, principal divisors and `Pic0`, after FLT's
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` lines 179–247
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean>).

`Pic0.torsion` and `Pic0.mem_torsion` are ported (pin lines 244–247): the
`SemilinearAut` action on the torsion of `Pic0`, and the `ZMod n`-module and
`torsionRep` built on it, are stated over them.  The pin's `AbelJacobiCard`
statement (line 252) is not ported — it is the statement of the unported Abel–Jacobi
card node, not a definition this module owns.  `Pic` (the pin's line 221) is a general
curve object and lives here beside `Pic0`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean

spec-pin: Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_degree_eq_sum.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.Place
import Mathlib.Algebra.Group.AddChar

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

abbrev Divisor : Type _ := Place K F →₀ ℤ

namespace Divisor

variable {K F}

def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  simp [degree]

/-- The degree of a divisor as the finite sum `∑ v ∈ D.support, D v * deg v`.
Verbatim from `Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_sum.lean`; the pin's
proof is the unfolding of the `Finsupp.liftAddHom` that defines `degree`. -/
theorem degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
  Finsupp.liftAddHom_apply (fun v : Place K F => AddMonoidHom.mulRight (v.deg : ℤ)) D

def degZero : AddSubgroup (Divisor K F) := degree.ker

theorem mem_degZero {D : Divisor K F} : D ∈ degZero (K := K) (F := F) ↔ degree D = 0 :=
  Iff.rfl

def IsPrincipal (D : Divisor K F) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

theorem mem_principal {D : Divisor K F} :
    D ∈ principal (K := K) (F := F) ↔ IsPrincipal D := Iff.rfl

end Divisor

class HasPrincipalDivisors : Prop where
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

abbrev Pic0 : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))

namespace Pic0

variable {K F}

def mk (D : Divisor.degZero (K := K) (F := F)) : Pic0 K F := QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

@[simp]
theorem mk_add (D E : Divisor.degZero (K := K) (F := F)) : mk (D + E) = mk D + mk E := rfl

@[simp]
theorem mk_zero : mk (0 : Divisor.degZero (K := K) (F := F)) = 0 := rfl

variable (K F) in

/-- Pin `Pic0.torsion` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:244`):
the `n`-torsion subgroup of `Pic0`, the kernel of multiplication by `n`. -/
def torsion (n : ℕ) : AddSubgroup (Pic0 K F) :=
  (Submodule.torsionBy ℤ (Pic0 K F) (n : ℤ)).toAddSubgroup

/-- Pin `Pic0.mem_torsion` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:247`). -/
theorem mem_torsion {n : ℕ} {x : Pic0 K F} : x ∈ torsion K F n ↔ (n : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

end Pic0

abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)

/-- Pin `HomPic0Gm` (`Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean:119`):
the `K`-valued additive characters of the `n`-torsion of `Pic0` — the target of the
Weil pairing's hom. -/
abbrev HomPic0Gm (n : ℕ) : Type _ := AddChar (Pic0.torsion K F n) K

end AlgebraicCurve
