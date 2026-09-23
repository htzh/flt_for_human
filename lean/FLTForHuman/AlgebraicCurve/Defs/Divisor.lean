/-
Divisors, principal divisors and `Pic0`, after FLT's
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` lines 179–247
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean>).

The `Pic`/`torsion`/`AbelJacobiCard` block is deliberately not ported: it is API
for the modular Hecke/Galois-representation layer, not for the exchange cone
(`TOPIC-ac0-vocabulary.md` §2.2).
-/
import FLTForHuman.AlgebraicCurve.Defs.Place

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

end Pic0

end AlgebraicCurve
