/-
  Layer 0b — the fibre of a bivariate polynomial at a value, and the mod-`ℓ` reduction of
  its coefficients.

  `fibrePoly Φ a` evaluates `Φ`'s first variable at `a`; `reduceModBivar ℓ` reduces a
  bivariate integer polynomial's coefficients mod `ℓ`. They are the definition layer of the
  `N = 2` fibre row of the Deligne–Serre column's ready shelf, whose statement is
  `fibrePoly phiTwo W.j = ∏ i, (X - C (j (W/⟨P i⟩)))`
  (`topics/modularCurve/WORKORDER-B1-phi-rows.md` §1 and `WORKORDER-B2`).

  `fibrePoly` was already in the port, but `private`, inside
  `ModularCurve/Degree/PhiData.lean`; the pin exposes it publicly and 68 pin files use it, so
  it is defined here at the pin's name and `PhiData` imports it instead of keeping a copy
  (the dedup of playbook §4(c)). `reduceModBivar` is the whole `ReduceModBivar` section of the
  pin's `Def_ModularCurve_KroneckerTransport.lean`; no other part of that module has a consumer
  on this cone.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_FibrePoly.lean` (53 lines) and
  `Definitions/Def_ModularCurve_KroneckerTransport.lean` lines 113–127, statements and bodies
  verbatim.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_FibrePoly.lean
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Perfect

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ReduceModBivar

/-- Reduction of a bivariate integer polynomial's coefficients mod `ℓ`. -/
def reduceModBivar (ℓ : ℕ) :
    Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial (ZMod ℓ)) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ)))

@[simp] theorem reduceModBivar_X (ℓ : ℕ) :
    reduceModBivar ℓ Polynomial.X = Polynomial.X := by
  simp [reduceModBivar, Polynomial.coe_mapRingHom]

@[simp] theorem reduceModBivar_C_X (ℓ : ℕ) :
    reduceModBivar ℓ (Polynomial.C Polynomial.X) = Polynomial.C Polynomial.X := by
  simp [reduceModBivar, Polynomial.coe_mapRingHom]

end ReduceModBivar

section FibrePoly

variable {k : Type*} [Field k]

/-- The fibre of `Φ` at `a`: its first variable evaluated at `a`. -/
def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : k) : Polynomial k :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) a)

variable {ℓ : ℕ} [CharP k ℓ]

theorem eval₂RingHom_intCast_eq_comp (a : k) :
    Polynomial.eval₂RingHom (Int.castRingHom k) a =
      (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

theorem fibrePoly_eq_map_reduceModBivar (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    fibrePoly Φ a =
      (reduceModBivar ℓ Φ).map
        (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a) := by
  rw [fibrePoly, eval₂RingHom_intCast_eq_comp (ℓ := ℓ),
    show reduceModBivar ℓ Φ
      = Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) from rfl,
    Polynomial.map_map]

end FibrePoly

section Factorization

variable {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]

theorem C_sub_X_pow_eq_neg_pow (a : k) :
    Polynomial.C a - Polynomial.X ^ ℓ =
      -((Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ) := by
  have hpoly : (Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ =
      Polynomial.X ^ ℓ - Polynomial.C ((frobeniusEquiv k ℓ).symm a) ^ ℓ :=
    sub_pow_char _ _
  rw [hpoly, ← Polynomial.C_pow, frobeniusEquiv_symm_pow_p, neg_sub]

end Factorization

end ModularCurve

end
