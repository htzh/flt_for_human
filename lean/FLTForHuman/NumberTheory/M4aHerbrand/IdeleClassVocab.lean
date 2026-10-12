/-
  The idèle class group and Galois descent data.

  `principalIdeles R F` is the diagonal image of `Fˣ` in `(𝔸_F)ˣ` and
  `IdeleClassGroup R F = (𝔸_F)ˣ ⧸ principalIdeles` is the idèle class group. An
  `IdeleGaloisDescent R E F` is a continuous action of `Gal(F/E)` on `𝔸_F`
  compatible with the action on `F`; `unitsAct` lifts it to the unit group,
  `map_principalIdeles` shows the principal idèles are stable, `classAct` descends it
  to the class group, and `ideleClassNorm`/`ideleClassDerive` are the norm
  (product over the Galois group) and the derivation `c ↦ σ·c · c⁻¹` on the class
  group. `identityDescent` is the inhabitant in the trivial-Galois-group case.

  Transcribed verbatim from `Definitions/Def_M4aHerbrand_IdeleClassVocab.lean`
  (pinned `aa2d8b3`, 114 lines / 9 declarations). The idèle class group is a
  number-theoretic carrier, so its home is the port's `NumberTheory/M4aHerbrand/`
  area (the pin's `Def_M4aHerbrand_*` family, playbook §3.1); the pin namespace
  `M4aHerbrand` is kept.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing

set_option autoImplicit false

-- The pin's `letI` walls in the Galois product feed instance search (the `Fintype`
-- for `F ≃ₐ[E] F`); kept verbatim.
set_option linter.style.haveILetI false

open NumberField

namespace M4aHerbrand

noncomputable section

section Carrier

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

def principalIdeles : Subgroup (AdeleRing R F)ˣ :=
  (Units.map (algebraMap F (AdeleRing R F) : F →* AdeleRing R F)).range

abbrev IdeleClassGroup := (AdeleRing R F)ˣ ⧸ principalIdeles R F

end Carrier

section Descent

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

structure IdeleGaloisDescent where

  act : (F ≃ₐ[E] F) →* RingAut (AdeleRing R F)

  compat : ∀ (g : F ≃ₐ[E] F) (x : F),
    act g (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) (g x)

  continuous_act : ∀ g : F ≃ₐ[E] F, Continuous (act g)

namespace IdeleGaloisDescent

variable {R E F}

def unitsAct (D : IdeleGaloisDescent R E F) : (F ≃ₐ[E] F) →* MulAut (AdeleRing R F)ˣ where
  toFun g := Units.mapEquiv (D.act g).toMulEquiv
  map_one' := by refine MulEquiv.ext fun u => Units.ext ?_; simp only [map_one]; rfl
  map_mul' g₁ g₂ := by refine MulEquiv.ext fun u => Units.ext ?_; simp only [map_mul]; rfl

theorem map_principalIdeles (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) :
    (principalIdeles R F).map (D.unitsAct g).toMonoidHom = principalIdeles R F := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨Units.map (g : F →* F) u, Units.ext (D.compat g u).symm⟩
  · intro x hx
    have hmem : D.unitsAct g⁻¹ x ∈ principalIdeles R F := by
      rcases hx with ⟨u, rfl⟩
      exact ⟨Units.map ((g⁻¹ : F ≃ₐ[E] F) : F →* F) u, Units.ext (D.compat g⁻¹ u).symm⟩
    refine ⟨D.unitsAct g⁻¹ x, hmem, ?_⟩
    show D.unitsAct g (D.unitsAct g⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

def classAct (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) :
    IdeleClassGroup R F →* IdeleClassGroup R F :=
  (QuotientGroup.congr (principalIdeles R F) (principalIdeles R F)
    (D.unitsAct g) (D.map_principalIdeles g)).toMonoidHom

end IdeleGaloisDescent

end Descent

section NormDerive

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

def ideleClassNorm [Finite (F ≃ₐ[E] F)] (D : IdeleGaloisDescent R E F) :
    IdeleClassGroup R F →* IdeleClassGroup R F where
  toFun c :=
    letI := Fintype.ofFinite (F ≃ₐ[E] F)
    ∏ τ : F ≃ₐ[E] F, D.classAct τ c
  map_one' := by simp
  map_mul' x y := by
    letI := Fintype.ofFinite (F ≃ₐ[E] F)
    simp only [map_mul]; exact Finset.prod_mul_distrib

set_option maxSynthPendingDepth 3 in

def ideleClassDerive (D : IdeleGaloisDescent R E F) (σ : F ≃ₐ[E] F) :
    IdeleClassGroup R F →* IdeleClassGroup R F where
  toFun c := D.classAct σ c * c⁻¹
  map_one' := by simp
  map_mul' x y := by
    show D.classAct σ (x * y) * (x * y)⁻¹ = D.classAct σ x * x⁻¹ * (D.classAct σ y * y⁻¹)
    rw [map_mul, mul_inv_rev, mul_comm y⁻¹ x⁻¹]
    exact mul_mul_mul_comm _ _ _ _

end NormDerive

section Inhabitant

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

def identityDescent [Subsingleton (F ≃ₐ[E] F)] : IdeleGaloisDescent R E F where
  act := 1
  compat g x := by
    have hg : g = 1 := Subsingleton.elim g 1
    subst hg; rfl
  continuous_act g := by
    have hg : g = 1 := Subsingleton.elim g 1
    subst hg; simp only [map_one]; exact continuous_id

end Inhabitant

end

end M4aHerbrand
