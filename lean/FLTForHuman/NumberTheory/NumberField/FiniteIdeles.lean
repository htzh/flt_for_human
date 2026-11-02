/-
  The unit idèles: the finite adèles that are integral at every finite place, together with
  their inverses.

  `unitIdeles R K` is the subgroup of `(FiniteAdeleRing R K)ˣ` whose every `v`-component and
  every `v`-component of the inverse lies in `v.adicCompletionIntegers K`; it is the finite
  half of the idèle group's "nowhere negative" part, and `mem_unitIdeles_iff` is the two
  conjuncts the norm estimates rewrite with.

  `finitePartUnits R K` is the projection of an idèle onto its finite part — the monoid
  homomorphism whose codomain is `(FiniteAdeleRing R K)ˣ`, hence the map whose fibres
  `unitIdeles` describes.

  Transcribed from the pin's `Definitions/Def_IsDedekindDomain_FiniteUnitIdeles.lean`
  (pinned `aa2d8b3`, the whole 30-line module: `unitIdeles` and `mem_unitIdeles_iff`) and
  the one declaration `finitePartUnits` of `Definitions/Def_NumberField_IdeleBox.lean`
  (`:96`), at the pin's names and namespaces. The pin's `import Mathlib` is replaced by the
  two specific modules this file uses; the pin's `val_finitePartUnits` is not carried (no
  consumer on the shelf names it).

  spec-pin: Definitions/Def_IsDedekindDomain_FiniteUnitIdeles.lean
  spec-pin: Definitions/Def_NumberField_IdeleBox.lean
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.AdicValuation

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

def unitIdeles : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {δ | (∀ v : HeightOneSpectrum R, (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) ∧
    ∀ v : HeightOneSpectrum R, ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' := ⟨fun v => by rw [Units.val_one]; exact one_mem _,
              fun v => by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun v => by rw [Units.val_mul]; exact mul_mem (hx1 v) (hy1 v),
           fun v => by rw [mul_inv, Units.val_mul]; exact mul_mem (hx2 v) (hy2 v)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, fun v => by rw [inv_inv]; exact hx1 v⟩

variable {R K} in
theorem mem_unitIdeles_iff (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdeles R K ↔
      (∀ v : HeightOneSpectrum R, (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v : HeightOneSpectrum R,
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

noncomputable def finitePartUnits : (AdeleRing R K)ˣ →* (IsDedekindDomain.FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom

end NumberField.AdeleRing
