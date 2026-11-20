/-
  SET-AF90C consumer: discrete principal idèles and compact adele quotient.

  **The rows.** `FLTForHuman/NumberTheory/NumberField/IntegralAdeles.lean` carries
  `AdeleRing.compactSpace_quotient_principalSubgroup` (the quotient `𝔸_F ⧸ F` is compact) and
  `AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton` (an open neighbourhood of `1` in the
  idèle group meeting the principal idèles only at `1`).

  **The reading.** The two halves of the adelic discreteness/cocompactness pair, read as one
  statement: the quotient is compact and the principal idèles are discrete. This is the shape in
  which the Fujisaki/Hecke arguments take the pair — compactness of the quotient for the
  fundamental-domain estimates, discreteness of `Fˣ` for the product formula's unit lattice.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF90CConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.NumberField.IntegralAdeles

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain

namespace NumberFieldSetAF90CConsumer

/-- **The reading.** `𝔸_F ⧸ F` is compact, and the principal idèles are discrete in the idèles. -/
theorem compact_quotient_and_discrete_principalIdeles
    (F : Type) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ∧
      ∃ V : Set (AdeleRing (𝓞 F) F)ˣ, IsOpen V ∧
        V ∩ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ) = {1} :=
  ⟨AdeleRing.compactSpace_quotient_principalSubgroup F,
   AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton F⟩

end NumberFieldSetAF90CConsumer
