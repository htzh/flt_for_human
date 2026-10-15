/-
  Number-field supplement: complex embeddings of a field extension and extensions of
  infinite places.

  Backported from the pin's `Definitions/Def_NumberField_Extension.lean` (pinned `aa2d8b3`).
  It supplies `NumberField.ComplexEmbedding.IsExtension`/`IsMixedExtension`/`IsUnmixedExtension`
  (a complex embedding `g` of `L` lying above `f` of `K`, and the mixed/unmixed dichotomy)
  with `isExtensionEquivSum`, and `NumberField.InfinitePlace.Extension`/`RamifiedExtension`/
  `UnramifiedExtension` with `IsLift`/`IsConjugateLift` and their API.

  Substitutions against mathlib `v4.34.0`: none — mathlib's `NumberField.ComplexEmbedding`
  and `NumberField.InfinitePlace` do not carry any of these declarations, so all 35 are
  transcribed at the pin's names.  The only proof change is that `convert` now closes the
  `inr` branch of `Extension.isExtension_or_isExtension_conjugate` outright, so the pin's
  trailing `rfl` (pin line 120) is dropped.
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

set_option autoImplicit false

section

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)

-- pin: IsExtension (Definitions/Def_NumberField_Extension.lean:12)
abbrev IsExtension := g.comp (algebraMap K L) = f

variable {f g} in
-- pin: IsExtension.not_isExtension_conjugate (Definitions/Def_NumberField_Extension.lean:15)
theorem IsExtension.not_isExtension_conjugate (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬IsExtension f (conjugate g) := by
  simp_all [RingHom.ext_iff, ComplexEmbedding.isReal_iff]

variable {f g} in
-- pin: IsExtension.ne (Definitions/Def_NumberField_Extension.lean:21)
theorem IsExtension.ne {r : L →+* ℂ} (hg : IsExtension f g) (hr : ¬IsExtension f r) :
    g ≠ r := by
  simp_all only [← hg, RingHom.ext_iff, RingHom.coe_comp, Function.comp_apply, not_forall,
    ne_eq]
  let ⟨x, hx⟩ := hr
  exact ⟨algebraMap K L x, by aesop⟩

-- pin: IsMixedExtension (Definitions/Def_NumberField_Extension.lean:28)
abbrev IsMixedExtension :=
  IsExtension f g ∧ ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g

-- pin: not_isReal_of_not_isReal (Definitions/Def_NumberField_Extension.lean:31)
theorem not_isReal_of_not_isReal {f : K →+* ℂ} {g : L →+* ℂ} (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬ComplexEmbedding.IsReal g :=
  mt (IsReal.comp _) (h ▸ hf)

namespace IsMixedExtension

-- pin: IsMixedExtension.isExtension (Definitions/Def_NumberField_Extension.lean:38)
theorem isExtension (h : IsMixedExtension f g) :
    IsExtension f g := h.1

-- pin: IsMixedExtension.isReal (Definitions/Def_NumberField_Extension.lean:41)
theorem isReal (h : IsMixedExtension f g) :
    ComplexEmbedding.IsReal f := h.2.1

-- pin: IsMixedExtension.not_isReal (Definitions/Def_NumberField_Extension.lean:44)
theorem not_isReal (h : IsMixedExtension f g) :
    ¬ComplexEmbedding.IsReal g := h.2.2

end IsMixedExtension

-- pin: IsUnmixedExtension (Definitions/Def_NumberField_Extension.lean:49)
abbrev IsUnmixedExtension := IsExtension f g ∧ ¬IsMixedExtension f g

variable {f g} in
-- pin: IsUnmixedExtension.isReal_of_isReal (Definitions/Def_NumberField_Extension.lean:52)
theorem IsUnmixedExtension.isReal_of_isReal (h : IsUnmixedExtension f g)
    (hf : ComplexEmbedding.IsReal f) :
    ComplexEmbedding.IsReal g := by
  simp only [IsUnmixedExtension, not_and, not_not] at h
  exact h.2 h.1 hf

open scoped Classical in

-- pin: isExtensionEquivSum (Definitions/Def_NumberField_Extension.lean:60)
def isExtensionEquivSum (f : K →+* ℂ) :
    { g : L →+* ℂ // IsExtension f g } ≃
      { g : L →+* ℂ // IsMixedExtension f g } ⊕ { g : L →+* ℂ // IsUnmixedExtension f g } :=
  (Equiv.sumCompl
    (fun g => ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g.1)).symm.trans <|
    Equiv.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun g => _ ∧ ¬ComplexEmbedding.IsReal g))
      ((Equiv.subtypeSubtypeEquivSubtypeInter _
        (fun g => ¬(_ ∧ ¬ComplexEmbedding.IsReal g))).trans
        (Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by aesop)))

end NumberField.ComplexEmbedding

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

variable [Algebra K L]

variable (L) in

-- pin: Extension (Definitions/Def_NumberField_Extension.lean:83)
abbrev Extension (v : InfinitePlace K) := { w : InfinitePlace L // w.comap (algebraMap K L) = v }

variable (K) in

-- pin: toExtension (Definitions/Def_NumberField_Extension.lean:87)
abbrev toExtension : (w.comap (algebraMap K L)).Extension L := ⟨w, rfl⟩

-- pin: coe_toExtension (Definitions/Def_NumberField_Extension.lean:89)
theorem coe_toExtension (w : InfinitePlace L) : (toExtension K w).1 = w := rfl

namespace Extension

variable {v : InfinitePlace K} (w : v.Extension L)

-- pin: Extension.isComplex_of_isComplex (Definitions/Def_NumberField_Extension.lean:95)
theorem isComplex_of_isComplex (hv : v.IsComplex) :
    w.1.IsComplex := by
  rw [isComplex_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff, not_forall] at hv ⊢
  let ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← w.2, ← mk_embedding w.1, comap_mk] at hx
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl => simp_all
  | inr hr => aesop

-- pin: Extension.isReal_base (Definitions/Def_NumberField_Extension.lean:105)
theorem isReal_base (hw : w.1.IsReal) :
    v.IsReal := by
  simp_all only [← not_isComplex_iff_isReal]
  exact mt w.isComplex_of_isComplex hw

-- pin: Extension.mk_embedding (Definitions/Def_NumberField_Extension.lean:110)
theorem mk_embedding : mk (w.1.embedding.comp (algebraMap K L)) = v := by
  rw [← comap_mk, w.1.mk_embedding, w.2]

-- pin: Extension.isExtension_or_isExtension_conjugate (Definitions/Def_NumberField_Extension.lean:113)
theorem isExtension_or_isExtension_conjugate :
    IsExtension v.embedding w.1.embedding ∨ IsExtension v.embedding (conjugate w.1.embedding) := by
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl =>
    convert Or.inl <| hl ▸ congrArg InfinitePlace.embedding w.mk_embedding
  | inr hr =>
    convert Or.inr <| hr ▸ congrArg InfinitePlace.embedding w.mk_embedding

-- pin: Extension.isExtension_conjugate_of_not_isExtension (Definitions/Def_NumberField_Extension.lean:122)
theorem isExtension_conjugate_of_not_isExtension (h : ¬IsExtension v.embedding w.1.embedding) :
    IsExtension v.embedding (conjugate w.1.embedding) :=
  w.isExtension_or_isExtension_conjugate.resolve_left h

variable (L)

variable (v : InfinitePlace K) (w : v.Extension L)

-- pin: Extension.IsLift (Definitions/Def_NumberField_Extension.lean:130)
class IsLift where
  isExtension' : IsExtension v.embedding w.1.embedding

-- pin: Extension.IsLift.isExtension (Definitions/Def_NumberField_Extension.lean:133)
theorem IsLift.isExtension [w.IsLift L v] : IsExtension v.embedding w.1.embedding :=
  IsLift.isExtension'

-- pin: Extension.IsConjugateLift (Definitions/Def_NumberField_Extension.lean:136)
class IsConjugateLift where
  isExtension' : IsExtension v.embedding (conjugate w.1.embedding)

-- pin: Extension.IsConjugateLift.isExtension (Definitions/Def_NumberField_Extension.lean:139)
theorem IsConjugateLift.isExtension [w.IsConjugateLift L v] :
    IsExtension v.embedding (conjugate w.1.embedding) := IsConjugateLift.isExtension'

-- pin: Extension.isLift_or_isConjugateLift (Definitions/Def_NumberField_Extension.lean:142)
theorem isLift_or_isConjugateLift (v : InfinitePlace K) (w : v.Extension L) :
    w.IsLift L v ∨ w.IsConjugateLift L v := by
  cases isExtension_or_isExtension_conjugate w with
  | inl hl => exact Or.inl ⟨hl⟩
  | inr hr => exact Or.inr ⟨hr⟩

end Extension

variable (L)

-- pin: RamifiedExtension (Definitions/Def_NumberField_Extension.lean:152)
abbrev RamifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }

-- pin: UnramifiedExtension (Definitions/Def_NumberField_Extension.lean:155)
abbrev UnramifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }

variable {L v}

-- pin: Extension.toRamifiedExtension (Definitions/Def_NumberField_Extension.lean:160)
def Extension.toRamifiedExtension {w : v.Extension L} (h : w.1.IsRamified K) :
    v.RamifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

-- pin: Extension.toUnramifiedExtension (Definitions/Def_NumberField_Extension.lean:163)
def Extension.toUnramifiedExtension {w : v.Extension L} (h : w.1.IsUnramified K) :
    v.UnramifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

namespace RamifiedExtension

-- pin: RamifiedExtension.comap_eq (Definitions/Def_NumberField_Extension.lean:168)
theorem comap_eq (w : v.RamifiedExtension L) : w.1.comap (algebraMap K L) = v := w.2.1

-- pin: RamifiedExtension.isRamified (Definitions/Def_NumberField_Extension.lean:170)
theorem isRamified (w : v.RamifiedExtension L) : w.1.IsRamified K := w.2.2

-- pin: RamifiedExtension.isReal_comap (Definitions/Def_NumberField_Extension.lean:172)
theorem isReal_comap (w : v.RamifiedExtension L) : (w.1.comap (algebraMap K L)).IsReal :=
  (isRamified_iff.1 w.isRamified).2

instance : Coe (v.RamifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.2.1⟩

-- pin: RamifiedExtension.isReal (Definitions/Def_NumberField_Extension.lean:178)
theorem isReal (w : v.RamifiedExtension L) : v.IsReal :=
  w.comap_eq ▸ w.isReal_comap

-- pin: RamifiedExtension.isComplex (Definitions/Def_NumberField_Extension.lean:181)
theorem isComplex (w : v.RamifiedExtension L) :
    (w.1 : InfinitePlace L).IsComplex :=
  (isRamified_iff.1 w.isRamified).1

end RamifiedExtension

namespace UnramifiedExtension

-- pin: UnramifiedExtension.comap_eq (Definitions/Def_NumberField_Extension.lean:189)
theorem comap_eq (w : UnramifiedExtension L v) : w.1.comap (algebraMap K L) = v := w.2.1

-- pin: UnramifiedExtension.isUnramified (Definitions/Def_NumberField_Extension.lean:191)
theorem isUnramified (w : UnramifiedExtension L v) : w.1.IsUnramified K := w.2.2

instance : Coe (v.UnramifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.comap_eq⟩

end UnramifiedExtension

end NumberField.InfinitePlace

end

end
