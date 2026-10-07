/-
The conjugation invariance of the isogeny kernel: if an integral function-field
endomorphism `ι` of `E'` over `E` has cyclic point-map kernel, then so does the
endomorphism `ι'' : D'.FunctionField →ₐ[ℂ] D.FunctionField` obtained from `ι` by
conjugating with two `ℂ`-algebra equivalences `eE`, `eE'` — provided `ι''` is
conjugate to `ι` (`∀ x, eE (ι'' x) = ι (eE' x)`). The two kernels are transported by
the `ℂ`-algebra equivalence `eE.symm`, and the cardinalities agree because
`finrankAlong` is invariant under conjugation. This is set **D-4** of
`topics/velu/WORKORDER-P2-basechange.md`.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3`
`P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean`
(1,821 lines); the wrapper
`Theorems/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean`
is the statement authority for the headline. The `ModularCurve.KwD5BetweenCurves*`
seam vocabulary of that file is transcribed at its pin names, which is what the
statement checker keys on.

Everything else the pin's file carries is **imported, not re-proved** (measured by
`tools/deps/port_advise.py`: 50 of its 116 declarations already have an identical
statement in the port; the remaining prelude copies are binder-spelling variants of
ported declarations). In particular the point-pullback/tensor prelude is D-1's
(`Isogeny/BaseChange.lean`, at its prefix-stripped names), the `IsogenyEndDatum`
machinery is `IsogenyEndDatum/Engine.lean` and friends, and the `PeriodPair`
uniformization prelude is `Elliptic/PeriodPair/`.

`ModularCurve.KwD5BetweenCurvesHoloLift` is **not** declared here. The pin's `conj`
file does carry a copy of it, but that copy is byte-identical to the four other
copies (the silos', the S row's) and its body mentions `PeriodPair.kw_toPointHom`,
which the port does not have in any form (`grep -c` = 0); see the friction log and
`CARRY-FORWARD.md`. It therefore belongs to D-5
(`Isogeny/KernelBaseChange.lean`), which must promote `PeriodPair.kw_toPointHom`
first. Declaring it here as well would also make D-5's import of this module fail on
a duplicate name.

Import note (P-2 §3.1). `IsogenyEndDatum/Engine.lean` is importable here because
D-1 imports `GenusOnePlaceGate.lean`, not the producer
`GenusOnePlaceGateCentred.lean`; the latter pulls `Place/RRSpace.lean`, whose
`scoped instance instInfinitePlace` collides at the name level with `Engine`'s.
`Velu/RestrictAlong.lean`, which declares a second `normFormulaAlong_of_elliptic`,
is likewise not imported.

Only proof bodies are adapted to mathlib `v4.34.0`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean>
-/
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChange
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Vocabulary
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.PointEndSubring
import FLTForHuman.Elliptic.PeriodPair.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve
open WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate WeierstrassCurve

universe u

namespace ModularCurve

/-! ## The `KwD5BetweenCurvesPMOPConjKerEquiv` seam

`kw_fdn2_qephod_hend21_conjSeam eE eE' ι` is the conjugate of `ι` by the pair of
algebra equivalences `eE.symm` and `eE'`; the three lemmas below record that it stays
integral and finite, and that `finrankAlong` is invariant. They are the whole
`ConjHelpers` block of the pin. -/

section ConjHelpers

variable {K : Type u} [Field K]
variable {E E' F F' : Affine K}

/-- The `K`-algebra map `F'.FunctionField →ₐ[K] F.FunctionField` conjugate to
`ι : E'.FunctionField →ₐ[K] E.FunctionField` through `eE`/`eE'`. -/
def kw_fdn2_qephod_hend21_conjSeam
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    F'.FunctionField →ₐ[K] F.FunctionField :=
  (eE.symm.toAlgHom.comp ι).comp eE'.toAlgHom

theorem kw_fdn2_qephod_hend21_conjSeam_isIntegral
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) :
    (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans eE'.toAlgHom.toRingHom (eE.symm.toAlgHom.comp ι).toRingHom
    (RingHom.isIntegral_of_surjective _ eE'.surjective)
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (RingHom.isIntegral_of_surjective _ eE.symm.surjective))

theorem kw_fdn2_qephod_hend21_conjSeam_finiteAlong
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    FiniteAlong K (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) := by
  have hfin' : RingHom.Finite ι.toRingHom := hfin
  have h1 : RingHom.Finite eE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE'.surjective
  have h2 : RingHom.Finite eE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE.symm.surjective
  have hcomp : RingHom.Finite
      (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom :=
    RingHom.Finite.comp (g := (eE.symm.toAlgHom.comp ι).toRingHom)
      (RingHom.Finite.comp (g := eE.symm.toAlgHom.toRingHom) h2 hfin') h1
  exact hcomp

theorem kw_fdn2_qephod_hend21_finrankAlong_conj
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    finrankAlong K (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) = finrankAlong K ι := by
  refine @Algebra.finrank_eq_of_equiv_equiv F'.FunctionField F.FunctionField _ _
    (algebraAlong (kw_fdn2_qephod_hend21_conjSeam eE eE' ι))
    E'.FunctionField E.FunctionField _ _ (algebraAlong ι)
    eE'.toRingEquiv eE.toRingEquiv (RingHom.ext fun x => ?_)
  show ι (eE' x) = eE (eE.symm (ι (eE' x)))
  exact (eE.apply_symm_apply _).symm

end ConjHelpers

/-! ## The `KwD5BetweenCurvesPMOPConjKerEquiv` seam

The `Prop` the whole conjugation block proves: cyclicity of the kernel of
`pointMapOfPushforward ι` implies cyclicity of the kernel of the conjugated map,
uniformly over the two `PeriodPair` models `L`, `L'` of the curves `E`, `E'`. -/

/-- The conjugation seam: cyclicity of the kernel transfers to the conjugate
endomorphism. -/
def KwD5BetweenCurvesPMOPConjKerEquiv : Prop :=
  ∀ (E E' : Affine ℂ) [E.IsElliptic] [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (L L' : PeriodPair) [L.weierstrassCurve.IsElliptic] [GenusOnePlaceGate L.weierstrassCurve] [GenusOnePlaceGate.IsCentred L.weierstrassCurve] [AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [GenusOnePlaceGate L'.weierstrassCurve] [GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [AbelTheorem L'.weierstrassCurve]
    (eE : L.weierstrassCurve.toAffine.FunctionField ≃ₐ[ℂ] E.FunctionField)
    (eE' : L'.weierstrassCurve.toAffine.FunctionField ≃ₐ[ℂ] E'.FunctionField),
    let ι'' := kw_fdn2_qephod_hend21_conjSeam eE eE' ι
    ∀ (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward ι hι hfin
        (normFormulaAlong_of_elliptic ι hfin))) →
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward ι'' hι'' hfin''
        (normFormulaAlong_of_elliptic ι'' hfin'')))

/-! ## The `kw_surgehgf4_pck_*` engine

The four `pointMapOfPushforward` functoriality legs (composition, identity, the
algebra-equivalence inverse laws) and the `algEquiv` seam factor, which together
reduce the seam to an additive equivalence of the two point groups. -/

section AxiomAnchor

/-- The pin's axiom anchor: a proof that uses exactly `propext`, `Classical.choice`
and `Quot.sound`, so that `#print axioms` on the block's theorems reports the
standard three. -/
theorem kw_surgehgf4_pck_axiomAnchor : True := by
  have h1 : (True ∧ True) = True := propext (by simp)
  have h2 := Classical.choice ⟨()⟩
  have h3 := Quot.sound (r := fun _ _ : Unit => True) (a := ()) (b := ()) trivial
  trivial

end AxiomAnchor

section PMOPComp

variable {W₁ W₂ W₃ : Affine ℂ}
  [W₁.IsElliptic] [GenusOnePlaceGate W₁] [GenusOnePlaceGate.IsCentred W₁] [AbelTheorem W₁] [W₂.IsElliptic] [GenusOnePlaceGate W₂] [GenusOnePlaceGate.IsCentred W₂] [AbelTheorem W₂] [W₃.IsElliptic] [GenusOnePlaceGate W₃] [GenusOnePlaceGate.IsCentred W₃] [AbelTheorem W₃]

/-- `pointMapOfPushforward` is functorial in the function-field map. -/
theorem kw_surgehgf4_pck_pmop_comp_apply
    (φ : W₂.FunctionField →ₐ[ℂ] W₃.FunctionField)
    (χ : W₁.FunctionField →ₐ[ℂ] W₂.FunctionField)
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hφχ : (φ.comp χ).toRingHom.IsIntegral)
    (hfinφ : FiniteAlong ℂ φ) (hfinχ : FiniteAlong ℂ χ)
    (hfinφχ : FiniteAlong ℂ (φ.comp χ)) (P : W₃.Point) :
    pointMapOfPushforward (φ.comp χ) hφχ hfinφχ
        (normFormulaAlong_of_elliptic (φ.comp χ) hfinφχ) P
      = pointMapOfPushforward χ hχ hfinχ (normFormulaAlong_of_elliptic χ hfinχ)
          (pointMapOfPushforward φ hφ hfinφ (normFormulaAlong_of_elliptic φ hfinφ) P) := by
  have _ := kw_surgehgf4_pck_axiomAnchor

  show genusOnePic0Equiv W₁ (Pic0.pushforwardAlongHom (φ.comp χ) _ _ _
        ((genusOnePic0Equiv W₃).symm P))
    = genusOnePic0Equiv W₁ (Pic0.pushforwardAlongHom χ _ _ _
        ((genusOnePic0Equiv W₂).symm
          (genusOnePic0Equiv W₂ (Pic0.pushforwardAlongHom φ _ _ _
            ((genusOnePic0Equiv W₃).symm P)))))
  rw [AddEquiv.symm_apply_apply]
  exact congrArg (genusOnePic0Equiv W₁)
    (Pic0.pushforwardAlongHom_comp_apply χ φ hχ hφ hφχ hfinχ hfinφ hfinφχ
      (normFormulaAlong_of_elliptic χ hfinχ) (normFormulaAlong_of_elliptic φ hfinφ)
      (normFormulaAlong_of_elliptic (φ.comp χ) hfinφχ)
      ((genusOnePic0Equiv W₃).symm P))

end PMOPComp

section PMOPEquiv

variable {W V : Affine ℂ} [W.IsElliptic] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W] [V.IsElliptic] [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]

/-- `pointMapOfPushforward` of the identity is the identity. -/
theorem kw_surgehgf4_pck_pmop_id
    (hι : (AlgHom.id ℂ W.FunctionField).toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ (AlgHom.id ℂ W.FunctionField)) (P : W.Point) :
    pointMapOfPushforward (AlgHom.id ℂ W.FunctionField) hι hfin
        (normFormulaAlong_of_elliptic _ hfin) P = P := by
  have _ := kw_surgehgf4_pck_axiomAnchor

  have h := IsogenyEndDatum.idDatum_pointEnd W
  calc pointMapOfPushforward (AlgHom.id ℂ W.FunctionField) hι hfin
          (normFormulaAlong_of_elliptic _ hfin) P
      = (IsogenyEndDatum.idDatum W).pointEnd' P := rfl
    _ = P := by rw [h]; rfl

theorem kw_surgehgf4_pck_algEquiv_isIntegral
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) :
    e.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ e.surjective

theorem kw_surgehgf4_pck_algEquiv_finiteAlong
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) :
    FiniteAlong ℂ (e.toAlgHom (R := ℂ)) := by
  show @Module.Finite W.FunctionField V.FunctionField _ _ (algebraAlong e.toAlgHom).toModule
  letI := algebraAlong e.toAlgHom
  exact Module.Finite.of_surjective
    (Algebra.linearMap W.FunctionField V.FunctionField) e.surjective

/-- `pointMapOfPushforward` depends only on the map, not on its proof arguments. -/
theorem kw_surgehgf4_pck_pmop_congr
    {ι ι' : W.FunctionField →ₐ[ℂ] V.FunctionField} (h : ι = ι')
    {hι : ι.toRingHom.IsIntegral} {hfin : FiniteAlong ℂ ι}
    {hι' : ι'.toRingHom.IsIntegral} {hfin' : FiniteAlong ℂ ι'} (P : V.Point) :
    pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin) P
      = pointMapOfPushforward ι' hι' hfin' (normFormulaAlong_of_elliptic ι' hfin') P := by
  subst h; rfl

/-- The `algEquiv` pushforward is a left inverse to its `symm` twin. -/
theorem kw_surgehgf4_pck_pmop_equiv_left_inv
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) (P : W.Point) :
    pointMapOfPushforward e.toAlgHom
        (kw_surgehgf4_pck_algEquiv_isIntegral e)
        (kw_surgehgf4_pck_algEquiv_finiteAlong e)
        (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e))
        (pointMapOfPushforward e.symm.toAlgHom
          (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
          (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
          (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)) P)
      = P := by
  have heq : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id ℂ W.FunctionField :=
    AlgHom.ext fun x => e.symm_apply_apply x
  have hι'' : (e.symm.toAlgHom.comp e.toAlgHom).toRingHom.IsIntegral :=
    heq ▸ (IsogenyEndDatum.idDatum W).hι
  have hfin'' : FiniteAlong ℂ (e.symm.toAlgHom.comp e.toAlgHom) :=
    heq ▸ (IsogenyEndDatum.idDatum W).hfin
  have hcomp := kw_surgehgf4_pck_pmop_comp_apply e.symm.toAlgHom e.toAlgHom
    (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
    (kw_surgehgf4_pck_algEquiv_isIntegral e) hι''
    (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
    (kw_surgehgf4_pck_algEquiv_finiteAlong e) hfin'' P
  rw [← hcomp,
    kw_surgehgf4_pck_pmop_congr heq (hι' := (IsogenyEndDatum.idDatum W).hι)
      (hfin' := (IsogenyEndDatum.idDatum W).hfin) P]
  exact kw_surgehgf4_pck_pmop_id (IsogenyEndDatum.idDatum W).hι
    (IsogenyEndDatum.idDatum W).hfin P

/-- The `algEquiv` pushforward is a right inverse to its `symm` twin. -/
theorem kw_surgehgf4_pck_pmop_equiv_right_inv
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) (P : V.Point) :
    pointMapOfPushforward e.symm.toAlgHom
        (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
        (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
        (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm))
        (pointMapOfPushforward e.toAlgHom
          (kw_surgehgf4_pck_algEquiv_isIntegral e)
          (kw_surgehgf4_pck_algEquiv_finiteAlong e)
          (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e)) P)
      = P := by
  have h := kw_surgehgf4_pck_pmop_equiv_left_inv e.symm P
  rw [kw_surgehgf4_pck_pmop_congr
      (show e.symm.symm.toAlgHom = e.toAlgHom from congrArg _ e.symm_symm)] at h
  exact h

/-- The `algEquiv` pushforward is bijective. -/
theorem kw_surgehgf4_pck_pmop_equiv_bijective
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) :
    Function.Bijective (pointMapOfPushforward e.toAlgHom
        (kw_surgehgf4_pck_algEquiv_isIntegral e)
        (kw_surgehgf4_pck_algEquiv_finiteAlong e)
        (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e))) := by
  refine ⟨?_, ?_⟩
  · intro P Q hPQ
    have := congrArg (pointMapOfPushforward e.symm.toAlgHom
      (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
      (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
      (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm))) hPQ
    rwa [kw_surgehgf4_pck_pmop_equiv_right_inv,
      kw_surgehgf4_pck_pmop_equiv_right_inv] at this
  · intro Q
    exact ⟨pointMapOfPushforward e.symm.toAlgHom
      (kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
      (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
      (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)) Q,
      kw_surgehgf4_pck_pmop_equiv_left_inv e Q⟩

end PMOPEquiv

section ConjSeamFactor

variable {E E' F F' : Affine ℂ}
  [E.IsElliptic] [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E'] [F.IsElliptic] [GenusOnePlaceGate F] [GenusOnePlaceGate.IsCentred F] [AbelTheorem F] [F'.IsElliptic] [GenusOnePlaceGate F'] [GenusOnePlaceGate.IsCentred F'] [AbelTheorem F']
variable (eE : F.FunctionField ≃ₐ[ℂ] E.FunctionField)
  (eE' : F'.FunctionField ≃ₐ[ℂ] E'.FunctionField)
  (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField)
  (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)

/-- The seam factors through `eE` and `eE'`: the conjugated point map is
`eE'`-pushforward after `ι`-pushforward after the inverse `eE`-pushforward. -/
theorem kw_surgehgf4_pck_pmop_conjSeam_factor
    (hι'' : (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral)
    (hfin'' : FiniteAlong ℂ (kw_fdn2_qephod_hend21_conjSeam eE eE' ι))
    (P : F.Point) :
    pointMapOfPushforward (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
        (normFormulaAlong_of_elliptic _ hfin'') P
      = pointMapOfPushforward eE'.toAlgHom
          (kw_surgehgf4_pck_algEquiv_isIntegral eE')
          (kw_surgehgf4_pck_algEquiv_finiteAlong eE')
          (normFormulaAlong_of_elliptic _ (kw_surgehgf4_pck_algEquiv_finiteAlong eE'))
          (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin)
            (pointMapOfPushforward eE.symm.toAlgHom
              (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm)
              (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)
              (normFormulaAlong_of_elliptic _
                (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)) P)) := by

  have h1 := kw_surgehgf4_pck_pmop_comp_apply
    (eE.symm.toAlgHom.comp ι) eE'.toAlgHom
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm))
    (kw_surgehgf4_pck_algEquiv_isIntegral eE') hι''
    (finiteAlong_comp ι eE.symm.toAlgHom hfin
      (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm))
    (kw_surgehgf4_pck_algEquiv_finiteAlong eE') hfin'' P

  have h2 := kw_surgehgf4_pck_pmop_comp_apply eE.symm.toAlgHom ι
    (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm) hι
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm))
    (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm) hfin
    (finiteAlong_comp ι eE.symm.toAlgHom hfin
      (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)) P

  calc pointMapOfPushforward (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
          (normFormulaAlong_of_elliptic _ hfin'') P
      = pointMapOfPushforward eE'.toAlgHom _ _ _
          (pointMapOfPushforward (eE.symm.toAlgHom.comp ι) _ _ _ P) := h1
    _ = _ := congrArg _ h2

/-- The seam: cyclicity of the kernel transfers to the conjugate endomorphism. -/
theorem kw_surgehgf4_pck_proved_core
    (hι'' : (kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral)
    (hfin'' : FiniteAlong ℂ (kw_fdn2_qephod_hend21_conjSeam eE eE' ι)) :
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward ι hι hfin
        (normFormulaAlong_of_elliptic ι hfin))) →
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward
        (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
        (normFormulaAlong_of_elliptic _ hfin''))) := by
  have _ := kw_surgehgf4_pck_axiomAnchor
  intro hcyc
  have hAbij := kw_surgehgf4_pck_pmop_equiv_bijective eE.symm
  have hBinj := (kw_surgehgf4_pck_pmop_equiv_bijective eE').injective

  have hker_iff : ∀ x : F.Point,
      x ∈ AddMonoidHom.ker (pointMapOfPushforward
          (kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
          (normFormulaAlong_of_elliptic _ hfin''))
        ↔ pointMapOfPushforward eE.symm.toAlgHom
            (kw_surgehgf4_pck_algEquiv_isIntegral eE.symm)
            (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)
            (normFormulaAlong_of_elliptic _
              (kw_surgehgf4_pck_algEquiv_finiteAlong eE.symm)) x
          ∈ AddMonoidHom.ker (pointMapOfPushforward ι hι hfin
              (normFormulaAlong_of_elliptic ι hfin)) := by
    intro x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker,
      kw_surgehgf4_pck_pmop_conjSeam_factor eE eE' ι hι hfin hι'' hfin'' x]
    exact ⟨fun h => hBinj (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩

  obtain ⟨⟨g, hg⟩⟩ := hcyc
  obtain ⟨g', hg'⟩ := hAbij.surjective (g : E.Point)
  refine ⟨⟨⟨g', (hker_iff g').mpr (hg' ▸ g.2)⟩, ?_⟩⟩
  rintro ⟨y, hy⟩
  obtain ⟨k, hk⟩ := hg ⟨_, (hker_iff y).mp hy⟩
  refine ⟨k, Subtype.ext (hAbij.injective ?_)⟩
  have hk' := congrArg Subtype.val hk
  simp only [AddSubgroup.coe_zsmul] at hk'
  calc (pointMapOfPushforward eE.symm.toAlgHom _ _ _)
          ((k • (⟨g', _⟩ : AddMonoidHom.ker _) : AddMonoidHom.ker _) : F.Point)
      = (pointMapOfPushforward eE.symm.toAlgHom _ _ _) (k • g') := by
        rw [AddSubgroup.coe_zsmul]
    _ = k • (pointMapOfPushforward eE.symm.toAlgHom _ _ _) g' := map_zsmul _ k g'
    _ = k • (g : E.Point) := by rw [hg']
    _ = _ := hk'

end ConjSeamFactor

/-- The seam, packaged as the `Prop` `KwD5BetweenCurvesPMOPConjKerEquiv`. -/
theorem kw_surgehgf4_pck_proved : KwD5BetweenCurvesPMOPConjKerEquiv :=
  fun _ _ _ _ _ _ _ _ _ _ ι hι hfin _ _ _ _ _ _ _ _ _ _ eE eE' hι'' hfin'' =>
    kw_surgehgf4_pck_proved_core eE eE' ι hι hfin hι'' hfin''

end ModularCurve

/-- The pin's `pck_s17`, the seam at the pin's bare name. -/
theorem pck_s17 : ModularCurve.KwD5BetweenCurvesPMOPConjKerEquiv :=
  ModularCurve.kw_surgehgf4_pck_proved

/-! ## The conjugation headline

The statement is that of the pin's `Theorems/` wrapper; the pin's `S_` file proof
conjugates `ι''` into the seam and then splits cyclicity (the core above) from the
cardinality (`finrankAlong` invariance). -/

namespace WeierstrassCurve
namespace Affine

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

/-- **Conjugation invariance of the isogeny kernel.** If `ι''` is the conjugate of
`ι` by `eE`/`eE'` and `ι` has cyclic point-map kernel, then so does `ι''`, with the
same kernel cardinality. -/
theorem isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
    (E E' D D' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic] [D.IsElliptic] [D'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    [GenusOnePlaceGate D] [GenusOnePlaceGate.IsCentred D] [AbelTheorem D]
    [GenusOnePlaceGate D'] [GenusOnePlaceGate.IsCentred D'] [AbelTheorem D']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (hN : NormFormulaAlong ℂ ι hfin)
    (eE : D.FunctionField ≃ₐ[ℂ] E.FunctionField) (eE' : D'.FunctionField ≃ₐ[ℂ] E'.FunctionField)
    (ι'' : D'.FunctionField →ₐ[ℂ] D.FunctionField) (hconj : ∀ x, eE (ι'' x) = ι (eE' x))
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'') (hN'' : NormFormulaAlong ℂ ι'' hfin'')
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker) :
    IsAddCyclic (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker ∧
      Nat.card (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker = Nat.card (pointMapOfPushforward ι hι hfin hN).ker := by
  have hι''eq : ι'' = ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι := by
    apply AlgHom.ext
    intro x
    apply eE.injective
    rw [hconj x]
    show ι (eE' x) = eE (eE.symm (ι (eE' x)))
    exact (eE.apply_symm_apply _).symm
  subst hι''eq
  refine ⟨?_, ?_⟩
  · exact ModularCurve.kw_surgehgf4_pck_proved_core eE eE' ι hι hfin hι'' hfin'' hcyc
  · rw [natCard_ker_pointMapOfPushforward_eq_finrankAlong, natCard_ker_pointMapOfPushforward_eq_finrankAlong,
      ModularCurve.kw_fdn2_qephod_hend21_finrankAlong_conj]

end Affine
end WeierstrassCurve

end

#print axioms WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
