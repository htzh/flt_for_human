/-
  The adelic Tate/zeta vocabulary.

  For a number field `F`: `normOneIdeles` is the kernel of the idele norm,
  `ideleNorm x = |x|` the norm of an idele (the real-valued `distribHaarChar`),
  `zetaIntegral ν f χ s = ∫ f(x) · χ(x) · |x|^s ∂ν` the global zeta integral,
  `localChar χ v` and `archLocalChar χ w` the finite and archimedean components of a
  Hecke character, `IsUnramifiedCharAt χ v` its triviality on the local units,
  `integralOutside S` the set of adèles integral outside `S`, and
  `IsFactorizableStandardOutside f S g h` the factorizable test functions (an
  archimedean factor, factors on `S`, and the integral indicator outside `S`) that
  the Euler-factor identity unfolds.

  Transcribed whole from `Definitions/Def_NumberField_TateGlobalZeta.lean` (pinned
  `aa2d8b3`). This is the theory's own vocabulary module and the natural base of the
  `NumberField.TateGlobal` development: it owns the namespace the three consumed
  headlines use, and the later development modules import it rather than each
  re-stating it (playbook §2.3, §3.1, §5).
-/
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.NumberTheory.AdelicVolume
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume
open AutomorphicForm IsDedekindDomain
open scoped NNReal

noncomputable section

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

-- pin: normOneIdeles (Def_NumberField_TateGlobalZeta.lean:16)
def normOneIdeles : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (distribHaarChar (AdeleRing (𝓞 F) F)).ker

-- pin: ideleNorm (Def_NumberField_TateGlobalZeta.lean:19)
def ideleNorm (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ((distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ≥0) : ℝ)

variable {F}

-- pin: ideleNorm_pos (Def_NumberField_TateGlobalZeta.lean:24)
theorem ideleNorm_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < ideleNorm F x :=
  NNReal.coe_pos.mpr (distribHaarChar_pos)

-- pin: zetaIntegral (Def_NumberField_TateGlobalZeta.lean:27)
def zetaIntegral {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (f : AdeleRing (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν

-- pin: localChar (Def_NumberField_TateGlobalZeta.lean:31)
def localChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℂˣ :=
  χ.comp ((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v))

-- pin: archUnitHom (Def_NumberField_TateGlobalZeta.lean:35)
-- Adapted: mathlib's `InfiniteAdeleRing F` is a `def`, not a reducible `abbrev`, so the
-- pin's `(1 : InfiniteAdeleRing F)` in `Function.update` is spelled as the Pi type here.
def archUnitHom (w : InfinitePlace F) : (w.Completion)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun := archCentralUnit F w
  map_one' := by
    classical
    refine Units.ext (Prod.ext (funext fun v => ?_) rfl)
    show Function.update (1 : (w : InfinitePlace F) → w.Completion) w
        ((1 : (w : InfinitePlace F) → w.Completion) w) v
      = (1 : (w : InfinitePlace F) → w.Completion) v
    rw [Function.update_eq_self]
  map_mul' a b := by
    classical
    refine Units.ext (Prod.ext (funext fun v => ?_) (one_mul 1).symm)
    show Function.update (1 : (w : InfinitePlace F) → w.Completion) w
        (((a * b : (w.Completion)ˣ)) : w.Completion) v
      = Function.update (1 : (w : InfinitePlace F) → w.Completion) w (a : w.Completion) v
          * Function.update (1 : (w : InfinitePlace F) → w.Completion) w (b : w.Completion) v
    by_cases hv : v = w
    · subst hv
      simp [Function.update_self]
    · rw [Function.update_of_ne hv, Function.update_of_ne hv, Function.update_of_ne hv]
      exact (mul_one _).symm

-- pin: archLocalChar (Def_NumberField_TateGlobalZeta.lean:55)
def archLocalChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) :
    (w.Completion)ˣ →* ℂˣ :=
  χ.comp (archUnitHom w)

-- pin: IsUnramifiedCharAt (Def_NumberField_TateGlobalZeta.lean:59)
def IsUnramifiedCharAt (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ t : (v.adicCompletion F)ˣ, (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      localChar χ v t = 1

-- pin: integralOutside (Def_NumberField_TateGlobalZeta.lean:64)
def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (AdeleRing (𝓞 F) F) :=
  {x | ∀ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

-- pin: IsFactorizableStandardOutside (Def_NumberField_TateGlobalZeta.lean:67)
def IsFactorizableStandardOutside (f : AdeleRing (𝓞 F) F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : (w : InfinitePlace F) → w.Completion → ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) : Prop :=
  ∀ x, f x = (integralOutside S).indicator
      (fun x => (∏ w, g w (x.1 w)) * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

-- pin: ideleNorm_mul (Def_NumberField_TateGlobalZeta.lean:73)
theorem ideleNorm_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F (x * y) = ideleNorm F x * ideleNorm F y := by
  simp [ideleNorm, map_mul]

-- pin: mem_normOneIdeles_iff (Def_NumberField_TateGlobalZeta.lean:76)
theorem mem_normOneIdeles_iff (x : (AdeleRing (𝓞 F) F)ˣ) : x ∈ normOneIdeles F ↔ ideleNorm F x = 1 := by
  simp [normOneIdeles, ideleNorm, MonoidHom.mem_ker]

-- pin: localChar_apply (Def_NumberField_TateGlobalZeta.lean:79)
theorem localChar_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ) :
    localChar χ v t = χ (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t)) := rfl

-- pin: archUnitHom_apply (Def_NumberField_TateGlobalZeta.lean:83)
theorem archUnitHom_apply (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archUnitHom w a = archCentralUnit F w a := rfl

-- pin: archLocalChar_apply (Def_NumberField_TateGlobalZeta.lean:86)
theorem archLocalChar_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archLocalChar χ w a = χ (archCentralUnit F w a) := rfl

end NumberField.TateGlobal

end
