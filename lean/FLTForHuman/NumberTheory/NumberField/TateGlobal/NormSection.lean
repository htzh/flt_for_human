/-
  A continuous section of the idèle norm: `ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ`.

  `ideleNormU` is the multiplicative Haar character `distribHaarChar (AdeleRing (𝓞 F) F)`
  pushed into the unit group of `ℝ≥0`; at an archimedean place `w` the completion is `ℝ`
  (`IsReal w`) or `ℂ` (`IsComplex w`) up to a ring equivalence that is an isometry
  (`ringEquivRealOfIsReal`, `ringEquivComplexOfIsComplex`). Hence the maps
  `t ↦ e.symm t` (`realSectionOfIsReal`) and `r ↦ e.symm (√r : ℂ)`
  (`realSectionOfIsComplex` — the square root because `w.mult = 2` there) are continuous
  monoid homomorphisms `ℝ≥0ˣ →* (w.Completion)ˣ` whose norm to the power `w.mult` is `r`
  (`norm_localSection_pow_mult`). `localSection` is the `if hv : IsReal w` merge of the
  two, and `normSectionAt : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ` transports it through
  `archUnitHom w` into the idèles, with trivial finite part by construction;
  `ideleNorm_normSectionAt` computes `ideleNorm F (normSectionAt w r) = r` from
  `ideleNorm_archUnitHom` (`TateGlobal/ArchNorm.lean`). The headline
  `NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq` takes any place
  (`Classical.arbitrary (InfinitePlace F)` — a nonempty `F` always has one) and is proved
  in the listed façade `NumberField/TateGlobalNormSection.lean`.

  Transcribed from the pin's `section Fold_FujisakiC3c` / `section Fold_FujisakiC3e` of
  `P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean`,
  lines 728–901 (pinned `aa2d8b3`):
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean#L728-L901
  The pin re-proves this same block in nine sibling `S_` files, so it is homed here once,
  as the tier-3 engine the norm-section consumers import; it is *not* listed for the
  statement checker, and every public declaration carries a `-- pin:` marker naming its
  pin line (playbook §4.1, §5).

  The pin's `M4aLocalCFT.FujisakiC3` is chapter-prefix renamed to
  `NumberField.TateGlobal.FujisakiC3`, as every other `M4aLocalCFT.*` block of the T1 set;
  its `p2m_*` scaffolding is dropped, and so are its two `scoped instance`s
  (`LocallyCompactSpace (AdeleRing …)ˣ`, `instSecondCountableCompletion`), which are prelude
  for the silo's T1 half and not for these 25 lines — a `scoped instance` in an engine would
  alter instance search for every importer. The pin's own prelude (lines 1–727) is already in
  the port and is imported, never re-proved.

  `norm_ringEquivRealOfIsReal_symm` and `norm_ringEquivComplexOfIsComplex_symm` are *also*
  proved inline inside `TateGlobal/ArchNorm.lean`'s `exists_norm_pow_mult_eq`, and declared
  publicly under a different namespace in
  `AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean`; neither substitutes (the
  first is not a declaration, the second is downstream — importing `AutomorphicForm` from
  `NumberTheory/TateGlobal` inverts the tower), so they are re-proved here.

  Drift: no statement changed, three proofs adapted across two drifts — the comment at
  `continuous_archUnitHom_val` (the `def`-keyed `InfiniteAdeleRing` topology: `Continuous.update`
  needs its family `A` named) and the `dif_pos` / `dif_neg` → `dite_eq_left` / `dite_eq_right`
  rename of `v4.34.0` in `continuous_localSection` and `norm_localSection_pow_mult`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchNorm

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NNReal

noncomputable section

namespace NumberField
namespace TateGlobal
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

-- pin: continuous_archUnitHom_val (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:729)
open scoped Classical in
theorem continuous_archUnitHom_val (w : InfinitePlace F) :
    Continuous (fun a : (w.Completion)ˣ =>
      ((archUnitHom w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
  refine continuous_prodMk.mpr ⟨?_, continuous_const⟩
  show Continuous fun a : (w.Completion)ˣ =>
    Function.update (1 : (v : InfinitePlace F) → v.Completion) w (a : w.Completion)
  -- Adapted: `InfiniteAdeleRing F` is a plain `def`, so `continuous_const.update` cannot read
  -- the dependent family `A : InfinitePlace F → Type` off the folded head of the goal (it
  -- takes `A := fun _ => Pi` from `Units.continuous_val`'s monoid instead — the same defect the
  -- `continuous_normQ` landing recorded). Naming `A` — the Pi type the `show` above already
  -- spells out — restores the pin's one-token proof.
  exact Continuous.update (A := fun v : InfinitePlace F => v.Completion) continuous_const w
    Units.continuous_val

-- pin: continuous_archUnitHom (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:737)
theorem continuous_archUnitHom (w : InfinitePlace F) :
    Continuous (archUnitHom (F := F) w) := by
  classical
  refine Units.continuous_iff.mpr ⟨continuous_archUnitHom_val w, ?_⟩
  have key : (fun a : (w.Completion)ˣ => ↑(archUnitHom w a)⁻¹) =
      (fun a => ((archUnitHom w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
    funext a; rw [← map_inv]
  rw [key]
  exact (continuous_archUnitHom_val w).comp continuous_inv

variable (F) in
-- pin: ideleNormU (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:774)
def ideleNormU : (AdeleRing (𝓞 F) F)ˣ →* ℝ≥0ˣ :=
  (distribHaarChar (AdeleRing (𝓞 F) F)).toHomUnits

-- pin: val_ideleNormU (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:777)
theorem val_ideleNormU (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((ideleNormU F x : ℝ≥0ˣ) : ℝ≥0) = distribHaarChar (AdeleRing (𝓞 F) F) x := rfl

-- pin: coe_val_ideleNormU (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:780)
theorem coe_val_ideleNormU (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((ideleNormU F x : ℝ≥0ˣ) : ℝ≥0) : ℝ) = ideleNorm F x := rfl

-- pin: ideleNormU_eq_one_iff (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:783)
theorem ideleNormU_eq_one_iff (x : (AdeleRing (𝓞 F) F)ˣ) :
    ideleNormU F x = 1 ↔ x ∈ normOneIdeles F := by
  rw [← Units.val_eq_one, val_ideleNormU, normOneIdeles, MonoidHom.mem_ker]

-- pin: ideleNormU_of_mem (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:786)
theorem ideleNormU_of_mem {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ normOneIdeles F) :
    ideleNormU F x = 1 :=
  (ideleNormU_eq_one_iff x).mpr hx

section LocalSection

variable {w : InfinitePlace F}

-- pin: norm_ringEquivRealOfIsReal_symm (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:794)
omit [NumberField F] in
theorem norm_ringEquivRealOfIsReal_symm (hv : IsReal w) (t : ℝ) :
    ‖(ringEquivRealOfIsReal hv).symm t‖ = ‖t‖ := by
  have h := ArchMulHaarCompletion.nnnorm_ringEquivReal hv ((ringEquivRealOfIsReal hv).symm t)
  rw [RingEquiv.apply_symm_apply] at h
  simpa only [coe_nnnorm] using congrArg NNReal.toReal h.symm

-- pin: norm_ringEquivComplexOfIsComplex_symm (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:800)
omit [NumberField F] in
theorem norm_ringEquivComplexOfIsComplex_symm (hv : IsComplex w) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hv).symm z‖ = ‖z‖ := by
  have h := ArchMulHaarCompletion.nnnorm_ringEquivComplex hv ((ringEquivComplexOfIsComplex hv).symm z)
  rw [RingEquiv.apply_symm_apply] at h
  simpa only [coe_nnnorm] using congrArg NNReal.toReal h.symm

-- pin: continuous_ringEquivRealOfIsReal_symm (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:807)
omit [NumberField F] in
theorem continuous_ringEquivRealOfIsReal_symm (hv : IsReal w) :
    Continuous (ringEquivRealOfIsReal hv).symm :=
  (isometryEquivRealOfIsReal hv).symm.continuous

-- pin: continuous_ringEquivComplexOfIsComplex_symm (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:811)
omit [NumberField F] in
theorem continuous_ringEquivComplexOfIsComplex_symm (hv : IsComplex w) :
    Continuous (ringEquivComplexOfIsComplex hv).symm :=
  (isometryEquivComplexOfIsComplex hv).symm.continuous

-- pin: realSectionOfIsReal (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:815)
def realSectionOfIsReal (hv : IsReal w) : ℝ≥0ˣ →* (w.Completion)ˣ :=
  (Units.map (ringEquivRealOfIsReal hv).symm.toRingHom.toMonoidHom).comp
    (Units.map NNReal.toRealHom.toMonoidHom)

-- pin: realSectionOfIsComplex (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:818)
def realSectionOfIsComplex (hv : IsComplex w) : ℝ≥0ˣ →* (w.Completion)ˣ :=
  (Units.map (ringEquivComplexOfIsComplex hv).symm.toRingHom.toMonoidHom).comp <|
    (Units.map Complex.ofRealHom.toMonoidHom).comp <|
      (Units.map NNReal.toRealHom.toMonoidHom).comp (Units.map NNReal.sqrtHom.toMonoidHom)

-- pin: val_realSectionOfIsReal (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:824)
omit [NumberField F] in
theorem val_realSectionOfIsReal (hv : IsReal w) (r : ℝ≥0ˣ) :
    ((realSectionOfIsReal hv r : (w.Completion)ˣ) : w.Completion) =
      (ringEquivRealOfIsReal hv).symm ((r : ℝ≥0) : ℝ) := rfl

-- pin: val_realSectionOfIsComplex (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:829)
omit [NumberField F] in
theorem val_realSectionOfIsComplex (hv : IsComplex w) (r : ℝ≥0ˣ) :
    ((realSectionOfIsComplex hv r : (w.Completion)ˣ) : w.Completion) =
      (ringEquivComplexOfIsComplex hv).symm (((NNReal.sqrt (r : ℝ≥0) : ℝ≥0) : ℝ) : ℂ) := rfl

-- pin: continuous_realSectionOfIsReal (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:834)
omit [NumberField F] in
theorem continuous_realSectionOfIsReal (hv : IsReal w) : Continuous (realSectionOfIsReal hv) :=
  (Continuous.units_map _ (continuous_ringEquivRealOfIsReal_symm hv)).comp
    (Continuous.units_map _ NNReal.continuous_coe)

-- pin: continuous_realSectionOfIsComplex (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:839)
omit [NumberField F] in
theorem continuous_realSectionOfIsComplex (hv : IsComplex w) :
    Continuous (realSectionOfIsComplex hv) :=
  (Continuous.units_map _ (continuous_ringEquivComplexOfIsComplex_symm hv)).comp <|
    (Continuous.units_map _ Complex.continuous_ofReal).comp <|
      (Continuous.units_map _ NNReal.continuous_coe).comp
        (Continuous.units_map _ NNReal.continuous_sqrt)

variable (w)

-- pin: localSection (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:847)
open scoped Classical in
def localSection : ℝ≥0ˣ →* (w.Completion)ˣ :=
  if hv : IsReal w then realSectionOfIsReal hv
  else realSectionOfIsComplex (not_isReal_iff_isComplex.mp hv)

-- pin: continuous_localSection (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:851)
omit [NumberField F] in
theorem continuous_localSection : Continuous (localSection w) := by
  by_cases hv : IsReal w
  · rw [localSection, dite_eq_left hv]; exact continuous_realSectionOfIsReal hv
  · rw [localSection, dite_eq_right hv]; exact continuous_realSectionOfIsComplex _

-- pin: norm_localSection_pow_mult (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:857)
omit [NumberField F] in
theorem norm_localSection_pow_mult (r : ℝ≥0ˣ) :
    ‖((localSection w r : (w.Completion)ˣ) : w.Completion)‖ ^ w.mult = ((r : ℝ≥0) : ℝ) := by
  by_cases hv : IsReal w
  · rw [localSection, dite_eq_left hv, val_realSectionOfIsReal, norm_ringEquivRealOfIsReal_symm,
      mult_isReal ⟨w, hv⟩, pow_one, NNReal.norm_eq]
  · rw [localSection, dite_eq_right hv, val_realSectionOfIsComplex, norm_ringEquivComplexOfIsComplex_symm,
      mult_isComplex ⟨w, not_isReal_iff_isComplex.mp hv⟩, Complex.norm_real, NNReal.norm_eq,
      ← NNReal.coe_pow, NNReal.sq_sqrt]

-- pin: normSectionAt (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:866)
def normSectionAt : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (archUnitHom w).comp (localSection w)

-- pin: normSectionAt_apply (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:869)
theorem normSectionAt_apply (r : ℝ≥0ˣ) :
    normSectionAt w r = archUnitHom w (localSection w r) := rfl

-- pin: continuous_normSectionAt (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:871)
theorem continuous_normSectionAt : Continuous (normSectionAt (F := F) w) :=
  (continuous_archUnitHom w).comp (continuous_localSection w)

-- pin: ideleNorm_normSectionAt (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:874)
theorem ideleNorm_normSectionAt (r : ℝ≥0ˣ) :
    ideleNorm F (normSectionAt w r) = ((r : ℝ≥0) : ℝ) := by
  rw [normSectionAt_apply, ideleNorm_archUnitHom, norm_localSection_pow_mult]

-- pin: ideleNormU_normSectionAt (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:877)
theorem ideleNormU_normSectionAt (r : ℝ≥0ˣ) : ideleNormU F (normSectionAt w r) = r :=
  Units.ext (NNReal.coe_injective (ideleNorm_normSectionAt w r))

end LocalSection

end FujisakiC3
end TateGlobal
end NumberField

end
