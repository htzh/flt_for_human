/-
  Tate's local zeta function.

  For a locally compact topological field `K` with Haar measure `μ`: `modulus` is
  the modulus `|·|`, the distribution-valued Haar character `distribHaarChar`
  extended by `0` at zero; `charExt χ` extends a multiplicative character of `Kˣ`
  by zero; and the local zeta integral is

    `localZeta μ f χ s = ∫ f(x) · χ(x) · |x|^s ∂(mulMeasure μ)`,

  integration against the multiplicative Haar measure `mulMeasure μ`. `tateFourier`
  is the additive Fourier transform and `localGammaAt` the local gamma factor.

  Transcribed whole from `Definitions/Def_LanglandsTunnell_TateLocalZeta.lean`
  (pinned `aa2d8b3`). The pin node imports only mathlib, so this file is its
  natural home: the adelic zeta layer's local half, kept beside nothing adelic
  (playbook §2.3, §3.1).
-/
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LanglandsTunnell.TateLocal

section Modulus

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

-- pin: modulus (Def_LanglandsTunnell_TateLocalZeta.lean:15)
def modulus (a : K) : ℝ≥0 := by
  classical exact if h : a = 0 then 0 else distribHaarChar K (Units.mk0 a h)

-- pin: modulus_zero (Def_LanglandsTunnell_TateLocalZeta.lean:18)
@[simp] theorem modulus_zero : modulus (0 : K) = 0 := by
  simp [modulus]

-- pin: modulus_of_ne_zero (Def_LanglandsTunnell_TateLocalZeta.lean:21)
theorem modulus_of_ne_zero {a : K} (h : a ≠ 0) : modulus a = distribHaarChar K (Units.mk0 a h) := by
  simp [modulus, h]

-- pin: modulus_coe_units (Def_LanglandsTunnell_TateLocalZeta.lean:24)
@[simp] theorem modulus_coe_units (u : Kˣ) : modulus (u : K) = distribHaarChar K u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

-- pin: modulus_pos (Def_LanglandsTunnell_TateLocalZeta.lean:27)
theorem modulus_pos {a : K} (h : a ≠ 0) : 0 < modulus a := by
  rw [modulus_of_ne_zero h]
  exact distribHaarChar_pos

-- pin: modulus_ne_zero (Def_LanglandsTunnell_TateLocalZeta.lean:31)
theorem modulus_ne_zero {a : K} (h : a ≠ 0) : modulus a ≠ 0 :=
  (modulus_pos h).ne'

-- pin: modulus_one (Def_LanglandsTunnell_TateLocalZeta.lean:34)
@[simp] theorem modulus_one : modulus (1 : K) = 1 := by
  rw [modulus_of_ne_zero one_ne_zero, Units.mk0_one, map_one]

-- pin: modulus_mul (Def_LanglandsTunnell_TateLocalZeta.lean:37)
theorem modulus_mul (a b : K) : modulus (a * b) = modulus a * modulus b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [modulus_of_ne_zero (mul_ne_zero ha hb), modulus_of_ne_zero ha, modulus_of_ne_zero hb,
    ← map_mul]
  congr 1
  exact Units.ext rfl

end Modulus

section TestFunctions

variable {K : Type*} [TopologicalSpace K]

-- pin: IsSchwartzBruhat (Def_LanglandsTunnell_TateLocalZeta.lean:53)
def IsSchwartzBruhat (f : K → ℂ) : Prop :=
  IsLocallyConstant f ∧ HasCompactSupport f

-- pin: IsSchwartzBruhat.zero (Def_LanglandsTunnell_TateLocalZeta.lean:56)
theorem IsSchwartzBruhat.zero : IsSchwartzBruhat (0 : K → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

-- pin: IsSchwartzBruhat.indicator_const (Def_LanglandsTunnell_TateLocalZeta.lean:59)
theorem IsSchwartzBruhat.indicator_const {U : Set K} (hU : IsClopen U) (hUc : IsCompact U)
    (c : ℂ) : IsSchwartzBruhat (U.indicator fun _ => c) := by
  refine ⟨?_, ?_⟩
  · intro s
    classical
    have : (U.indicator fun _ => c) ⁻¹' s =
        (if c ∈ s then U else ∅) ∪ (if (0 : ℂ) ∈ s then Uᶜ else ∅) := by
      ext x
      by_cases hx : x ∈ U <;> by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
        simp [Set.indicator, hx, hc, h0]
    rw [this]
    refine IsOpen.union ?_ ?_
    · split_ifs
      · exact hU.isOpen
      · exact isOpen_empty
    · split_ifs
      · exact hU.compl.isOpen
      · exact isOpen_empty
  · exact HasCompactSupport.intro' hUc hU.isClosed fun x hx => Set.indicator_of_notMem hx _

end TestFunctions

section Fourier

variable {K : Type*} [Field K] [MeasurableSpace K]

-- pin: tateFourier (Def_LanglandsTunnell_TateLocalZeta.lean:85)
def tateFourier (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) : ℂ :=
  ∫ x, f x * ψ (x * y) ∂μ

-- pin: tateFourier_zero_fun (Def_LanglandsTunnell_TateLocalZeta.lean:88)
theorem tateFourier_zero_fun (ψ : AddChar K ℂ) (μ : Measure K) :
    tateFourier ψ μ (0 : K → ℂ) = 0 := by
  funext y
  simp [tateFourier]

end Fourier

section Characters

variable {K : Type*} [Field K]

-- pin: charExt (Def_LanglandsTunnell_TateLocalZeta.lean:99)
def charExt (χ : Kˣ →* ℂˣ) (x : K) : ℂ := by
  classical exact if h : x = 0 then 0 else (χ (Units.mk0 x h) : ℂ)

-- pin: charExt_zero (Def_LanglandsTunnell_TateLocalZeta.lean:102)
@[simp] theorem charExt_zero (χ : Kˣ →* ℂˣ) : charExt χ (0 : K) = 0 := by
  simp [charExt]

-- pin: charExt_of_ne_zero (Def_LanglandsTunnell_TateLocalZeta.lean:105)
theorem charExt_of_ne_zero (χ : Kˣ →* ℂˣ) {x : K} (h : x ≠ 0) :
    charExt χ x = χ (Units.mk0 x h) := by
  simp [charExt, h]

-- pin: charExt_coe_units (Def_LanglandsTunnell_TateLocalZeta.lean:109)
@[simp] theorem charExt_coe_units (χ : Kˣ →* ℂˣ) (u : Kˣ) : charExt χ (u : K) = χ u := by
  rw [charExt_of_ne_zero χ u.ne_zero, Units.mk0_val]

-- pin: charExt_one_of_ne_zero (Def_LanglandsTunnell_TateLocalZeta.lean:112)
theorem charExt_one_of_ne_zero {x : K} (h : x ≠ 0) : charExt (1 : Kˣ →* ℂˣ) x = 1 := by
  rw [charExt_of_ne_zero _ h, MonoidHom.one_apply, Units.val_one]

end Characters

section Zeta

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K]

-- pin: mulMeasure (Def_LanglandsTunnell_TateLocalZeta.lean:122)
def mulMeasure (μ : Measure K) : Measure K :=
  (μ.restrict {0}ᶜ).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹

-- pin: localZeta (Def_LanglandsTunnell_TateLocalZeta.lean:125)
def localZeta (μ : Measure K) (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s ∂(mulMeasure μ)

-- pin: localZeta_zero_fun (Def_LanglandsTunnell_TateLocalZeta.lean:128)
theorem localZeta_zero_fun (μ : Measure K) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta μ (0 : K → ℂ) χ s = 0 := by
  simp [localZeta]

-- pin: localGammaAt (Def_LanglandsTunnell_TateLocalZeta.lean:132)
def localGammaAt (μ : Measure K) (ψ : AddChar K ℂ) (f₀ : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / localZeta μ f₀ χ s

-- pin: localGammaAt_eq_zero_of_localZeta_eq_zero (Def_LanglandsTunnell_TateLocalZeta.lean:135)
theorem localGammaAt_eq_zero_of_localZeta_eq_zero {μ : Measure K} {ψ : AddChar K ℂ} {f₀ : K → ℂ}
    {χ : Kˣ →* ℂˣ} {s : ℂ} (h : localZeta μ f₀ χ s = 0) : localGammaAt μ ψ f₀ χ s = 0 := by
  simp [localGammaAt, h]

end Zeta

end LanglandsTunnell.TateLocal

end
