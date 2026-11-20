/-
  The adelic bookkeeping of the weight-one lift.

  `ratArch` is the real component of an idele-class representative, `ratArchHom` its bundled
  monoid homomorphism; `DetIntegral` is the finite-adèle integrality of level `Γ₁(N)` — the
  decompositions of an integral finite adèle, the compact-open subgroup `U` and its archimedean
  and finite parts, and the level comparison `finiteLevelZero ≤ finiteIntegralGL2`; `ArchLift`
  is the archimedean slash factor of the lift; and the last block is the lift's independence of
  the chosen decomposition and its equivariance under global points and `U`.

  This is the shared prelude of the five `weightOneLift` rows of SET-AF93. The pin states it
  `private` in each of the five `S_` files (48 declarations, ~1,600 duplicated lines); it is
  written here once, public, at the pin's names.

  spec-pin: P2M/Sol/S_LanglandsTunnell_isCuspidalFn_weightOneLift.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_weightOneLift_centralScalar_mul.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_isKfSmooth_weightOneLift.lean
  spec-pin: P2M/Sol/S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift.lean

  ## Port deltas

  - The pin's search-stage namespaces are renamed: `P4.I2` → `RatArch` (the real component) and
    `DetIntegral` (the finite-adèle integrality), `P2GProbe.R1` → `ArchLift` (the archimedean slash
    factor), and `P2GProbe.R3`/`R4a`/`R7` are dropped (the lift's own lemmas sit at
    `LanglandsTunnell`). All declaration names and statements are the pin's.
  - Eleven declarations are moved here from `LanglandsTunnell/WeightOneBound.lean`, where the
    boundedness row had transcribed them privately: `RatArch.{glFin_globalPoints_apply,
    isReal_rat_infinitePlace, ratArch, ratArch_eq_one_of_glArch_eq_one, ratArch_globalPoints,
    det_ratArch_globalPoints}` and `DetIntegral.{finiteLevelZero_le_finiteIntegralGL2,
    exists_algebraMap_eq_of_mem_integral, exists_intCast_eq_of_mem_integral,
    abs_eq_one_of_mem_integral, archDetNorm_default_eq}`. They are public here (the five rows
    import them) and `WeightOneBound` imports this module instead of declaring them.
  - The pin's `p2m_export`/`p2m_open` staging lines are dropped; the pin's repeated
    `noncomputable section`/`open` blocks are hoisted into one header; `ℍ` is `UpperHalfPlane`.
  - Import added: `AutomorphicForm.Adelic.ProductionPinsTail`, for
    `AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat` (the pin's
    `AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat`, pin 1 `:371` — the body of
    `hasWeightOneDecomp_of_ne_bot`), whose port homes it behind this module's import list.
  - Three body-level substitutions the pin's own text cannot replay at mathlib `v4.34` (all
    statement-neutral, bodies only):
    `Matrix.SpecialLinearGroup.mapGL_coe_matrix` no longer rewrites under `implicit` transparency
    (the `change` that follows it in the pin's `exists_mapGL_eq_of_mem_finiteIntegralGL2` does the
    job on its own); `AdelicBox.algebraMap_mem_adicCompletionIntegers` is
    `NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers` here (FR-0238's rename class);
    and `if_pos`/`dif_pos` are `ite_eq_left`/`dite_eq_left` (deprecated in this mathlib — a
    deprecation warning would break the module's silence).
  - `dedup --within` reports **two `shape` clusters (18 lines)**, and they stay: they are the
    pin's own two spellings of one lemma, `exists_algebraMap_eq_of_mem_integralFiniteAdeles`
    (generic `{R} [IsDedekindDomain]`, pin 1 `:154`) beside
    `exists_algebraMap_eq_of_mem_integral` (`𝓞 ℚ` specialised, pin 1 `:1101`), and the same for the
    `intCast` pair (pin 1 `:166`/`:1113`). Both names are on the pin's surface and both have
    consumers here (the generic pair serves the lift's `Γ₁` arguments, the specialised pair the
    boundedness row's determinant arguments), so neither can be dropped; the duplication is the
    pin's, not the port's.
  - Heartbeat probe (never installed, FR-0225). The silence gate is `lake env lean
    -DautoImplicit=false` at the project's own `maxHeartbeats = 4000000` (the module is silent
    there, and also at `-DmaxHeartbeats=200000`). The probe pair: silent at
    `-DmaxHeartbeats=10000`, failing at `-DmaxHeartbeats=5000` (`deterministic timeout at
    isDefEq`, `:513`), so the natural cost of the heaviest declaration is ≈5–10 k. No
    `set_option maxHeartbeats` is carried.
-/


import FLTForHuman.LanglandsTunnell.DihedralWeightOneLift
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsTail
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.AutomorphicForm.Adelic.ArchType

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix
open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open Matrix Matrix.GeneralLinearGroup
open CongruenceSubgroup ModularGroup
open AdelicDock
open NumberField.AdelicHaar
open HeckeIntegralSeam HeckePair
open AutomorphicForm.SmoothCusp IsDedekindDomain.HeightOneSpectrum
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne
local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "ν₀" => ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (NumberField.AdelicBox.adelicBox ℚ)
local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ


namespace LanglandsTunnell



namespace DetIntegral

theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

end DetIntegral

open DetIntegral

namespace RatArch

theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end RatArch

open RatArch

namespace DetIntegral

theorem exists_mapGL_eq_of_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hpos : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ)) :
    ∃ δ : SL(2, ℤ), Matrix.SpecialLinearGroup.mapGL ℚ δ = γ := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint

  have hγ' : ∀ i j, ∃ n : ℤ, (n : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) i j := fun i j =>
    exists_intCast_eq_of_mem_integralFiniteAdeles (by rw [← glFin_globalPoints_apply]; exact hγ i j)
  have hγinv' : ∀ i j, ∃ n : ℤ, (n : ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j :=
    fun i j => exists_intCast_eq_of_mem_integralFiniteAdeles (by
      rw [← glFin_globalPoints_apply, map_inv, map_inv]; exact hγinv i j)
  choose a ha using hγ'
  choose b hb using hγinv'
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => a i j with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => b i j with hB
  have hAmap : A.map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hA, ha]
  have hBmap : B.map (Int.castRingHom ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hB, hb]

  have hAB : A * B = 1 := by
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℚ) :=
      Matrix.map_injective (f := ⇑(Int.castRingHom ℚ)) Int.cast_injective
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _),
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdetAB : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdetQ : ((A.det : ℤ) : ℚ) = ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hAmap]
    exact (RingHom.map_det (Int.castRingHom ℚ) A)
  have hdetA : A.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetAB with h1 | h1
    · exact h1
    · exfalso
      rw [← hdetQ, h1] at hpos
      norm_num at hpos
  refine ⟨⟨A, hdetA⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (algebraMap ℤ ℚ) (A i j) = _
  rw [← hAmap, Matrix.map_apply]
  rfl

end DetIntegral

open DetIntegral

namespace RatArch

theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

def ratArch (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
    (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g))

theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArchHom g = ratArch g :=
  rfl

theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArch (g * g') = ratArch g * ratArch g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArch g⁻¹ = (ratArch g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_one : ratArch 1 = 1 :=
  by rw [← ratArchHom_apply, map_one]

theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    ratArch u = 1 := by
  unfold ratArch
  rw [hu, map_one, map_one]

theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ratArch (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    ratArch (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) = (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) = (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

end RatArch

open RatArch

namespace DetIntegral

abbrev archPart (k : 𝔾) : 𝔾 := adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ k)

abbrev finPart (k : 𝔾) : 𝔾 := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ k)

theorem eq_of_glArch_eq_of_glFin_eq {g g' : 𝔾} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ g')
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g') : g = g' := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha) i) j
    rwa [glArch_apply, glArch_apply] at this
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) hf) i) j
    rwa [glFin_apply, glFin_apply] at this

theorem glArch_archPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (archPart k) = glArch (𝓞 ℚ) ℚ k :=
  glArch_adelicArchGLIncl ℚ _

theorem glFin_archPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (archPart k) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glArch_finPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (finPart k) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

theorem glFin_finPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (finPart k) = glFin (𝓞 ℚ) ℚ k :=
  AdelicDock.glFin_finEmbed (𝓞 ℚ) ℚ _

theorem archPart_mul_finPart (k : 𝔾) : archPart k * finPart k = k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, glArch_archPart, glArch_finPart, mul_one])
    (by rw [map_mul, glFin_archPart, glFin_finPart, one_mul])

theorem archPart_mul_finPart_comm (k k' : 𝔾) : archPart k * finPart k' = finPart k' * archPart k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, glArch_archPart, glArch_finPart, mul_one, one_mul])
    (by rw [map_mul, map_mul, glFin_archPart, glFin_finPart, one_mul, mul_one])

theorem finPart_eq_self_of_glArch_eq_one {u : 𝔾} (hu : glArch (𝓞 ℚ) ℚ u = 1) : finPart u = u :=
  eq_of_glArch_eq_of_glFin_eq (by rw [glArch_finPart, hu]) (glFin_finPart u)

end DetIntegral

open DetIntegral

namespace RatArch

theorem ratArch_archPart (k : 𝔾) : ratArch (archPart k) = ratArch k := by
  unfold ratArch
  rw [glArch_archPart]

end RatArch

open RatArch

namespace DetIntegral

theorem mem_U_top_iff (u : 𝔾) :
    u ∈ (productionPinsCompact ℚ).U ⊤ ↔ glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤ ∧ glArch (𝓞 ℚ) ℚ u = 1 :=
  Iff.rfl

theorem finPart_mem_U_top {k : 𝔾} (hk : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤) :
    finPart k ∈ (productionPinsCompact ℚ).U ⊤ :=
  (mem_U_top_iff _).mpr ⟨by rwa [glFin_finPart], glArch_finPart k⟩

theorem intCast_mem_integralFiniteAdeles (n : ℤ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  have h := algebraMap_mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) v (n : 𝓞 ℚ)
  rw [map_intCast] at h
  exact h

end DetIntegral

open DetIntegral

namespace ArchLift

section

variable (f : ℍ → ℂ)

theorem weightOneArchLift_def (h : GL (Fin 2) ℝ) :
    weightOneArchLift f h = (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (1 : ℤ) :=
  rfl

theorem weightOneArchLift_mul_of_slash_eq (γ h : GL (Fin 2) ℝ) (hγ : f ∣[(1 : ℤ)] γ = f)
    (hdet : γ.det.val = 1) :
    weightOneArchLift f (γ * h) = weightOneArchLift f h := by
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, hγ]
  congr 2
  rw [map_mul, Units.val_mul, hdet, one_mul]

theorem slash_one_scalar (c : GL (Fin 2) ℝ) (r : ℝ) (hr : 0 < r)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    f ∣[(1 : ℤ)] c = fun z => ((r⁻¹ : ℝ) : ℂ) * f z := by
  have h00 : c 0 0 = r := by
    have := congr_fun (congr_fun hc 0) 0; simpa using this
  have h01 : c 0 1 = 0 := by
    have := congr_fun (congr_fun hc 0) 1; simpa using this
  have h10 : c 1 0 = 0 := by
    have := congr_fun (congr_fun hc 1) 0; simpa using this
  have h11 : c 1 1 = r := by
    have := congr_fun (congr_fun hc 1) 1; simpa using this
  have hdet : c.det.val = r * r := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < c.det.val := by rw [hdet]; positivity
  have hsmul : ∀ z : ℍ, c • z = z := by
    intro z
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hdetpos, num, denom, h00, h01, h10, h11]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    rw [zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ hr']
  funext z
  rw [ModularForm.slash_apply, σ, ite_eq_left hdetpos, hsmul z, denom, h10, h11]
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, zero_mul, zero_add, sub_self,
    zpow_zero, mul_one, _root_.zpow_neg, zpow_one, Complex.ofReal_inv]
  ring

theorem weightOneArchLift_scalar_mul (c h : GL (Fin 2) ℝ) (r : ℝ) (hr : 0 < r)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    weightOneArchLift f (c * h) = (r : ℂ) * weightOneArchLift f h := by
  have hdet : c.det.val = r * r := by
    have h00 : c 0 0 = r := by
      have := congr_fun (congr_fun hc 0) 0; simpa using this
    have h01 : c 0 1 = 0 := by
      have := congr_fun (congr_fun hc 0) 1; simpa using this
    have h10 : c 1 0 = 0 := by
      have := congr_fun (congr_fun hc 1) 0; simpa using this
    have h11 : c 1 1 = r := by
      have := congr_fun (congr_fun hc 1) 1; simpa using this
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, slash_one_scalar f c r hr hc]
  have hfun : (fun z => ((r⁻¹ : ℝ) : ℂ) * f z) = ((r⁻¹ : ℝ) : ℂ) • f := by
    funext z; simp [smul_eq_mul]
  rw [hfun, ModularForm.smul_slash, σ_ofReal, Pi.smul_apply, smul_eq_mul, map_mul, Units.val_mul,
    hdet]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [zpow_one]
  push_cast
  field_simp

end

end ArchLift

open ArchLift

theorem hasWeightOneDecomp_of_ne_bot {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : DihedralWeightOne.HasWeightOneDecomp N g := by
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ :=
    AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat hN g
  exact ⟨γ, h, u, hu, hfin, hpos default (IsTotallyReal.isReal default), hg⟩

namespace RatArch

theorem ratArchGL2_eq_ratArch (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g = ratArch g :=
  rfl

end RatArch

open RatArch

namespace DetIntegral

theorem mem_of_algebraMap_mem_idealBall {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) {r : 𝓞 ℚ}
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r) ∈ idealBall (𝓞 ℚ) ℚ N) :
    r ∈ N := by
  classical
  rw [← Ideal.iInf_maxPowDividing_eq hN, Ideal.mem_iInf]
  intro v
  have h1 := h v
  rw [show (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)) v
      = algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ r) from rfl, valued_algebraMap,
    idealBound_of_ne_bot hN, HeightOneSpectrum.intValuation_le_pow_iff_mem] at h1
  exact h1

theorem dvd_of_algebraMap_intCast_mem_idealBall {n : ℕ} (hn : n ≠ 0) {k : ℤ}
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (k : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    (n : ℤ) ∣ k := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have h' : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ))
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rwa [map_intCast]
  have hmem : (k : 𝓞 ℚ) ∈ Ideal.span {(n : 𝓞 ℚ)} := mem_of_algebraMap_mem_idealBall hN h'
  have hdvd : (n : 𝓞 ℚ) ∣ (k : 𝓞 ℚ) := Ideal.mem_span_singleton.mp hmem
  have := map_dvd Rat.ringOfIntegersEquiv hdvd
  simpa using this

theorem glFin_globalPoints_mapGL_apply (ε : SL(2, ℤ)) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((ε i j : ℤ) : ℚ) := by
  rw [glFin_globalPoints_apply]
  congr 1

theorem mem_Gamma1_of_glFin_mem_finiteLevelOne {n : ℕ} (hn : n ≠ 0) (ε : SL(2, ℤ))
    (hε : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    ε ∈ Gamma1 n := by
  have hL := (mem_finiteLevelOne_iff.mp hε).1

  have hc : (n : ℤ) ∣ ε 1 0 := by
    apply dvd_of_algebraMap_intCast_mem_idealBall hn
    have := hL.lowerLeft
    rwa [glFin_globalPoints_mapGL_apply] at this

  have hd : (n : ℤ) ∣ ε 1 1 - 1 := by
    apply dvd_of_algebraMap_intCast_mem_idealBall hn
    have := hL.lowerRight
    rw [glFin_globalPoints_mapGL_apply] at this
    rwa [Int.cast_sub, Int.cast_one, map_sub, map_one]
  have hc' : (ε 1 0 : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hc
  have hd' : (ε 1 1 : ZMod n) = 1 := by
    have h0 : ((ε 1 1 - 1 : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hd
    rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at h0
    exact h0

  have hdet : ε 0 0 * ε 1 1 - ε 0 1 * ε 1 0 = 1 := by
    have := ε.det_coe
    rwa [Matrix.det_fin_two] at this
  have ha' : (ε 0 0 : ZMod n) = 1 := by
    have h1 : ((ε 0 0 * ε 1 1 - ε 0 1 * ε 1 0 : ℤ) : ZMod n) = 1 := by rw [hdet, Int.cast_one]
    push_cast at h1
    rwa [hd', hc', mul_one, mul_zero, sub_zero] at h1
  exact (Gamma1_mem n ε).mpr ⟨ha', hd', hc'⟩

theorem finiteLevelZero_le_finiteIntegralGL2 (N : Ideal (𝓞 ℚ)) :
    finiteLevelZero (𝓞 ℚ) ℚ N ≤ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  intro g hg
  rw [mem_finiteLevelZero_iff] at hg
  show g ∈ finiteLevelZero (𝓞 ℚ) ℚ ⊤
  rw [mem_finiteLevelZero_iff]
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ),
      IsLevelZeroMatrix (𝓞 ℚ) ℚ N m → IsLevelZeroMatrix (𝓞 ℚ) ℚ ⊤ m := fun m hm =>
    ⟨hm.integral, fun v => (hm.lowerLeft v).trans
      ((idealBound_le_one N v).trans (idealBound_top v).ge)⟩
  exact ⟨key _ hg.1, key _ hg.2⟩

end DetIntegral

open DetIntegral

namespace ArchLift

theorem weightOneArchLift_eq_of_decomps {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ γ' : GL (Fin 2) ℚ}
    {h u h' u' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u)
    (hu' : u' ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh' : glFin (𝓞 ℚ) ℚ h' = 1)
    (hpos' : LanglandsTunnell.ratArchGL2 h' ∈ GLPos (Fin 2) ℝ)
    (hg' : g = globalPoints (𝓞 ℚ) ℚ γ' * h' * u') :
    weightOneArchLift f (LanglandsTunnell.ratArchGL2 h)
      = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h') := by
  simp only [ratArchGL2_eq_ratArch] at hpos hpos' ⊢
  have hufin := glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu
  have hu'fin := glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu'
  have huarch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu
  have hu'arch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu'
  set P := globalPoints (𝓞 ℚ) ℚ with hP
  set δ : GL (Fin 2) ℚ := γ'⁻¹ * γ with hδ
  have hquot : P δ = h' * u' * u⁻¹ * h⁻¹ := by
    have E : P γ * (h * u) = P γ' * (h' * u') := by rw [← mul_assoc, ← mul_assoc, ← hg, ← hg']
    rw [hδ, map_mul, map_inv]
    have : P γ = P γ' * (h' * u') * (h * u)⁻¹ := eq_mul_inv_of_mul_eq E
    rw [this, _root_.mul_inv_rev]
    group

  have hlevel : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [hquot, map_mul, map_mul, map_mul, map_inv, map_inv, hh, hh', one_mul, inv_one, mul_one]
    exact Subgroup.mul_mem _ hu'fin (Subgroup.inv_mem _ hufin)
  have hint : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _ hlevel)

  have harch : ratArch (P δ) = ratArch h' * (ratArch h)⁻¹ := by
    rw [hquot, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_inv,
      ratArch_eq_one_of_glArch_eq_one huarch, ratArch_eq_one_of_glArch_eq_one hu'arch, inv_one,
      mul_one, mul_one]
  have hdetpos : 0 < ((GeneralLinearGroup.det δ : ℚˣ) : ℚ) := by
    have h1 : 0 < ((ratArch (P δ)).det.val : ℝ) := by
      rw [harch, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hpos' (inv_pos.mpr hpos)
    rw [det_ratArch_globalPoints] at h1
    exact_mod_cast h1
  obtain ⟨ε, hε⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hint hdetpos

  have hεΓ : ε ∈ Gamma1 n := by
    apply mem_Gamma1_of_glFin_mem_finiteLevelOne hn
    rw [hε]
    exact hlevel
  have hh'eq : ratArch h' = (ε : GL (Fin 2) ℝ) * ratArch h := by
    rw [← ratArch_globalPoints_mapGL, hε, harch, inv_mul_cancel_right]
  have hεdet : ((ε : GL (Fin 2) ℝ)).det.val = 1 := by simp
  rw [hh'eq, weightOneArchLift_mul_of_slash_eq f _ _ (hf ε hεΓ) hεdet]

end ArchLift

open ArchLift

theorem weightOneLift_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hfin : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) := by
  have H : HasWeightOneDecomp (Ideal.span {(n : 𝓞 ℚ)}) g := ⟨γ, h, u, hu, hfin, hpos, hg⟩
  unfold DihedralWeightOne.weightOneLift
  rw [dite_eq_left H]
  obtain ⟨u₀, hu₀, hh₀, hpos₀, hg₀⟩ := H.choose_spec.choose_spec
  exact weightOneArchLift_eq_of_decomps hn f hf hu₀ hh₀ hpos₀ hg₀ hu hfin hpos hg

theorem weightOneLift_mul_of_mem_U {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) {u₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (g * u₀) = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := hasWeightOneDecomp_of_ne_bot hN g
  have hg' : g * u₀ = globalPoints (𝓞 ℚ) ℚ γ * h * (u * u₀) := by
    rw [hg]; simp only [mul_assoc]
  rw [weightOneLift_eq hn f hf (g * u₀) γ h (u * u₀) (Subgroup.mul_mem _ hu hu₀) hfin hpos hg',
    weightOneLift_eq hn f hf g γ h u hu hfin hpos hg]

theorem weightOneLift_globalPoints_mul {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (γ₀ : GL (Fin 2) ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ₀ * g)
      = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := hasWeightOneDecomp_of_ne_bot hN g
  have hg' : globalPoints (𝓞 ℚ) ℚ γ₀ * g = globalPoints (𝓞 ℚ) ℚ (γ₀ * γ) * h * u := by
    rw [hg, map_mul]; simp only [mul_assoc]
  rw [weightOneLift_eq hn f hf _ (γ₀ * γ) h u hu hfin hpos hg',
    weightOneLift_eq hn f hf g γ h u hu hfin hpos hg]

namespace DetIntegral

theorem mem_U_iff (N : Ideal (𝓞 ℚ)) (u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    u ∈ (productionPinsCompact ℚ).U N ↔
      glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glArch (𝓞 ℚ) ℚ u = 1 :=
  Iff.rfl

theorem finPart_mem_U {N : Ideal (𝓞 ℚ)} {k : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hk : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ N) : finPart k ∈ (productionPinsCompact ℚ).U N :=
  (mem_U_iff N _).mpr ⟨by rwa [glFin_finPart], glArch_finPart k⟩

end DetIntegral

open DetIntegral

theorem weightOneLift_mul_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {g₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ₀ : GL (Fin 2) ℚ} {h₀ u₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh₀ : glFin (𝓞 ℚ) ℚ h₀ = 1)
    (hg₀ : g₀ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * u₀) (k : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (hkf : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}))
    (hdet : 0 < (ratArch h₀ * ratArch k).det.val) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (g₀ * k) = weightOneArchLift f (ratArch h₀ * ratArch k) := by
  have hu : u₀ * finPart k ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}) :=
    Subgroup.mul_mem _ hu₀ (finPart_mem_U hkf)
  have hfin : glFin (𝓞 ℚ) ℚ (h₀ * archPart k) = 1 := by
    rw [map_mul, hh₀, glFin_archPart, mul_one]
  have hpos : LanglandsTunnell.ratArchGL2 (h₀ * archPart k) ∈ GLPos (Fin 2) ℝ := by
    show 0 < (LanglandsTunnell.ratArchGL2 (h₀ * archPart k)).det.val
    rw [ratArchGL2_eq_ratArch, ratArch_mul, ratArch_archPart]
    exact hdet
  have hu₀' : finPart u₀ = u₀ := finPart_eq_self_of_glArch_eq_one ((mem_U_iff _ u₀).mp hu₀).2
  have hg : g₀ * k = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart k) * (u₀ * finPart k) :=
    calc g₀ * k = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * u₀ * (archPart k * finPart k) := by
          rw [archPart_mul_finPart, hg₀]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (finPart u₀ * archPart k) * finPart k := by rw [hu₀']; group
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (archPart k * finPart u₀) * finPart k := by
          rw [archPart_mul_finPart_comm]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart k) * (u₀ * finPart k) := by rw [hu₀']; group
  rw [weightOneLift_eq hn f hf (g₀ * k) γ₀ _ _ hu hfin hpos hg, ratArchGL2_eq_ratArch, ratArch_mul,
    ratArch_archPart]

theorem det_coe_SL (ρ : SL(2, ℤ)) : ((ρ : GL (Fin 2) ℝ)).det.val = 1 := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ ρ).det.val = 1
  rw [Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]

namespace DetIntegral

theorem exists_algebraMap_eq_of_mem_integral {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem exists_intCast_eq_of_mem_integral {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integral hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

theorem abs_eq_one_of_mem_integral {q : ℚ} (hq0 : q ≠ 0)
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hq' : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q⁻¹ ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) : |q| = 1 := by
  obtain ⟨a, ha⟩ := exists_intCast_eq_of_mem_integral hq
  obtain ⟨b, hb⟩ := exists_intCast_eq_of_mem_integral hq'
  have hab : a * b = 1 := by
    have : ((a * b : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, ha, hb, mul_inv_cancel₀ hq0]
    exact_mod_cast this
  rw [← ha]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h1 | h1 <;> simp [h1]

theorem archDetNorm_default_eq (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    archDetNorm (default : InfinitePlace ℚ) g = |(ratArch g).det.val| := by
  unfold archDetNorm ratArch
  rw [GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, GeneralLinearGroup.val_det_apply,
    ← Real.norm_eq_abs]
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (isReal_rat_infinitePlace (default : InfinitePlace ℚ))
  exact (hiso.norm_map_of_map_zero (map_zero _) _).symm

end DetIntegral

open DetIntegral

end LanglandsTunnell

end
