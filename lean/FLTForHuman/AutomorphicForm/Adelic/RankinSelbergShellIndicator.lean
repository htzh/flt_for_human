/-
  The Rankin–Selberg shell indicator: the Whittaker coefficient squared against the section.

  Let `x` be a finite sum of translates of an automorphic function `x₀` by unipotent elements
  supported in a finite set `S` of places, `ω`-equivariant under the centre with trivial
  archimedean-part rows, and vanishing against the lower unipotent of depth `n`. Let `φ` be an
  induced section of `η(s)` with the indicator values `0`, `1` on the adelic maximal compact and
  the prescribed support in the bottom row. Then there is a **finite** set `J` of archimedean-only
  elements such that

    `‖W x (diagOne t * k)‖² * ‖φ s (diagOne t * k)‖² ≤ 1_S(t) * ‖t‖^{s.re + 1/2} * ∑_{g ∈ J} ‖W x₀ (…)‖²`

  for every `s`, every `k` in the adelic maximal compact and every `t` that is a unit outside `S`:
  the coefficient of `x` is bounded by a finite sum of coefficients of `x₀` read off at
  archimedean translates, with the shell indicator and the section's norm factor on the right.

  This is the "shell surgery" input of the Rankin–Selberg unfolding: it turns the squared
  coefficient of the unipotent average, which is what the quotient integral carries, into a
  finite sum of archimedean-data coefficients — the step that makes the unfolding integrable.

  The pin's four search-stage namespaces are renamed or merged: `Ws50CH1` (the shell-surgery
  development) becomes `AutomorphicForm.RankinSelberg.ShellSurgery`, and `RS27T2`, `RS27` are
  folded into it (their declarations are engines of the same row, and merging keeps the pin's
  names — `evalAt`, `finAdeleOf`, `T1_strip` … — at their pin spelling). `RS24`, the pin's
  unipotent-depth block, is **not** repeated here: it is already ported at
  `AutomorphicForm.UnipotentDepth` (`Adelic/RightTranslateSpan.lean`) and imported. The row lives
  at the pin's published name in `AutomorphicForm.RankinSelberg`. Five of the pin's declarations
  are already in the port only as `private` helpers of `Automorphic/Adelic/WhittakerCoefficient.lean`
  (`whittakerCoefficient_mul_right`, `glArch_unipotentGL2_eq_one`,
  `mul_comm_of_glArch_eq_one_of_glFin_eq_one`) or of a dead module (`evalAt`-shaped `projV`,
  `finAdeleOf`-shaped `entryF`); a `private` decl is not importable, so the module transcribes them
  at the pin's names under `ShellSurgery`, which is a fresh namespace and therefore no second public
  copy of any full name (FR-0259).

  The pin's `gl_ext` is imported (`AutomorphicForm.gl_ext`, `Adelic/MaximalCompactFactors.lean`)
  rather than restated: the pin states it twice, once at the file's `Ws50CH1` head and once as a
  local `have` inside `torus_at_S`; the port keeps the one home and the local `have` is the
  per-component form the proof needs.

  Build record (AF98C).

  * Imports: three added to the scaffold's six — `MaximalCompactFactors` (the two-factor split and
    `gl_ext`), `RightTranslateSpan` (the pin's already-ported `RS24` block, 23 declarations),
    `BorelSubgroup` (`adelicBorel`, `borelDiagFst`, `borelDiagSnd`, the Iwasawa decomposition's
    home), and nothing else: `evalAt`/`finAdeleOf` are the pin's own and are transcribed here.
  * Heartbeat probe, **never installed** (FR-0225): silent at `70000`, fails at `65000`
    (deterministic timeout at `isDefEq`/`whnf` inside `torus_at_S`, the pin's only
    `set_option maxHeartbeats 1600000 in` declaration — the port carries **no** option and needs
    none). Measured with the edit loop, `lake env lean -DautoImplicit=false -DmaxHeartbeats=<cap>`;
    the module is silent at the project's own `200000` (a ~3× margin) and at the lakefile's
    `4000000`, so no floor is carried.
  * v4.34 proof-side drift in the pin's bodies: `if_pos`/`if_neg` →
    `ite_eq_left`/`ite_eq_right` (seven sites: four in `T4_boxShell`, three in the row), `push Not` for
    `push_neg` (`T4_boxShell`), `letI := pins.nS` → `let : MeasurableSpace …` (two sites, the
    `linter.style.haveILetI` cure holds here because the value is a projection, FR-0262's
    exception does not apply), `eq_of_glArch_eq_of_glFin_eq` for the pin's per-component `gl_ext`
    (`mul_comm_of_glArch_eq_one_of_glFin_eq_one`,
    `mul_inv_finEmbed_glFin_eq_adelicArchGLIncl`), the pin's `val_finitePartUnits` (not carried by
    the port) replaced by the `rfl`-level `change` at the two `T2_ideleNorm_eq_one` sites, and one
    unused-`simp` argument dropped in `T2_unipotentGL2_algebraMap_eq_globalPoints`.
  * One declaration-scoped lint silencer: `linter.unusedVariables false` on the row, for the pin's
    own `hsec` binder, which the statement binds without an underscore and which no proof can
    reference (FR-0218/FR-0236: a `sorry` body hides this warning).

  spec-pin: P2M/Sol/S_AutomorphicForm_RankinSelberg_exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law.lean
-/


import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.RankinSelbergSection
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.RightTranslateSpan
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.NumberTheory.StandardAddChar.GlobalAndInfinite

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace AutomorphicForm

namespace RankinSelberg

namespace ShellSurgery

/-! ## The coefficient's laws on the right, and the archimedean/finite split

The pin's `Ws50CH1` prelude. The coefficient is covariant under right translation, hence invariant
under a right factor on which the function is already invariant; and a `diagOne` element commuting
with an archimedean-only element produces the split the cover argument needs. -/

theorem whittakerCoefficient_mul_right (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (a : F) (g k : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ a (g * k) = whittakerCoefficient F pins ψ (fun y => φ (y * k)) a g := by
  let : MeasurableSpace (AdeleRing (𝓞 F) F) := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

theorem whittakerCoefficient_mul_right_eq_of_forall (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (a : F) (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ y, φ (y * k) = φ y) :
    whittakerCoefficient F pins ψ φ a (g * k) = whittakerCoefficient F pins ψ φ a g := by
  rw [whittakerCoefficient_mul_right]
  congr 1
  funext y
  exact hk y

theorem glArch_unipotentGL2_eq_one (K : Type) [Field K] [NumberField K]
    (y : AdeleRing (𝓞 K) K) (hy : y.1 = 0) : glArch (𝓞 K) K (unipotentGL2 y) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, unipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hy]

theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one (K : Type) [Field K] [NumberField K]
    {a b : AdelicGL2 (𝓞 K) K} (ha : glArch (𝓞 K) K a = 1) (hb : glFin (𝓞 K) K b = 1) : a * b = b * a :=
  eq_of_glArch_eq_of_glFin_eq K (by rw [map_mul, map_mul, ha, one_mul, mul_one])
    (by rw [map_mul, map_mul, hb, mul_one, one_mul])

theorem mul_inv_finEmbed_glFin_eq_adelicArchGLIncl (K : Type) [Field K] [NumberField K] (g : AdelicGL2 (𝓞 K) K) :
    g * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g))⁻¹ = adelicArchGLIncl K (glArch (𝓞 K) K g) :=
  eq_of_glArch_eq_of_glFin_eq K
    (by rw [map_mul, map_inv, AdelicDock.glArch_finEmbed, inv_one, mul_one, glArch_adelicArchGLIncl])
    (by rw [map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel, glFin_adelicArchGLIncl])


/-! ### The adelic coordinates and the `diagOne` algebra

The pin's `RS27T2`: the finite-part evaluation, the integral finite adèle, and the elementary
commutation laws among `diagOne`, `centralScalar` and `unipotentGL2`. -/

section TorusCoord

variable (F : Type) [Field F] [NumberField F]

noncomputable def evalAt (v : HeightOneSpectrum (𝓞 F)) : AdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  (finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)

theorem evalAt_eq (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F) : x.2 v = evalAt F v x := rfl

noncomputable def finAdeleOf (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨x, Filter.Eventually.of_forall hx⟩

theorem finAdeleOf_apply (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    finAdeleOf F x hx v = x v := rfl

theorem diagOne_coe_eq (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![(t : AdeleRing (𝓞 F) F), 0; 0, 1] := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem diagOne_mul_unipotentGL2 (t : (AdeleRing (𝓞 F) F)ˣ) (x : AdeleRing (𝓞 F) F) :
    diagOne t * unipotentGL2 x = unipotentGL2 ((t : AdeleRing (𝓞 F) F) * x) * diagOne t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe, unipotentGL2_coe, diagOne_coe_eq, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add]

theorem centralScalar_coe_eq (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      !![(z : AdeleRing (𝓞 F) F), 0; 0, (z : AdeleRing (𝓞 F) F)] := by
  rw [centralScalar, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

theorem diagOne_mul_centralScalar (t z : (AdeleRing (𝓞 F) F)ˣ) :
    diagOne t * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * diagOne t :=
  (centralScalar_mul_comm z (diagOne t)).symm

end TorusCoord


/-! ### The centre, the unipotent and the idèle norm

The pin's `T2` block: centrality of `centralScalar` against an arbitrary element, the rational
unipotent as a global point, the central character pulling out of the coefficient, the idèle norm
of a unit of valuation one everywhere. -/

theorem T2_centralScalar_comm (K : Type) [Field K] [NumberField K] (z : (AdeleRing (𝓞 K) K)ˣ) (h : AdelicGL2 (𝓞 K) K) :
    h * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * h :=
  (centralScalar_mul_comm z h).symm

theorem T2_unipotentGL2_algebraMap_eq_globalPoints (K : Type) [Field K] [NumberField K] (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem T2_whittakerCoefficient_mul_central (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g c : AdelicGL2 (𝓞 F) F) (ω : ℂ)
    (hcomm : ∀ h : AdelicGL2 (𝓞 F) F, h * c = c * h) (hc : ∀ h, φ (c * h) = ω * φ h) :
    whittakerCoefficient F pins ψ φ α (g * c) = ω * whittakerCoefficient F pins ψ φ α g := by
  let : MeasurableSpace (AdeleRing (𝓞 F) F) := pins.nS
  simp only [whittakerCoefficient]
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, hcomm (unipotentGL2 u * g), hc]
  ring

theorem T2_units_inv_snd_apply (K : Type) [Field K] [NumberField K] (s : (AdeleRing (𝓞 K) K)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w = (((s : AdeleRing (𝓞 K) K)).2 w)⁻¹ := by
  have h : ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w * ((s : AdeleRing (𝓞 K) K)).2 w = 1 := by
    have := congrArg (fun x : AdeleRing (𝓞 K) K => x.2 w) s.inv_mul
    exact this
  exact eq_inv_of_mul_eq_one_left h

theorem T2_ideleNorm_eq_one (K : Type) [Field K] [NumberField K] (D : (AdeleRing (𝓞 K) K)ˣ)
    (hD1 : ((D : AdeleRing (𝓞 K) K)).1 = 1)
    (hDv : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((D : AdeleRing (𝓞 K) K)).2 v) = 1) :
    NumberField.TateGlobal.ideleNorm K D = 1 := by
  refine NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K D hD1 ?_
  rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((D : AdeleRing (𝓞 K) K).2 v) ≤ 1
    exact (hDv v).le
  · have hfin : ((NumberField.AdeleRing.finitePartUnits (𝓞 K) K D)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ)
        = NumberField.AdeleRing.finitePartUnits (𝓞 K) K D⁻¹ :=
      (map_inv (NumberField.AdeleRing.finitePartUnits (𝓞 K) K) D).symm
    rw [hfin, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (((D⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) ≤ 1
    rw [T2_units_inv_snd_apply, map_inv₀, hDv, inv_one]

/-! ### The two compact factors of a maximal-compact element

The pin's `T1`: every `k` in the adelic maximal compact is a `maximalCompactAt S` factor times a
`maximalCompactAway S` factor, and the `S`-part of the matrix entries — and the whole archimedean
part — is unchanged. -/

theorem T1_strip (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (k : AdelicGL2 (𝓞 K) K)
    (hk : k ∈ adelicMaximalCompact K) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 K) K, k₁ ∈ maximalCompactAt K S ∧ k₂ ∈ maximalCompactAway K S ∧ k = k₁ * k₂ ∧
      glArch (𝓞 K) K k₁ = glArch (𝓞 K) K k ∧
      ∀ (i j : Fin 2), ∀ v ∈ S, (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2) v =
        (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2) v := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk12⟩ :=
    AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq K S k hk
  have hk₂' := mem_maximalCompactAway_iff.mp hk₂
  refine ⟨k₁, k₂, hk₁, hk₂, hk12, ?_, ?_⟩
  · rw [hk12, map_mul, hk₂'.2.1, mul_one]
  · intro i j v hv
    have e : ∀ g : AdelicGL2 (𝓞 K) K, (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2) v =
        ((finComponent (𝓞 K) K v (glFin (𝓞 K) K g) : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := fun g => by
      rw [finComponent_apply, glFin_apply]
    rw [e, e, hk12, map_mul, map_mul, hk₂'.2.2 v hv, mul_one]

/-! ### The section's norm on the shell

The pin's `T5`: on the adelic maximal compact the section scales by the idèle norm to the power
`s.re + 1/2`, and its nonvanishing forces the shell inequality on the `S`-places. -/

theorem T5_sectionNorm (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
    (hφval : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          φ s k = 0 ∨ φ s k = 1)
    (hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
    (hsec : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        φ s (diagOne t * k) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s k)
    (s : ℂ) (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K) (t : (AdeleRing (𝓞 K) K)ˣ) :
    ‖φ s (diagOne t * k)‖ ≤ NumberField.TateGlobal.ideleNorm K t ^ (s.re + 1 / 2) ∧
      (φ s (diagOne t * k) ≠ 0 → ∀ v ∈ S,
        Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
          Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) := by
  have hkK := mem_adelicMaximalCompact_iff.mp hk
  have hval := hφval s k hkK.1 hkK.2
  have hnpos := NumberField.TateGlobal.ideleNorm_pos (F := K) t
  have hre : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
  constructor
  · rw [hsec s k hk t, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, hre]
    have h1 : ‖φ s k‖ ≤ 1 := by
      rcases hval with h | h
      · rw [h, norm_zero]; exact zero_le_one
      · rw [h, norm_one]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hnpos.le _) h1
  · intro hne v hv
    by_contra hlt
    apply hne
    rw [hsec s k hk t, hφsupp s k hkK.1 hkK.2 ⟨v, hv, hlt⟩, mul_zero]


/-! ### The cover of the shell by archimedean translates

The pin's `lcover_whittaker_sq_le_sum` and `C1_cover`: the `diagOne t * κ` value of the coefficient
is *equal* to one of finitely many archimedean-only translates (so the square is bounded by the
finite sum of squares), and the same cover absorbs the idèle part of a `diagOne (t * u)` argument. -/

theorem lcover_whittaker_sq_le_sum (K : Type) [Field K] [NumberField K]
    (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (α : K)
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (κ : AdelicGL2 (𝓞 K) K) (hκ : glArch (𝓞 K) K κ = 1)
    (a : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ J : Finset (AdelicGL2 (𝓞 K) K), (∀ g ∈ J, glArch (𝓞 K) K g = 1) ∧
      ∀ (y : AdelicGL2 (𝓞 K) K) (t : (AdeleRing (𝓞 K) K)ˣ),
        ((t : AdeleRing (𝓞 K) K)).1 = 1 →
        (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((t : AdeleRing (𝓞 K) K)).2 w = 1) →
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
            ((Multiplicative.ofAdd (a v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∃ g ∈ J, whittakerCoefficient K pins ψ x₀ α (y * (diagOne t * κ)) =
            whittakerCoefficient K pins ψ x₀ α (y * g)) ∧
        ‖whittakerCoefficient K pins ψ x₀ α (y * (diagOne t * κ))‖ ^ 2 ≤
          ∑ g ∈ J, ‖whittakerCoefficient K pins ψ x₀ α (y * g)‖ ^ 2 := by
  obtain ⟨G, hGarch, hGcov⟩ := UnipotentDepth.exists_finset_diagOne_mul_mem_mul_levelOne K N hN S κ a
  refine ⟨G, fun g hg => (hGarch g hg).trans hκ, fun y t ht1 htS htv => ?_⟩
  obtain ⟨g, hg, hmem⟩ := hGcov t ht1 htS (fun v hv => htv v hv)
  have heq : whittakerCoefficient K pins ψ x₀ α (y * (diagOne t * κ)) =
      whittakerCoefficient K pins ψ x₀ α (y * g) := by
    have hsplit : y * (diagOne t * κ) = (y * g) * (g⁻¹ * (diagOne t * κ)) := by group
    rw [hsplit, whittakerCoefficient_mul_right_eq_of_forall K pins ψ x₀ α (y * g) _
      (fun z => hx₀lev z _ hmem)]
  refine ⟨⟨g, hg, heq⟩, ?_⟩
  rw [heq]
  exact Finset.single_le_sum (f := fun g => ‖whittakerCoefficient K pins ψ x₀ α (y * g)‖ ^ 2)
    (fun _ _ => by positivity) hg

theorem C1_cover (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    (κ : AdelicGL2 (𝓞 K) K) (hκarch : glArch (𝓞 K) K κ = 1)
    (aexp : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ J : Finset (AdelicGL2 (𝓞 K) K), (∀ g ∈ J, glArch (𝓞 K) K g = 1) ∧
      ∀ (a : GL (Fin 2) (InfiniteAdeleRing K)) (t u : (AdeleRing (𝓞 K) K)ˣ),
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1) →
        ((u : AdeleRing (𝓞 K) K)).1 = 1 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) →
        (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K)).2 v) = 1) →
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
            ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        ∃ g ∈ J,
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
            (diagOne (t * u) * adelicArchGLIncl K a * κ) =
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
            (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K a * g) := by
  obtain ⟨J, hJarch, hJ⟩ := lcover_whittaker_sq_le_sum K
    (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) 1
    x₀ N hN hx₀lev S κ hκarch aexp
  refine ⟨J, hJarch, fun a t u htS hu1 huS huv htv => ?_⟩

  set p : (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.partAt K ∅ t with hp
  set tf : (AdeleRing (𝓞 K) K)ˣ := p⁻¹ * (t * u) with htf
  have hp1 : ((p : AdeleRing (𝓞 K) K)).1 = ((t : AdeleRing (𝓞 K) K)).1 := NumberField.Idele.partAt_fst K ∅ t
  have hp2 : ∀ w : HeightOneSpectrum (𝓞 K), ((p : AdeleRing (𝓞 K) K)).2 w = 1 := fun w =>
    NumberField.Idele.partAt_snd_of_not_mem K ∅ t (Finset.notMem_empty w)
  have hpinv2 : ∀ w : HeightOneSpectrum (𝓞 K), ((↑(p⁻¹) : AdeleRing (𝓞 K) K)).2 w = 1 := fun w => by
    rw [UnipotentDepth.units_inv_snd_apply, hp2, inv_one]
  have htf1 : ((tf : AdeleRing (𝓞 K) K)).1 = 1 := by
    have h : ((↑(p⁻¹) : AdeleRing (𝓞 K) K)).1 * ((p : AdeleRing (𝓞 K) K)).1 = 1 :=
      congrArg Prod.fst p.inv_mul
    calc ((tf : AdeleRing (𝓞 K) K)).1
        = ((↑(p⁻¹) : AdeleRing (𝓞 K) K)).1 * (((t : AdeleRing (𝓞 K) K)).1 * ((u : AdeleRing (𝓞 K) K)).1) := rfl
      _ = 1 := by rw [hu1, mul_one, ← hp1, h]
  have htf2 : ∀ w : HeightOneSpectrum (𝓞 K),
      ((tf : AdeleRing (𝓞 K) K)).2 w = ((t : AdeleRing (𝓞 K) K)).2 w * ((u : AdeleRing (𝓞 K) K)).2 w := by
    intro w
    show ((↑(p⁻¹) : AdeleRing (𝓞 K) K) * ((t : AdeleRing (𝓞 K) K) * (u : AdeleRing (𝓞 K) K))).2 w = _
    show ((↑(p⁻¹) : AdeleRing (𝓞 K) K)).2 w * (((t : AdeleRing (𝓞 K) K)).2 w * ((u : AdeleRing (𝓞 K) K)).2 w) = _
    rw [hpinv2, one_mul]
  have htfS : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((tf : AdeleRing (𝓞 K) K)).2 w = 1 := fun w hw => by
    rw [htf2, htS w hw, huS w hw, one_mul]
  have htfv : ∀ v ∈ S, Valued.v (((tf : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := fun v hv => by
    rw [htf2, map_mul, huv, mul_one, htv v hv]

  have hsplit : t * u = p * tf := by rw [htf, mul_inv_cancel_left]
  have hcomm : diagOne tf * adelicArchGLIncl K a = adelicArchGLIncl K a * diagOne tf :=
    (mul_comm_of_glArch_eq_one_of_glFin_eq_one K (UnipotentDepth.glArch_diagOne_eq_one K tf htf1)
      (glFin_adelicArchGLIncl K a))
  have hre : diagOne (t * u) * adelicArchGLIncl K a * κ =
      (diagOne p * adelicArchGLIncl K a) * (diagOne tf * κ) := by
    rw [hsplit, map_mul, mul_assoc (diagOne p), hcomm]
    simp only [mul_assoc]
  obtain ⟨⟨g, hg, heq⟩, -⟩ := hJ (diagOne p * adelicArchGLIncl K a) tf htf1 htfS htfv
  refine ⟨g, hg, ?_⟩
  rw [hre, heq, mul_assoc]


/-! ### Shell surgery on the unipotent average

The pin's `T3` and `T4`: the coefficient of the unipotent average `x` at an archimedean-only element
is the shell character times the coefficient of `x₀`, and hence the squared coefficient on the
shell is bounded by the shell indicator times the coefficient of `x₀` at `diagOne (t * u)`. -/

theorem T3_surgeryArch (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (κ : AdelicGL2 (𝓞 K) K)
    (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ)
    (hysupp : ∀ i, (y i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (y i).2 v = 0)
    (hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (y i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (y i) * κ)))
    (a : GL (Fin 2) (InfiniteAdeleRing K)) (t : (AdeleRing (𝓞 K) K)ˣ) :
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * adelicArchGLIncl K a) =
      (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * adelicArchGLIncl K a * κ) := by
  have hga : glFin (𝓞 K) K (adelicArchGLIncl K a) = 1 := glFin_adelicArchGLIncl K a
  have hxfun : (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (y i) * κ)) = x := by
    funext g
    rw [hxsum g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc]
  have hcomm : ∀ i, adelicArchGLIncl K a * unipotentGL2 (y i) = unipotentGL2 (y i) * adelicArchGLIncl K a := fun i =>
    (mul_comm_of_glArch_eq_one_of_glFin_eq_one K (glArch_unipotentGL2_eq_one K (y i) (hysupp i).1) hga).symm
  have hmul := hWmult t (adelicArchGLIncl K a) hcomm
  rw [hxfun] at hmul
  rw [hmul, whittakerCoefficient_mul_right K _ _ x₀ 1 (diagOne t * adelicArchGLIncl K a) κ]

theorem T4_boxShell (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (κ : AdelicGL2 (𝓞 K) K)
    (aexp : HeightOneSpectrum (𝓞 K) → ℤ)
    (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ) (m : ℕ)
    (hysupp : ∀ i, (y i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (y i).2 v = 0)
    (hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (y i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
    (hμbox : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
    (hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (y i) * κ)))
    (a : GL (Fin 2) (InfiniteAdeleRing K)) (ha : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl a))
    (u : (AdeleRing (𝓞 K) K)ˣ) (hu : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K)).2 v) = 1)
    (t : (AdeleRing (𝓞 K) K)ˣ) :
    ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne (t * u) * adelicArchGLIncl K a)‖ ≤
      (if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then (1 : ℝ) else 0) *
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (t * u) * adelicArchGLIncl K a * κ)‖ := by
  have hT3 := T3_surgeryArch K S D₀ x₀ κ r y cs hysupp hWmult x hxsum a (t * u)
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((((t * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) := fun v => by
    rw [show (((t * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = ((t : AdeleRing (𝓞 K) K)).2 v * ((u : AdeleRing (𝓞 K) K)).2 v from rfl,
      Valuation.map_mul, hu v, mul_one]
  have hga : glFin (𝓞 K) K (adelicArchGLIncl K a) = 1 := glFin_adelicArchGLIncl K a
  have harch : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (adelicArchGLIncl K a))) := by
    intro pl
    rw [glArch_adelicArchGLIncl]
    exact ha pl
  by_cases hbox : ∀ v ∈ S, Valued.v ((((t * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) ≤
      ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  ·
    have hμ := hμbox (t * u) hbox
    by_cases hshell : ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
        ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    · have hshell' : ∀ v ∈ S, Valued.v ((((t * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
        fun v hv => (hval v).trans (hshell v hv)
      rw [ite_eq_left hshell'] at hμ
      rw [ite_eq_left hshell, hT3, hμ, one_mul, one_mul]
    · have hshell' : ¬ ∀ v ∈ S, Valued.v ((((t * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
        fun h => hshell fun v hv => (hval v).symm.trans (h v hv)
      rw [ite_eq_right hshell'] at hμ
      rw [ite_eq_right hshell, hT3, hμ, zero_mul, zero_mul, norm_zero]
  ·
    push Not at hbox
    have h0 := hboxvan (adelicArchGLIncl K a) hga harch (t * u) hbox
    rw [hT3, h0, mul_zero, norm_zero]
    split_ifs
    · rw [one_mul]
    · rw [zero_mul]


/-! ### The torus at `S`: the Iwasawa surgery

The pin's `RS27.torus_at_S`. For `W` a unipotent-covariant, central-character function and
`k ∈ maximalCompactAt F S` with the shell inequality on `S`, the value `W (diagOne t * k)` is the
character at a fixed `β` times the central character at a unit `D` times the value at
`diagOne (t * u) * (k * (finEmbed (glFin k))⁻¹)` — the `u` being a unit everywhere and `1` outside
`S`. The proof strips `k` of its finite part at `S` along a lower-unipotent element, splits the
resulting Borel element into unipotent × centre × torus, and reads off the three factors. -/

open AdelicDock in
theorem torus_at_S
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (n : ℕ)
    (hinv : ∀ (γ : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), γ.1 = 0 →
      (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → γ.2 w = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤ ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      W (g * lowerUnipotentGL2 γ) = W g)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ maximalCompactAt F S)
    (hsupp : ∀ v ∈ S,
      Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v) ≤
        Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v) *
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ (u D : (AdeleRing (𝓞 F) F)ˣ) (β : AdeleRing (𝓞 F) F),
      ((u : AdeleRing (𝓞 F) F)).1 = 1 ∧ (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ((u : AdeleRing (𝓞 F) F)).2 w = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (((u : AdeleRing (𝓞 F) F)).2 v) = 1) ∧
      ((D : AdeleRing (𝓞 F) F)).1 = 1 ∧ (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ((D : AdeleRing (𝓞 F) F)).2 w = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (((D : AdeleRing (𝓞 F) F)).2 v) = 1) ∧
      ∀ t : (AdeleRing (𝓞 F) F)ˣ,
        W (diagOne t * k) = ψ ((t : AdeleRing (𝓞 F) F) * β) * ((ω D : ℂˣ) : ℂ) *
          W (diagOne (t * u) * (k * (finEmbed (𝓞 F) F (glFin (𝓞 F) F k))⁻¹)) := by
  classical
  have hkK : k ∈ adelicMaximalCompact F := maximalCompactAt_le F S hk
  have hkoff : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → finComponent (𝓞 F) F w (glFin (𝓞 F) F k) = 1 :=
    (mem_maximalCompactAt_iff.mp hk).2

  have hent : ∀ (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)),
      ((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) v := by
    intro g i j v; rw [finComponent_apply, glFin_apply]
  have hent1 : ∀ (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2),
      ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1) := by
    intro g i j; rw [glArch_apply]
  have hint : ∀ (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)),
      Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) v) ≤ 1 := by
    intro i j v; rw [← hent]; exact (valued_finComponent_apply_le_one hkK v i j).1
  have hc_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) w = 0 := by
    intro w hw; rw [← hent, hkoff w hw, Units.val_one, Matrix.one_apply_ne (by decide)]
  have hd_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) w = 1 := by
    intro w hw; rw [← hent, hkoff w hw, Units.val_one, Matrix.one_apply_eq]
  have hexp_le : ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]; omega

  have hd_S : ∀ v ∈ S, Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v) = 1 := by
    intro v hv
    apply le_antisymm (hint 1 1 v)
    have hdet := valued_det_finComponent_eq_one hkK v
    rw [Matrix.det_fin_two, hent, hent, hent, hent] at hdet
    have hcd : Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v) ≤
        Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v) :=
      (hsupp v hv).trans (mul_le_of_le_one_right' hexp_le)
    rw [← hdet]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
    · exact mul_le_of_le_one_left' (hint 0 0 v)
    · exact (mul_le_of_le_one_left' (hint 0 1 v)).trans hcd
  have hd_all : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v) = 1 := by
    intro v; by_cases hv : v ∈ S
    · exact hd_S v hv
    · rw [hd_off v hv, map_one]
  have hd_ne : ∀ v : HeightOneSpectrum (𝓞 F), (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v ≠ 0 := by
    intro v h; have h1 := hd_all v; rw [h, map_zero] at h1; exact zero_ne_one h1

  set γloc : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun v =>
    (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v *
      ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v)⁻¹ with hγloc
  have hγint : ∀ v : HeightOneSpectrum (𝓞 F), γloc v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hγloc]
    dsimp only
    rw [map_mul, map_inv₀, hd_all, inv_one, mul_one]
    exact hint 1 0 v
  set γ : AdeleRing (𝓞 F) F := ((0 : InfiniteAdeleRing F), finAdeleOf F γloc hγint) with hγdef
  have hγ1 : γ.1 = 0 := rfl
  have hγ2 : ∀ v : HeightOneSpectrum (𝓞 F), γ.2 v = γloc v := fun v => rfl
  have hγoff : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → γ.2 w = 0 := by
    intro w hw; rw [hγ2, hγloc]; dsimp only; rw [hc_off w hw, zero_mul]
  have hγS : ∀ v ∈ S, Valued.v (γ.2 v) ≤
      ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro v hv
    rw [hγ2, hγloc]; dsimp only
    rw [map_mul, map_inv₀, hd_S v hv, inv_one, mul_one]
    have h := hsupp v hv
    rwa [hd_S v hv, one_mul] at h

  set kfin : AdelicGL2 (𝓞 F) F := AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F k) with hkfin
  have hkfin_arch : glArch (𝓞 F) F kfin = 1 := AdelicDock.glArch_finEmbed _ _ _
  have hkfin_fin : glFin (𝓞 F) F kfin = glFin (𝓞 F) F k := AdelicDock.glFin_finEmbed _ _ _
  set karch : AdelicGL2 (𝓞 F) F := k * kfin⁻¹ with hkarch
  have hkarch_fin : glFin (𝓞 F) F karch = 1 := by rw [hkarch, map_mul, map_inv, hkfin_fin, mul_inv_cancel]
  have hk_eq : k = karch * kfin := by rw [hkarch, inv_mul_cancel_right]
  set lam : AdelicGL2 (𝓞 F) F := lowerUnipotentGL2 γ with hlam
  have hlam_coe : ((lam : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, 0; γ, 1] := rfl
  have hlaminv_coe : (((lam⁻¹ : AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, 0; -γ, 1] := rfl

  have hgl_ext : ∀ {g h : AdelicGL2 (𝓞 F) F}, glArch (𝓞 F) F g = glArch (𝓞 F) F h →
      (∀ u, finComponent (𝓞 F) F u (glFin (𝓞 F) F g) = finComponent (𝓞 F) F u (glFin (𝓞 F) F h)) → g = h := by
    intro g h h₁ h₂
    apply Units.ext; ext i j; apply Prod.ext
    · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
        (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) h₁) i) j
      rwa [glArch_apply, glArch_apply] at this
    · refine RestrictedProduct.ext _ _ fun u => ?_
      have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (u.adicCompletion F) =>
        (m : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) (h₂ u)) i) j
      rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

  have hlam_arch : glArch (𝓞 F) F lam = 1 := by
    apply Units.ext; ext i j
    rw [hent1, hlam_coe, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [hγ1] <;> rfl
  have hlam_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → finComponent (𝓞 F) F w (glFin (𝓞 F) F lam) = 1 := by
    intro w hw
    apply Units.ext; ext i j
    rw [hent, hlam_coe, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [hγoff w hw] <;> rfl
  have hlam_K : lam ∈ adelicMaximalCompact F := by
    refine ⟨mem_finiteIntegralGL2_iff.mpr ⟨fun i j w => ?_, fun i j w => ?_⟩, fun w' => ?_⟩
    · rw [glFin_apply, hlam_coe]
      fin_cases i <;> fin_cases j
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
      · show (0 : AdeleRing (𝓞 F) F).2 w ∈ _; exact zero_mem _
      · show γ.2 w ∈ _; exact hγint w
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
    · rw [← map_inv, glFin_apply, hlaminv_coe]
      fin_cases i <;> fin_cases j
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
      · show (0 : AdeleRing (𝓞 F) F).2 w ∈ _; exact zero_mem _
      · show (-γ).2 w ∈ _; exact neg_mem (hγint w)
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
    · rw [hlam_arch, map_one]; exact isRowIsometry_one
  set βm : AdelicGL2 (𝓞 F) F := kfin * lam⁻¹ with hβm
  have hkfin_K : kfin ∈ adelicMaximalCompact F :=
    ⟨by rw [hkfin_fin]; exact hkK.1, fun w => by rw [hkfin_arch, map_one]; exact isRowIsometry_one⟩
  have hβm_K : βm ∈ adelicMaximalCompact F := mul_mem hkfin_K (inv_mem hlam_K)
  have hβm_arch : glArch (𝓞 F) F βm = 1 := by rw [hβm, map_mul, map_inv, hkfin_arch, hlam_arch, inv_one, mul_one]
  have hβm_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → finComponent (𝓞 F) F w (glFin (𝓞 F) F βm) = 1 := by
    intro w hw; rw [hβm, map_mul, map_inv, map_mul, map_inv, hkfin_fin, hkoff w hw, hlam_off w hw, inv_one, mul_one]
  have h1arch : ∀ i : Fin 2, ((((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i)).1 = 1 := by
    intro i; rw [← hent1, hβm_arch, Units.val_one, Matrix.one_apply_eq]
  have h1off : ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 F)), w ∉ S →
      ((((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i)).2 w = 1 := by
    intro i w hw; rw [← hent, hβm_off w hw, Units.val_one, Matrix.one_apply_eq]

  have hβ10 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := by
    apply Prod.ext
    · rw [← hent1, hβm_arch, Units.val_one, Matrix.one_apply_ne (by decide)]; rfl
    · refine RestrictedProduct.ext _ _ fun v => ?_
      have h1 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 =
          ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 * 1 +
          ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 * (-γ) := by
        rw [hβm, Units.val_mul, hlaminv_coe, Matrix.mul_apply, Fin.sum_univ_two]
        simp
      have hk10 : evalAt F v ((((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0)) =
          (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v := by rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
      have hk11 : evalAt F v ((((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)) =
          (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v := by rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
      have hγv : evalAt F v γ = γloc v := rfl
      show evalAt F v ((((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0)) = evalAt F v 0
      rw [h1, map_add, map_mul, map_mul, map_one, map_neg, map_zero, hk10, hk11, hγv, hγloc]
      dsimp only
      rw [mul_one, mul_neg, ← mul_assoc, mul_comm ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v),
        mul_assoc, mul_inv_cancel₀ (hd_ne v), mul_one, add_neg_cancel]
  have hβ : βm ∈ adelicBorel (𝓞 F) F := hβ10
  have hkf00 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
  have hkf01 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
  have hkf10 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
  have hkf11 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]

  set Bel : ↥(adelicBorel (𝓞 F) F) := ⟨βm, hβ⟩ with hBel
  set t₁ : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst Bel with ht₁
  set t₂ : (AdeleRing (𝓞 F) F)ˣ := borelDiagSnd Bel with ht₂
  set βad : AdeleRing (𝓞 F) F :=
    ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 *
      ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) with hβad
  have h00 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (t₁ : AdeleRing (𝓞 F) F) := rfl
  have h11 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = (t₂ : AdeleRing (𝓞 F) F) := rfl
  have ht2inv : ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (t₂ : AdeleRing (𝓞 F) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcs := centralScalar_coe_eq F t₂
  have hdo : ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := by
    rw [diagOne_coe_eq, Units.val_mul]
  have hx00 : (t₂ : AdeleRing (𝓞 F) F) * ((t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      = (t₁ : AdeleRing (𝓞 F) F) := by
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hβ01 : βad * (t₂ : AdeleRing (𝓞 F) F)
      = ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 := by
    rw [hβad, mul_assoc, ht2inv, mul_one]
  have hR : ((unipotentGL2 βad : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F), βad * (t₂ : AdeleRing (𝓞 F) F); 0, (t₂ : AdeleRing (𝓞 F) F)] := by
    rw [hcs, hdo, unipotentGL2_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add, hx00]
  have hdecomp : βm = unipotentGL2 βad * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) := by
    apply Units.ext
    change ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ((unipotentGL2 βad : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    rw [hR, hβ01]
    conv_lhs => rw [Matrix.eta_fin_two ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))]
    rw [h00, h11, hβ10]

  have hcomm_fa : ∀ {a b : AdelicGL2 (𝓞 F) F}, glArch (𝓞 F) F a = 1 → glFin (𝓞 F) F b = 1 → a * b = b * a := by
    intro a b ha hb
    exact hgl_ext (by rw [map_mul, map_mul, ha, one_mul, mul_one])
      (fun u => by rw [map_mul, map_mul, map_mul, map_mul, hb, map_one, mul_one, one_mul])
  have hdn := diagOne_mul_unipotentGL2 F
  have hdz := diagOne_mul_centralScalar F

  have hkβ : k = karch * βm * lam := by
    rw [hβm, hkarch]; simp only [mul_assoc, inv_mul_cancel, inv_mul_cancel_left, mul_one]
  have hmain : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      W (diagOne t * k) = ψ ((t : (AdeleRing (𝓞 F) F)) * βad) * ((ω t₂ : ℂˣ) : ℂ) *
        W (diagOne (t * (t₁ * t₂⁻¹)) * karch) := by
    intro t
    have e1 : diagOne t * k = (diagOne t * βm * karch) * lam := by
      rw [hkβ, ← hcomm_fa hβm_arch hkarch_fin]; simp only [mul_assoc]
    have e2 : diagOne t * (unipotentGL2 βad * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹)) * karch =
        unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * (diagOne (t * (t₁ * t₂⁻¹)) * karch)) := by
      calc diagOne t * (unipotentGL2 βad * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹)) * karch
          = (diagOne t * unipotentGL2 βad) * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) * karch := by
            simp only [mul_assoc]
        _ = (unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * diagOne t) * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) * karch := by
            rw [hdn]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (diagOne t * centralScalar (𝓞 F) F t₂) * diagOne (t₁ * t₂⁻¹) * karch := by
            simp only [mul_assoc]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * diagOne t) * diagOne (t₁ * t₂⁻¹) * karch := by
            rw [hdz]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * ((diagOne t * diagOne (t₁ * t₂⁻¹)) * karch)) := by
            simp only [mul_assoc]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * (diagOne (t * (t₁ * t₂⁻¹)) * karch)) := by
            rw [← map_mul]
    rw [e1, hinv γ (diagOne t * βm * karch) hγ1 hγoff hγS, hdecomp, e2, hN, hZ]
    ring

  have hval : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((t₁ : (AdeleRing (𝓞 F) F))).2 v) = 1 ∧ Valued.v (((t₂ : (AdeleRing (𝓞 F) F))).2 v) = 1 := by
    intro v
    have hγv : evalAt F v γ = γloc v := rfl

    have e00 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 * 1 + ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 * (-γ) := by
      rw [hβm, Units.val_mul, hlaminv_coe, Matrix.mul_apply, Fin.sum_univ_two]; simp
    have e11 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 * 0 + ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 * 1 := by
      rw [hβm, Units.val_mul, hlaminv_coe, Matrix.mul_apply, Fin.sum_univ_two]; simp
    have ht2 : ((t₂ : (AdeleRing (𝓞 F) F))).2 v = ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v := by
      show evalAt F v (((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) = _
      rw [e11, map_add, map_mul, map_mul, map_zero, map_one, hkf10 v, hkf11 v, mul_zero, zero_add, mul_one]
    have hdet := valued_det_finComponent_eq_one hkK v
    rw [Matrix.det_fin_two, hent, hent, hent, hent] at hdet
    have ht1 : ((t₁ : (AdeleRing (𝓞 F) F))).2 v =
        (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 v * ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v - ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2 v * ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v) * (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v)⁻¹ := by
      show evalAt F v (((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0) = _
      rw [e00, map_add, map_mul, map_mul, map_one, map_neg, hkf00 v, hkf01 v, hγv, hγloc]
      dsimp only
      field_simp [hd_ne v]
      ring
    refine ⟨?_, ?_⟩
    · rw [ht1, map_mul, map_inv₀, hdet, hd_all v, inv_one, mul_one]
    · rw [ht2, hd_all v]

  have hinv_fst : ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).1 = 1 := by
    have h := congrArg Prod.fst (Units.inv_mul t₂)
    change ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).1 * ((t₂ : (AdeleRing (𝓞 F) F))).1 = (1 : (AdeleRing (𝓞 F) F)).1 at h
    rw [show ((t₂ : (AdeleRing (𝓞 F) F))).1 = 1 from h1arch 1, mul_one] at h
    exact h
  have hinv_snd : ∀ w : HeightOneSpectrum (𝓞 F),
      ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).2 w * ((t₂ : (AdeleRing (𝓞 F) F))).2 w = 1 := by
    intro w
    have h := congrArg (fun x : (AdeleRing (𝓞 F) F) => x.2 w) (Units.inv_mul t₂)
    exact h
  refine ⟨t₁ * t₂⁻¹, t₂, βad, ?_, ?_, ?_, h1arch 1, fun w hw => h1off 1 w hw, fun v => (hval v).2, hmain⟩
  · show ((t₁ : (AdeleRing (𝓞 F) F))).1 * ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).1 = 1
    rw [show ((t₁ : (AdeleRing (𝓞 F) F))).1 = 1 from h1arch 0, hinv_fst, mul_one]
  · intro w hw
    show ((t₁ : (AdeleRing (𝓞 F) F))).2 w * ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).2 w = 1
    have h := hinv_snd w
    rw [show ((t₂ : (AdeleRing (𝓞 F) F))).2 w = 1 from h1off 1 w hw, mul_one] at h
    rw [show ((t₁ : (AdeleRing (𝓞 F) F))).2 w = 1 from h1off 0 w hw, h, mul_one]
  · intro v
    show Valued.v (((t₁ : (AdeleRing (𝓞 F) F))).2 v * ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).2 v) = 1
    have h := congrArg Valued.v (hinv_snd v)
    rw [map_mul, (hval v).2, mul_one, map_one] at h
    rw [map_mul, (hval v).1, h, mul_one]


/-! ### The torus norm is the archimedean translate

The pin's `T2_torusNorm`: the torus surgery of `torus_at_S` preserves the *norm* of the coefficient
once the character has norm one and the central character has the `ideleNorm` law — the two scalar
factors drop out. -/

theorem T2_torusNorm (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (hω : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
    (n : ℕ)
    (hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)
    (k₁ : AdelicGL2 (𝓞 K) K) (hk₁ : k₁ ∈ maximalCompactAt K S)
    (hsupp : ∀ v ∈ S, Valued.v (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
        Valued.v (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ u : (AdeleRing (𝓞 K) K)ˣ, ((u : AdeleRing (𝓞 K) K)).1 = 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K)).2 v) = 1) ∧
      ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k₁)‖ =
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne (t * u) * adelicArchGLIncl K (glArch (𝓞 K) K k₁))‖ := by
  set pins := productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K) with hpins
  set ψ := NumberField.StandardAddChar.stdAddChar K with hψdef
  have hψ : IsGlobalAddChar K ψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K
  set W : AdelicGL2 (𝓞 K) K → ℂ := fun g => whittakerCoefficient K pins ψ x 1 g with hW

  have hper : ∀ (g : AdelicGL2 (𝓞 K) K) (β : K) (u : AdeleRing (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = x (unipotentGL2 u * g) := by
    intro g β u
    rw [unipotentGL2_add, mul_assoc, T2_unipotentGL2_algebraMap_eq_globalPoints, hxG]
  have hN : ∀ (u : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), W (unipotentGL2 u * g) = ψ u * W g := by
    intro u g
    have h := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D₀
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ψ hψ.principalInvariant
      x g (hper g) 1 u
    simpa only [hW, hpins, map_one, one_mul] using h

  have hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      W (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * W g := by
    intro z g
    simp only [hW]
    rw [← T2_centralScalar_comm K z g]
    exact T2_whittakerCoefficient_mul_central K pins ψ x 1 g (centralScalar (𝓞 K) K z) _
      (fun h => T2_centralScalar_comm K z h) (hxZ z)

  have hinv : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → γ.2 w = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤ ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      W (g * lowerUnipotentGL2 γ) = W g := by
    intro γ g h1 h2 h3
    simp only [hW]
    exact whittakerCoefficient_mul_right_eq_of_forall K pins ψ x 1 g (lowerUnipotentGL2 γ)
      (fun y => hxlow γ y h1 h2 h3)
  obtain ⟨u, D, β, hu1, huS, huv, hD1, -, hDv, hWeq⟩ :=
    torus_at_S K S W ψ ω hN hZ n hinv k₁ hk₁ hsupp
  refine ⟨u, hu1, huS, huv, fun t => ?_⟩
  have h := hWeq t
  simp only [hW] at h
  rw [h, norm_mul, norm_mul, norm_apply_eq_one_of_isGlobalAddChar K hψ, hω D,
    T2_ideleNorm_eq_one K D hD1 hDv, Real.one_rpow, one_mul, one_mul,
    mul_inv_finEmbed_glFin_eq_adelicArchGLIncl]

end ShellSurgery

/-! ## The row -/

set_option linter.unusedVariables false in
theorem exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))
      (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hω : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥)
      (_hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (_hWpt : whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t₀ * k₀) ≠ 0)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))
      (aexp : HeightOneSpectrum (𝓞 K) → ℤ)
      (_haexp : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) =
        ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))

      (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ) (m : ℕ)
      (_hysupp : ∀ i, (y i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (y i).2 v = 0)
      (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (y i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
      (_hμbox : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
      (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (y i) * κ)))
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφval : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          φ s k = 0 ∨ φ s k = 1)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (hsec : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        φ s (diagOne t * k) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s k),
    (∃ J : Finset (AdelicGL2 (𝓞 K) K), (∀ g ∈ J, glArch (𝓞 K) K g = 1) ∧
      ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1) →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k)‖ ^ 2 * ‖φ s (diagOne t * k)‖ ≤
          (if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then (1 : ℝ) else 0) *
            NumberField.TateGlobal.ideleNorm K t ^ (s.re + 1 / 2) *
            ∑ g ∈ J, ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * g)‖ ^ 2)
  := by
  intro α hα S D₀ ω w _hω x₀ N _hN _hx₀lev t₀ _ht₀ k₀ _hk₀ _hWpt κ _hκ aexp _haexp r y cs m _hysupp _hWmult _hμbox _hboxvan x _hxsum _hxG _hxZ _hxKS n _hn _hxlow φ _hφ _hφKS _hφval _hφsupp hsec
  have hκarch : glArch (𝓞 K) K κ = 1 := by rw [_hκ, AdelicDock.glArch_finEmbed]
  obtain ⟨J, hJarch, hJ⟩ := ShellSurgery.C1_cover K S D₀ x₀ N _hN _hx₀lev κ hκarch aexp
  refine ⟨J, hJarch, ?_⟩
  intro s k hk t htS

  have hsum0 : 0 ≤ ∑ g ∈ J, ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * g)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm0 : 0 ≤ NumberField.TateGlobal.ideleNorm K t ^ (s.re + 1 / 2) :=
    Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos (F := K) t).le _

  obtain ⟨hφle, hφsupp'⟩ := ShellSurgery.T5_sectionNorm K S n φ _hφval _hφsupp hsec s k hk t
  by_cases hφ0 : φ s (diagOne t * k) = 0
  · rw [hφ0, norm_zero, mul_zero]
    split_ifs
    · rw [one_mul]; exact mul_nonneg hnorm0 hsum0
    · rw [zero_mul, zero_mul]
  have hsuppk := hφsupp' hφ0

  obtain ⟨k₁, k₂, hk₁, hk₂, hk12, hk₁arch, hk₁S⟩ := ShellSurgery.T1_strip K S k hk
  have hWk : whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k) = whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k₁) := by
    rw [hk12, ← mul_assoc]
    exact ShellSurgery.whittakerCoefficient_mul_right_eq_of_forall K _ _ x 1 _ k₂ (fun g => _hxKS k₂ hk₂ g)
  have hsuppk₁ : ∀ v ∈ S, Valued.v (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
      Valued.v (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro v hv
    rw [hk₁S 1 0 v hv, hk₁S 1 1 v hv]
    exact hsuppk v hv

  obtain ⟨u, hu1, huS, huv, hWu⟩ := ShellSurgery.T2_torusNorm K S D₀ ω w _hω x _hxG _hxZ n _hxlow k₁ hk₁ hsuppk₁
  rw [hk₁arch] at hWu

  have harch : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k)) :=
    (mem_adelicMaximalCompact_iff.mp hk).2
  have hbox := ShellSurgery.T4_boxShell K S D₀ x₀ κ aexp r y cs m _hysupp _hWmult _hμbox _hboxvan x _hxsum
    (glArch (𝓞 K) K k) harch u huv t
  have hchain : ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k)‖ ≤ (if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then (1 : ℝ) else 0) * ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (t * u) * adelicArchGLIncl K (glArch (𝓞 K) K k) * κ)‖ := by
    rw [hWk, hWu t]
    exact hbox
  by_cases hshell : ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  · rw [ite_eq_left hshell, one_mul] at hchain ⊢
    obtain ⟨g, hgJ, hg⟩ := hJ (glArch (𝓞 K) K k) t u htS hu1 huS huv hshell
    rw [hg] at hchain
    have hsq : ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k)‖ ^ 2 ≤
        ∑ g ∈ J, ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * g)‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hchain 2).trans
        (Finset.single_le_sum (f := fun g => ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * g)‖ ^ 2)
          (fun _ _ => sq_nonneg _) hgJ)
    calc _ ≤ (∑ g ∈ J, ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * g)‖ ^ 2) *
          NumberField.TateGlobal.ideleNorm K t ^ (s.re + 1 / 2) :=
        mul_le_mul hsq hφle (norm_nonneg _) hsum0
      _ = _ := by rw [mul_comm]
  · rw [ite_eq_right hshell, zero_mul] at hchain
    rw [ite_eq_right hshell, zero_mul, zero_mul]
    have h0 : ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k)‖ = 0 := le_antisymm hchain (norm_nonneg _)
    rw [h0]
    simp

end RankinSelberg

end AutomorphicForm

end
