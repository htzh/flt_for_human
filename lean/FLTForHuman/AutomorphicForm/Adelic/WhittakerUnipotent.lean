/-
  The unipotent-integral form of the unfolding identity, and the Bessel bound over the units.

  `AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le`:
  for two functions `x y` on the adelic `GL₂` left-invariant under `GL₂(F)`, with `x` vanishing at
  the zero parameter and `y` continuous on every unipotent slice, the integral of `x · conj y` along
  the unipotent slice against the box-normalized measure is the `tsum` over the units `Fˣ` of the
  products `W x (a) · conj (W y (a))` of Whittaker coefficients read at `diagOne a`; that product of
  norms is summable and its `tsum` is bounded by `√(∫ ‖x‖²) · √(∫ ‖y‖²)` — Bessel on each factor,
  termwise Cauchy–Schwarz. The `Fˣ → F` reading needs `x` to vanish at `0` (so that the support of
  the product sits in the image of the units) and `y` bounded on the slice (the pin's
  `slice_bounded`, from a compact box containing a full set of representatives and the periodicity
  `slice_periodic`). `continuous_unipotentGL2` and `globalPoints_unipotentGL2` are the slice
  continuity and the compatibility of `globalPoints` with the unipotent embedding.

  Transcribed from the pin (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le.lean`
  (216 lines; 6 public declarations — `continuous_unipotentGL2`, `globalPoints_unipotentGL2`,
  `slice_periodic`, `slice_bounded`, `main` and the `solution` that becomes this module's row — and
  no `private` declaration), whose `Theorems/` wrapper carries the row at its line 23. The row's
  three premises are the landed
  `integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj` (`WhittakerPositivity.lean`), the
  `whittakerCoefficient_eq_…_diagOne_mul` identity and
  `sum_norm_whittakerCoefficient_sq_le_integral_norm_sq` (`WhittakerCoefficient.lean`,
  `BesselInequality.lean`).

  spec-pin: P2M/Sol/S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le.lean

  ## Port deltas

  * `import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup` is added to the three premise modules:
    the pin's `globalPoints_unipotentGL2` proof rewrites with `globalPoints_apply`, which lives there
    (`AutomorphicForm.globalPoints_apply`, the port of the pin's
    `Definitions/Def_AutomorphicForm_BorelSubgroup.lean` import) and not in the three. The pin's
    other definition imports (Whittaker coefficient, production pins general, adèlic box, adèlic
    level) arrive through the three.
  * `continuous_unipotentGL2` is **not** redeclared. `AutomorphicForm.continuous_unipotentGL2`
    already exists in the import closure (`ConstantTerm.lean`, ported from
    `S_AutomorphicForm_continuous_unipotentGL2.lean`) at the general ring, and the pin's copy is its
    instance at `AdeleRing (𝓞 F) F`; the module body calls it at
    `R := AdeleRing (𝓞 F) F` and `scaffold_audit` reports the pin's declaration as satisfied by the
    import closure.
  * The pin's `namespace FibreParsevalC9B` (its search-stage label) is dropped, as ordered: the
    declarations sit at `AutomorphicForm.*`, and the pin's `solution` is the row at the graph node's
    name. The pin's `p2m_open`/`p2m_export` are not ported; `open NumberField.AdelicLevel` supplies
    the pin's `diagOne` unqualified.
  * The pin's two `attribute [local instance]` lines (`adeleBorel`, `borelSpace_adeleBorel`) are
    kept, as the module's proofs and the `ν`-integrals need them; the pin's `attribute [-instance]`
    / `attribute [-simp]` heads are dropped (they belong to the pin's `RestrictedProduct`
    vocabulary, which the row does not touch).
  * Body-only: the row's body calls the pin's `main` unqualified instead of
    `AutomorphicForm.FibreParsevalC9B.main`.
  * `main` and the row carry the pin's **own** duplicate statement — the pin's `main` (`:67`) and
    its `solution` (`:182`) are one proposition — so `dedup.py --within` reports exactly that one
    cluster (38 lines). It is kept: the pin declares both, and the row's body is the pin's
    `solution`, the wrapper glue over `main`.

  ## Heartbeat probe

  Never installed (this module sets no `maxHeartbeats`). Probed with

      lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/AutomorphicForm/Adelic/WhittakerUnipotent.lean

  silent at `N = 8000` and failing at `N = 7000` — there with `(deterministic) timeout at whnf` at
  `:209`, the `simp only` closing the row's `tsum_congr`, and from `N = 6500` down as a
  declaration-level timeout at `:102` (`main`). The module is silent at the project cap
  (`maxHeartbeats = 4000000`) with a wide margin, so the probe is a measurement, not a limit.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerPositivity
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.BesselInequality
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open scoped ENNReal NNReal ComplexConjugate

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

section

variable (F : Type) [Field F] [NumberField F]

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem slice_periodic (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g : AdelicGL2 (𝓞 F) F) (β : F) (u : AdeleRing (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ]

theorem slice_bounded (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : AdeleRing (𝓞 F) F => φ (unipotentGL2 u * g))
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g)) :
    ∃ C : ℝ, ∀ u : AdeleRing (𝓞 F) F, ‖φ (unipotentGL2 u * g)‖ ≤ C := by
  obtain ⟨K, hK, hbox⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨β, hβ, -⟩ := existsUnique_algebraMap_add_mem_adelicBox F u
  rw [← hper β u]
  exact hC _ (hbox hβ)

theorem main
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      x (globalPoints (𝓞 F) F γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      y (globalPoints (𝓞 F) F γ * g) = y g)
    (hxc : Continuous x) (hyc : Continuous y)
    (hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
    (hxW : ∀ g, Summable fun a : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
    (g : AdelicGL2 (𝓞 F) F) :
    (Summable fun a : Fˣ =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ∧
    (∑' a : Fˣ,
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ≤
      Real.sqrt (∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) *
        Real.sqrt (∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) ∧
    ∫ u, x (unipotentGL2 u * g) * (starRingEnd ℂ) (y (unipotentGL2 u * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' a : Fˣ,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
            (globalPoints (𝓞 F) F (diagOne a) * g) *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
            (globalPoints (𝓞 F) F (diagOne a) * g)) := by
  classical
  set pins := productionPinsOf F D U gen (adelicBox F) with hpins

  have hperx := slice_periodic F x hxG g
  have hpery := slice_periodic F y hyG g
  have hcx : Continuous fun u : AdeleRing (𝓞 F) F => x (unipotentGL2 u * g) :=
    hxc.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)
  have hcy : Continuous fun u : AdeleRing (𝓞 F) F => y (unipotentGL2 u * g) :=
    hyc.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)
  have hbddy := slice_bounded F y g hcy hpery

  have hWx : ∀ a : Fˣ, whittakerCoefficient F pins ψ x (a : F) g =
      whittakerCoefficient F pins ψ x 1 (globalPoints (𝓞 F) F (diagOne a) * g) := by
    intro a
    have h := whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul F D U gen ψ hψ x hxG (a : F)
      a.ne_zero g
    have ha : Units.mk0 (a : F) a.ne_zero = a := Units.ext rfl
    rw [ha] at h
    exact h
  have hWy : ∀ a : Fˣ, whittakerCoefficient F pins ψ y (a : F) g =
      whittakerCoefficient F pins ψ y 1 (globalPoints (𝓞 F) F (diagOne a) * g) := by
    intro a
    have h := whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul F D U gen ψ hψ y hyG (a : F)
      a.ne_zero g
    have ha : Units.mk0 (a : F) a.ne_zero = a := Units.ext rfl
    rw [ha] at h
    exact h

  set X : ℝ := ∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂pins.ν with hX
  set Y : ℝ := ∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂pins.ν with hY
  have hX0 : 0 ≤ X := integral_nonneg fun u => sq_nonneg _
  have hY0 : 0 ≤ Y := integral_nonneg fun u => sq_nonneg _
  set p : Fˣ → ℝ := fun a => ‖whittakerCoefficient F pins ψ x 1 (globalPoints (𝓞 F) F (diagOne a) * g)‖ with hp
  set q : Fˣ → ℝ := fun a => ‖whittakerCoefficient F pins ψ y 1 (globalPoints (𝓞 F) F (diagOne a) * g)‖ with hq
  have hBx : ∀ A : Finset Fˣ, ∑ a ∈ A, p a ^ 2 ≤ X := by
    intro A
    have h := sum_norm_whittakerCoefficient_sq_le_integral_norm_sq F D U gen ψ hψ x g hcx (A.image (Units.val : Fˣ → F))
    rw [Finset.sum_image (fun a _ b _ hab => Units.ext hab)] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) h
    rw [hp, hWx]
  have hBy : ∀ A : Finset Fˣ, ∑ a ∈ A, q a ^ 2 ≤ Y := by
    intro A
    have h := sum_norm_whittakerCoefficient_sq_le_integral_norm_sq F D U gen ψ hψ y g hcy (A.image (Units.val : Fˣ → F))
    rw [Finset.sum_image (fun a _ b _ hab => Units.ext hab)] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) h
    rw [hq, hWy]
  have hnn : ∀ a, 0 ≤ p a * q a := fun a => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound : ∀ A : Finset Fˣ, ∑ a ∈ A, p a * q a ≤ Real.sqrt X * Real.sqrt Y := by
    intro A
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq A p q
    have h2 : (∑ a ∈ A, p a ^ 2) * (∑ a ∈ A, q a ^ 2) ≤ X * Y :=
      mul_le_mul (hBx A) (hBy A) (Finset.sum_nonneg fun a _ => sq_nonneg _) hX0
    calc ∑ a ∈ A, p a * q a = Real.sqrt ((∑ a ∈ A, p a * q a) ^ 2) :=
          (Real.sqrt_sq (Finset.sum_nonneg fun a _ => hnn a)).symm
      _ ≤ Real.sqrt (X * Y) := Real.sqrt_le_sqrt (hcs.trans h2)
      _ = Real.sqrt X * Real.sqrt Y := Real.sqrt_mul hX0 Y
  refine ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound, ?_⟩

  have hP := integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj F D U gen ψ hψ x y g hperx hcx hcy hbddy (hxW g)
  rw [hP]
  set f : F → ℂ := fun α => whittakerCoefficient F pins ψ x α g *
    (starRingEnd ℂ) (whittakerCoefficient F pins ψ y α g) with hf
  have hsupp : Function.support f ⊆ Set.range (Units.val : Fˣ → F) := by
    intro α hα
    by_cases h0 : α = 0
    · exfalso
      apply hα
      rw [hf, h0]
      simp only
      rw [hx0 g, zero_mul]
    · exact ⟨Units.mk0 α h0, rfl⟩
  have key := (Units.val_injective (α := F)).tsum_eq hsupp
  show ∑' α : F, f α = _
  rw [← key]
  exact tsum_congr fun a => by simp only [hf]; rw [hWx, hWy]

end

theorem integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      x (globalPoints (𝓞 F) F γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      y (globalPoints (𝓞 F) F γ * g) = y g)
    (hxc : Continuous x) (hyc : Continuous y)
    (hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
    (hxW : ∀ g, Summable fun a : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
    (g : AdelicGL2 (𝓞 F) F) :
    (Summable fun a : Fˣ =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ∧
    (∑' a : Fˣ,
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ≤
      Real.sqrt (∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) *
        Real.sqrt (∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) ∧
    ∫ u, x (unipotentGL2 u * g) * (starRingEnd ℂ) (y (unipotentGL2 u * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' a : Fˣ,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
            (globalPoints (𝓞 F) F (diagOne a) * g) *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
            (globalPoints (𝓞 F) F (diagOne a) * g)) :=
  main F D U gen ψ hψ x y hxG hyG hxc hyc hx0 hxW g

end AutomorphicForm
