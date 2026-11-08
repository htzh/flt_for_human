/-
  Coset sums of right convolutions.

  Two facts about a right convolution against a coset sum:

  * `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` — for a Hecke coset system `reps` at a place
    `v` whose representatives are pure local matrices, and a `U`-invariant `φ` that is a Hecke
    coset-eigenfunction at `v`, any finite combination `Φ = ∑ c i · rightConv φ f (· * h i)` of right
    convolutions by `v`-central elements is again `v`-invariant, is again a Hecke coset-eigenfunction at
    `v` (same eigenvalue `a`), and is `U`-bi-invariant;
  * `cosetSum_rightConv_of_isLevelSphericalOfType` — for a level-spherical `f` and any double-coset
    transversal `reps` of `g` mod `U`, the coset sum of `rightConv φ f` is the right convolution by the
    coset sum of `φ`: `∑ i rightConv φ f (· * reps i) = rightConv (∑ i φ (· * reps i)) f`.

  These are the two moves that let the Hecke/archimedean-cut arguments push a convolution through a
  coset sum; `rightConv` is the right action, so the two statements are the "eigen" and the "linearity"
  halves of the same bookkeeping.

  The first is transcribed whole from the pin's proof file
  `P2M/Sol/S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps.lean` (pinned
  `aa2d8b3`, 138 lines).  The second keeps the pin's statement and the ~50-line bridge from the pin's
  hypotheses to the general statement (the `IsFactorizableTestFn` decomposition of the level indicator,
  at `Cusp/SpectrumLift.lean`'s `U`), but its ~46-line analytic argument is the one in
  `CuspidalSpectrum.cosetSum_rightConv_eq` — one application, not a second proof (AF dedup wave).

  spec-pin: Theorems/Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps.lean
  spec-pin: Theorems/Thm_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SmoothRealization
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumLift
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.ArchSpherical
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.RepTheory.LocalLanglands.HeckeCosetSystem
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain Matrix
open AutomorphicForm AutomorphicForm.SmoothCusp AutomorphicForm.CuspidalConstituent UnramifiedWhittaker HeckeIntegralSeam
open NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

section PureReps

variable {G : Type*} [Group G]

/-- A right `U`-translate of a Hecke coset system is again one. Pin helper
`P2M/Sol/S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps.lean:20-38`
(`RS11CH.isHeckeCosetSystem_mul_right`). -/
theorem isHeckeCosetSystem_mul_right {U : Subgroup G} {gv : G} {ι : Type*}
    {reps : ι → G} (hsys : IsHeckeCosetSystem U gv reps) {u : G} (hu : u ∈ U) :
    IsHeckeCosetSystem U gv (fun i => reps i * u) where
  mem_doubleCoset i := HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) hu
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers (x * u⁻¹) (HeckePair.doubleCoset_mul_mem hx (inv_mem hu))
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have : x⁻¹ * (reps i * u) = u⁻¹ * ((x * u⁻¹)⁻¹ * reps i) * u := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hu) hi) hu
  mk_injective i j hij := by
    apply hsys.mk_injective
    have hij' : (QuotientGroup.mk (reps i * u) : G ⧸ U) = QuotientGroup.mk (reps j * u) := hij
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [QuotientGroup.eq] at hij' ⊢
    have : (reps i)⁻¹ * reps j = u * ((reps i * u)⁻¹ * (reps j * u)) * u⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hu hij') (inv_mem hu)

end PureReps

theorem heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hUv : ∀ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) ∈ U)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K)
    (hsys : IsHeckeCosetSystem U (heckeGen (𝓞 K) K v) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), reps j = placeEmbed K v m)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (a : ℂ) (hφT : IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v φ a)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
      z = z₁ * z₂ ∧ z₂ ∈ U ∧ ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * placeEmbed K v xv = placeEmbed K v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => φ (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K))
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (c : Fin n → ℂ)
    (hh : ∀ i, ∀ xv : GL (Fin 2) (v.adicCompletion K), h i * placeEmbed K v xv = placeEmbed K v xv * h i) :
    let Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i, c i * rightConv K φ f (g * h i)
    (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      Φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Φ g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps Φ g = a * Φ g) ∧
    IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v Φ a := by
  classical
  intro Φ

  obtain ⟨reps', hsys', hT'⟩ := hφT
  have hT : ∀ g : AdelicGL2 (𝓞 K) K, ∑ j, φ (g * reps j) = a * φ g := by
    intro g
    rw [HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys' hsys hφU g]
    exact hT' g

  choose mrep hmrep using hpure

  have hkey : ∀ g z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∑ j, φ (g * reps j * z) = a * φ (g * z) := by
    intro g z hz
    obtain ⟨z₁, z₂, rfl, hz₂, hcomm⟩ := hsupp z hz
    have h1 : ∀ j, g * reps j * (z₁ * z₂) = (g * z₁) * (reps j * z₂) := by
      intro j
      rw [hmrep j, show g * placeEmbed K v (mrep j) * (z₁ * z₂) = g * (placeEmbed K v (mrep j) * z₁) * z₂ by group,
        ← hcomm (mrep j)]
      group
    simp only [h1]
    rw [HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys
      (isHeckeCosetSystem_mul_right hsys hz₂) hφU (g * z₁), hT (g * z₁), ← mul_assoc, hφU _ z₂ hz₂]
  have hsph : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g z : AdelicGL2 (𝓞 K) K), f z ≠ 0 →
      φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) * z) = φ (g * z) := by
    intro kv g z hz
    obtain ⟨z₁, z₂, rfl, hz₂, hcomm⟩ := hsupp z hz
    set kk := placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) with hkk
    calc φ (g * kk * (z₁ * z₂)) = φ (g * (kk * z₁) * z₂) := by congr 1; group
      _ = φ (g * (z₁ * kk) * z₂) := by rw [hkk, hcomm]
      _ = φ ((g * z₁) * (kk * z₂)) := by congr 1; group
      _ = φ (g * z₁) := hφU _ _ (mul_mem (hUv kv) hz₂)
      _ = φ (g * z₁ * z₂) := (hφU _ _ hz₂).symm
      _ = φ (g * (z₁ * z₂)) := by rw [mul_assoc]

  have hconvT : ∀ g : AdelicGL2 (𝓞 K) K, ∑ j, rightConv K φ f (g * reps j) = a * rightConv K φ f g := by
    intro g
    simp only [rightConv_apply]
    rw [← integral_finsetSum _ (fun j _ => hint (g * reps j)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    by_cases hz : f z = 0
    · simp [hz]
    · rw [← Finset.sum_mul, hkey g z hz, mul_assoc]
  have hconvS : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      rightConv K φ f (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = rightConv K φ f g := by
    intro kv g
    simp only [rightConv_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    by_cases hz : f z = 0
    · simp [hz]
    · rw [hsph kv g z hz]

  have hΦS : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      Φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Φ g := by
    intro kv g
    show (∑ i, c i * rightConv K φ f (g * _ * h i)) = ∑ i, c i * rightConv K φ f (g * h i)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← hh i, ← mul_assoc, hconvS]
  have hΦT : ∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps Φ g = a * Φ g := by
    intro g
    show (∑ j, ∑ i, c i * rightConv K φ f (g * reps j * h i)) = a * ∑ i, c i * rightConv K φ f (g * h i)
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcomm : ∀ j, g * reps j * h i = g * h i * reps j := by
      intro j
      rw [hmrep j, mul_assoc, ← hh i (mrep j), ← mul_assoc]
    simp only [hcomm, ← Finset.mul_sum, hconvT]
    ring
  exact ⟨hΦS, hΦT, ⟨reps, hsys, hΦT⟩⟩

section CosetSumRightConv

-- The pin's `letI`/`haveI` wall at
-- `P2M/Sol/S_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType.lean:89-91`, made
-- file-local instead (the port idiom of `Cusp/SpectrumLift.lean:65-67`); the integral lemmas
-- below need `BorelSpace`/`IsHaarMeasure` at `glBorel`.
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem cosetSum_rightConv_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (hreps : ∀ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u')
    (hcov : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
      ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    (fun x => ∑ i, rightConv F φ f (x * reps i)) = rightConv F (fun x => ∑ i, φ (x * reps i)) f := by
  classical
  set U : Subgroup (AdelicGL2 (𝓞 F) F) := (productionPinsOf F D
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N with hUdef
  change IsLevelSphericalOfType F tys U f at hf
  have hf0 : IsLevelSphericalOfType F tys U f := hf
  change ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u' at hreps
  change ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') →
    ∃ i, ∃ u ∈ U, x = reps i * u at hcov
  change ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j at hinj
  have hφU' : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x := fun x u hu => hφU x u hu
  have hPa : U ≤ finiteAdelicGL2Subgroup F := by
    intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  set Uf : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := finiteLevelOne (𝓞 F) F N with hUfdef
  have hfinU : ∀ k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), k ∈ Uf →
      AdelicDock.finEmbed (𝓞 F) F k ∈ U := by
    intro k hk
    refine ⟨?_, ?_⟩
    · show AdelicDock.finEmbed (𝓞 F) F k ∈ levelOne (𝓞 F) F N
      rw [mem_levelOne_iff, AdelicDock.glFin_finEmbed]; exact hk
    · show AdelicDock.finEmbed (𝓞 F) F k ∈ finiteAdelicGL2Subgroup F
      rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
  have hUimg : (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) =
      (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
    ext k
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact mem_levelOne_iff.mp hg.1
    · intro hk
      exact ⟨AdelicDock.finEmbed (𝓞 F) F k, hfinU k hk, AdelicDock.glFin_finEmbed (𝓞 F) F k⟩
  have hUfo : IsOpen (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    isOpen_finiteLevelOne (𝓞 F) F hN
  have hUfc : IsCompact (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    isCompact_finiteLevelOne (𝓞 F) F N
  have hUfcl : IsClosed (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    isClosed_finiteLevelOne (𝓞 F) F N

  obtain ⟨fa, hfaT, -, -, hfeq⟩ := hf
  rw [hUimg] at hfeq
  set ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ) with hffdef
  have hff : IsFinTestFactor F ff := by
    refine ⟨?_, HasCompactSupport.intro hUfc fun y hy => Set.indicator_of_notMem hy _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    · exact ⟨_, hUfo, hx, fun x' hx' => by
        rw [hffdef, Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
    · exact ⟨_, hUfcl.isOpen_compl, hx, fun x' hx' => by
        rw [hffdef, Set.indicator_of_notMem (show x' ∉ (Uf : Set _) from hx'),
          Set.indicator_of_notMem hx]⟩
  have hfF : IsFactorizableTestFn F f := ⟨fa, ff, hfaT, hff, hfeq⟩
  exact CuspidalSpectrum.cosetSum_rightConv_eq F U hPa tys f hfF hf0 g hg n reps hreps hcov hinj
    φ hφ hφU'

end CosetSumRightConv

end AutomorphicForm
