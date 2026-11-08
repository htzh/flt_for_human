/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/RightConvCosetSum.lean` (order AF39B).

  A `spec/` probe, not a library module: it *consumes* the two headlines in composition, never by
  `#check`.

  The two headlines are the "eigen" and the "linearity" halves of the same bookkeeping, both about
  `rightConv` (the right regular action of a test function) against a double-coset transversal
  `reps`, both summed with `heckeCosetSum`:

  * `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` — for a Hecke coset system `reps` at a
    pure place `v`, a `U`-invariant `φ` that is a coset eigenfunction with eigenvalue `a`, and `f`
    supported in `U · (v-central elements)`, the combination `Φ = ∑ i, c i * rightConv φ f (· * h i)`
    is again `v`-invariant and again a coset eigenfunction with the *same* eigenvalue `a`;
  * `cosetSum_rightConv_of_isLevelSphericalOfType` — for a level-spherical `f` and a transversal
    `reps` of `g` mod `U`, the coset sum of the convolution is the convolution by the coset sum:
    `∑ i rightConv φ f (· * reps i) = rightConv (∑ i φ (· * reps i)) f`.

  The zones below read the two headlines **at the same `reps`** and let them act on each other.

  * **Zone 1** is the linearity half written in the eigen half's vocabulary: the `heckeCosetSum` of
    `rightConv φ f` — the very operator that the eigen half sets equal to `a • Φ` — is the
    convolution by the coset sum of `φ`. No new input, only the headline at a point.

  * **Zone 2** is the eigen half at the one-element combination `n = 1`, `h = c = 1`: a single right
    convolution `rightConv φ f` is itself a coset eigenfunction at `v` with the eigenvalue `a` of
    `φ`, and is `v`-invariant under `placeEmbed` of the integral local units. This is the eigen half
    with the combination unrolled — the statement the Hecke recursion actually consumes downstream.

  * **Zone 3** puts them side by side: since Zone 1 identifies the coset sum with a convolution and
    Zone 2 evaluates that coset sum, the convolution by the coset sum of an eigenfunction `φ` is the
    convolution by `φ` scaled by the eigenvalue `a`. This is the composition the smoothing arguments
    use: pushing the Hecke operator through a convolution turns it into scalar multiplication.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF39BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvCosetSum

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain Matrix
open AutomorphicForm AutomorphicForm.SmoothCusp AutomorphicForm.CuspidalConstituent UnramifiedWhittaker
  HeckeIntegralSeam
open NumberField.AdelicHaar NumberField.AdelicBox

namespace AutomorphicFormSetAF39BConsumer

variable {F : Type} [Field F] [NumberField F]

/-- The level subgroup of the linearity headline, `productionPinsOf … .U N`, as one name. -/
abbrev pinsU (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N

/-- **Zone 1.** The linearity half in the eigen half's vocabulary: the coset sum of the right
convolution of a level-spherical test function is the right convolution by the coset sum. -/
theorem heckeCosetSum_rightConv_eq_rightConv
    (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys (pinsU D N) f)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (hreps : ∀ i, ∃ u ∈ pinsU D N, ∃ u' ∈ pinsU D N, reps i = u * g * u')
    (hcov : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ pinsU D N, ∃ u' ∈ pinsU D N, x = u * g * u') →
      ∃ i, ∃ u ∈ pinsU D N, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ pinsU D N → i = j)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) (x : AdelicGL2 (𝓞 F) F) :
    heckeCosetSum F reps (rightConv F φ f) x =
      rightConv F (fun y => ∑ i, φ (y * reps i)) f x := by
  have h := cosetSum_rightConv_of_isLevelSphericalOfType F D N hN tys f hf g hg n reps
    hreps hcov hinj φ hφ hφU
  simpa only [heckeCosetSum] using congrFun h x

/-- **Zone 2.** The eigen half at a single convolution (`n = 1`, `h = c = 1`): the right
convolution of a coset eigenfunction is a coset eigenfunction with the same eigenvalue, and it is
invariant under the integral local units embedded at `v`. -/
theorem rightConv_cosetEigen
    (v : HeightOneSpectrum (𝓞 F)) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (hUv : ∀ kv : GL (Fin 2) (v.adicCompletionIntegers F),
      placeEmbed F v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv) ∈ U)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F)
    (hsys : IsHeckeCosetSystem U (heckeGen (𝓞 F) F v) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion F), reps j = placeEmbed F v m)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (g * u) = φ g)
    (a : ℂ) (hφT : IsHeckeCosetEigenfunctionAt F U (heckeGen (𝓞 F) F v) v φ a)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hsupp : ∀ z : AdelicGL2 (𝓞 F) F, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 F) F,
      z = z₁ * z₂ ∧ z₂ ∈ U ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion F), z₁ * placeEmbed F v xv = placeEmbed F v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 F) F, Integrable (fun z => φ (g * z) * f z)
      (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers F)) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (g * placeEmbed F v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv)) = rightConv F φ f g) ∧
    (∀ g : AdelicGL2 (𝓞 F) F, heckeCosetSum F reps (rightConv F φ f) g = a * rightConv F φ f g) := by
  have h := heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps F v U hUv reps hsys hpure φ hφU a
    hφT f hsupp hint (n := 1) (h := fun _ => 1) (c := fun _ => 1) (hh := fun i xv => by simp)
  constructor
  · intro kv g
    simpa using h.1 kv g
  · intro g
    simpa using h.2.1 g

/-- **Zone 3.** The composition: the coset sum of an eigenfunction's convolution, which Zone 1 reads
as a convolution *by the coset sum*, is by Zone 2 the eigenfunction's own convolution scaled by the
eigenvalue. Pushing the Hecke operator through a right convolution is scalar multiplication. -/
theorem rightConv_cosetSum_eq_smul
    (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : ArchTypeFamily F)
    (v : HeightOneSpectrum (𝓞 F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys (pinsU D N) f)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F)
    (hsys : IsHeckeCosetSystem (pinsU D N) (heckeGen (𝓞 F) F v) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion F), reps j = placeEmbed F v m)
    (hUv : ∀ kv : GL (Fin 2) (v.adicCompletionIntegers F),
      placeEmbed F v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv) ∈ pinsU D N)
    (hreps : ∀ i, ∃ u ∈ pinsU D N, ∃ u' ∈ pinsU D N, reps i = u * g * u')
    (hcov : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ pinsU D N, ∃ u' ∈ pinsU D N, x = u * g * u') →
      ∃ i, ∃ u ∈ pinsU D N, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ pinsU D N → i = j)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ pinsU D N, φ (x * u) = φ x)
    (a : ℂ) (hφT : IsHeckeCosetEigenfunctionAt F (pinsU D N) (heckeGen (𝓞 F) F v) v φ a)
    (hsupp : ∀ z : AdelicGL2 (𝓞 F) F, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 F) F,
      z = z₁ * z₂ ∧ z₂ ∈ pinsU D N ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion F), z₁ * placeEmbed F v xv = placeEmbed F v xv * z₁)
    (hint : ∀ z : AdelicGL2 (𝓞 F) F, Integrable (fun y => φ (z * y) * f y)
      (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    rightConv F (fun x => ∑ i, φ (x * reps i)) f g = a * rightConv F φ f g := by
  have hφUmem : φ ∈ levelInvariantSubmodule F (productionPinsOf F D
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun w => heckeGen (𝓞 F) F w) (adelicBox F)) N := hφU
  have hC := cosetSum_rightConv_of_isLevelSphericalOfType F D N hN tys f hf g hg
    (Ideal.absNorm v.asIdeal + 1) reps hreps hcov hinj φ hφ hφUmem
  have hB := (rightConv_cosetEigen (F := F) v (pinsU D N) hUv reps hsys hpure φ hφU a hφT f hsupp
    hint).2 g
  calc rightConv F (fun x => ∑ i, φ (x * reps i)) f g
      = (fun x => ∑ i, rightConv F φ f (x * reps i)) g := (congrFun hC g).symm
    _ = heckeCosetSum F reps (rightConv F φ f) g := rfl
    _ = a * rightConv F φ f g := hB

end AutomorphicFormSetAF39BConsumer
