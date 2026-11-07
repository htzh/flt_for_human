/-
  SET-AF18C consumer: the two operator-algebra modules composed into what they are for.

  **Zone 1 (module 1) — what right convolution preserves, read off the definition.** Rows 2 and 3 of
  `Adelic/RightConvPreservation.lean` say that `rightConv F φ f` of a continuous cuspidal `φ` by a
  factorisable `f` is again cuspidal and is `K_f`-smooth. Fed into `IsCuspidalFn`'s definitional form
  (`∀ g, constantTerm ν unipotentGL2 · g = 0`) they become a *value* of the unipotent constant term of
  the convolution at an arbitrary `g`, next to the smoothness statement. Row 4 then re-associates the
  triple convolution `(φ * f) * h * k` — the `GL₂(𝔸)` convolution algebra's product with the inverse
  twist on the right factor — first inside the outer factor, then (with the regularity of the two
  derived factors as hypotheses, since the port has no compact-support-of-a-convolution row) all the
  way to a single convolution with `φ` on the outside.

  **Zone 2 (module 2) — the right action.** Row 5 and row 6 are the two halves of one statement:
  convolving a translate conjugates the kernel, and for a *level-spherical* `f` the conjugated kernel
  `y ↦ f (k y k⁻¹)` is `f` again. Composed, the conjugation by a row-isometry translate is invisible in
  the convolution — the equality is read through the injectivity of the right translate by `k`, so it is
  row 5 at `k`, row 6 at `k`, not a re-proof. Row 7 is the archimedean Casimir: applied to `x` with its
  three arch-smoothness hypotheses it gives, in one conjunction, the Casimir commutation with the
  row-isometry translate and the two Casimir commutations with a factorisable arch-bi-finite `f`; the
  theorem below reads one commutation out of each side.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvPreservation
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Action
-- zone 1c reads the port's continuity row for a right convolution
-- (`AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport`)
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.CuspidalConstituent
open Filter Set Topology

-- the pin's wrappers register the two adelic Borel structures as local instances for these
-- statements (`Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean:11`)
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace AutomorphicForm
namespace SetAF18C

/-! ### Zone 1 (module 1) — cuspidality and `K_f`-smoothness read as a constant-term value -/

/-- **Zone 1a.** Row 3's `K_f`-smoothness and row 2's cuspidality of `rightConv F φ f`, with the
cuspidality conjunct read in `IsCuspidalFn`'s definitional form: the unipotent constant term of the
convolution vanishes at every `g`. -/
theorem consumer_zone1_preservation_unfolded
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hcusp : @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (g : AdelicGL2 (𝓞 F) F) :
    IsKfSmooth F (rightConv F φ f) ∧
      constantTerm (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2
        (rightConv F φ f) g = 0 :=
  ⟨isKfSmooth_rightConv F φ f hf, isCuspidalFn_rightConv F D U gen φ hcont hcusp f hf g⟩

/-- **Zone 1b.** Row 4's associativity applied to the triple convolution `(φ * f) * h`, inside a
further right convolution by `k`: the bracket `(φ * f) * h` is the same as
`φ * (h * (f ∘ inv))`. The hypotheses are exactly row 4's, on `φ`, `f` and `h`. -/
theorem consumer_zone1_triple_assoc
    (F : Type) [Field F] [NumberField F]
    (φ f h k : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : Continuous φ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hhc : Continuous h) (hhs : HasCompactSupport h) :
    rightConv F (rightConv F (rightConv F φ f) h) k =
      rightConv F (rightConv F φ (rightConv F h fun x => f x⁻¹)) k := by
  congr 1
  exact rightConv_rightConv_eq_rightConv_rightConv_comp_inv F φ hφ f h hfc hfs hhc hhs

/-- **Zone 1c.** The same row applied twice: the triple convolution `(φ * f) * h * k` flattened onto
`φ` alone, `rightConv F φ (rightConv F (rightConv F k (·⁻¹-precomposed h)) (·⁻¹-precomposed f))`. The
first step's `φ` slot is the convolution `rightConv F φ f`, whose continuity is the port's
`continuous_rightConv_of_continuous_of_hasCompactSupport`; the second step's `f`/`h` slots are `f` and
`rightConv F k (fun x => h x⁻¹)`, whose continuity comes from the same row at `k` and `h ∘ (·)⁻¹`. Row 4
asks for continuity *and* compact support on both factors, and the port has no
compact-support-of-a-convolution row, so exactly one fact is assumed: the compact support of the one
derived factor that row 4 sees as a factor rather than as the `φ` slot. -/
theorem consumer_zone1_triple_assoc_flatten
    (F : Type) [Field F] [NumberField F]
    (φ f h k : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : Continuous φ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hhc : Continuous h) (hhs : HasCompactSupport h)
    (hkc : Continuous k) (hks : HasCompactSupport k)
    (hGs : HasCompactSupport (rightConv F k fun x => h x⁻¹)) :
    rightConv F (rightConv F (rightConv F φ f) h) k =
      rightConv F φ (rightConv F (rightConv F k fun x => h x⁻¹) fun x => f x⁻¹) := by
  have hinv : Continuous fun x : AdelicGL2 (𝓞 F) F => h x⁻¹ := hhc.comp continuous_inv
  have hinvs : HasCompactSupport fun x : AdelicGL2 (𝓞 F) F => h x⁻¹ :=
    hhs.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))
  have hmc : Continuous (rightConv F φ f) :=
    continuous_rightConv_of_continuous_of_hasCompactSupport F φ hφ f hfc hfs
  have hGc : Continuous (rightConv F k fun x => h x⁻¹) :=
    continuous_rightConv_of_continuous_of_hasCompactSupport F k hkc (fun x => h x⁻¹) hinv hinvs
  rw [rightConv_rightConv_eq_rightConv_rightConv_comp_inv F (rightConv F φ f) hmc h k hhc hhs hkc hks,
    rightConv_rightConv_eq_rightConv_rightConv_comp_inv F φ hφ f
      (rightConv F k fun x => h x⁻¹) hfc hfs hGc hGs]

/-! ### Zone 2 (module 2) — the row-isometry translate through a level-spherical convolution -/

/-- **Zone 2a.** Row 5 and row 6 composed: for a level-spherical `f`, conjugating the kernel by a
row-isometry translate does not change the convolution. Row 6 says the translate passes through the
convolution; row 5 turns the translate of a convolution into a convolution with the conjugated kernel;
the two agree, so the conjugation is invisible — read through injectivity of the right translate. -/
theorem consumer_zone2_translate_passes_conv
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys U f)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F φ (fun y => f (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹)) =
      rightConv F φ f := by
  have hinj : ∀ a b : AdelicGL2 (𝓞 F) F → ℂ,
      rightTranslate F (rowIsometryInclAt₀ F w k) a = rightTranslate F (rowIsometryInclAt₀ F w k) b →
        a = b := by
    intro a b hab
    funext g
    have h := congrFun hab (g * (rowIsometryInclAt₀ F w k)⁻¹)
    simpa only [rightTranslate, mul_assoc, inv_mul_cancel, mul_one] using h
  have h5 := CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj F
    (rowIsometryInclAt₀ F w k) φ f
  have h6 := rightTranslate_rightConv_of_isLevelSphericalOfType F tys U f hf w k φ
  exact hinj _ _ (by rw [← h5, h6])

/-! ### Zone 2b — the Casimir commutes with both right actions -/

/-- **Zone 2b.** Row 7 read on both sides at a function `x` meeting its three arch-smoothness
hypotheses and a factorisable arch-bi-finite `f`: the archimedean Casimir commutes with the
row-isometry translate (first conjunct) and with the right convolution (second conjunct). -/
theorem consumer_zone2_casimir_commutes
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : ArchTypeFamily K)
    (hf : IsFactorizableTestFn K f) (hbf : IsArchBiFinite K tys f) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x)) ∧
      archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f := by
  have h := archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
    K w hw x hxc hxs hD1 hD2
  exact ⟨fun w' k => (h.1 w' k).2.2.2.1, (h.2 f tys hf hbf).2.2.2.1⟩

end SetAF18C
end AutomorphicForm
