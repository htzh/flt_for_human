/-
  The unramified package: right convolution by translates, and the Hecke eigenvalue law.

  A genuine cusp realization `R` of a Hecke eigensystem `Θ` at the level `Θ.level` carries a family
  of unramified test functions — one per finite place `v` and Hecke generator `ϖ` — such that the
  right convolution of any member of `R` by a translate in the `v`-adic direction is the sum of a
  finite package of right convolutions at `v`-unramified elements, and such that the Whittaker
  coefficient of the Hecke generator's translate is the Hecke eigenvalue `Θ b` times the coefficient
  at the place embedding.

  The two halves are the "unramified package" of the cuspidal-spectrum analysis: the first is the
  finite-sum decomposition along the Hecke operator, the second is the spectral eigenvalue law that
  makes the decomposition diagonal. Both are stated for an arbitrary production-pins bundle and the
  standard additive character.

  **Build record (AF99D).** The pin's 621 lines are transcribed whole: its four search-stage
  namespaces `RS12L`, `RS12W`, `RS12L_e13`, `RS12H` keep their labels under this module's namespace
  (only the generation prefix `P2MW.S_…` is dropped, as the port's naming policy requires), each
  declaration at the pin's own statement, and the pin's `solution` row *is* the headline. The pin
  carries **17 public and 1 `private` declaration** of 18, so `scaffold_audit`'s `complete` is a real
  reading here, not the vacuous case of FR-0277.

  **Reuse before re-proving.** `port_advise --nodes
  AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate` reports exactly
  three declarations already in the port, and two of them are this row's own `solution` and its
  `Theorems/` wrapper. The third is used:

  * `RS12W.whittakerCoefficient_mul_right` — statement transcribed, proof
    `AutomorphicForm.DCFN.whittakerCoefficient_mul_right` (`WhittakerDiagOne.lean:230`), the same
    theorem with the bound field variable spelled `K` instead of the pin's `F` (the checker's
    `same_stmt` cannot see the equality: the field variable occurs in the statement *text*, not as a
    binder).
  * `RS12L_e13.centralScalar_comm` — statement transcribed with the pin's binder `h`, proof
    `AutomorphicForm.DCFN.centralScalar_comm` (`WhittakerDiagOne.lean:489`), which the checker's
    `same_stmt` reports identical up to binder spelling.
  * `RS12L_e13.adele_ext` is `private` in the pin and is re-stated `private` here (FR-0279). The
    port's two *public* copies (`AutomorphicForm.IwasawaWeyl.adele_ext`,
    `AutomorphicForm.WeylIntegrable.adele_ext`) live outside this module's import closure and the
    lemma is a two-line `Prod.ext`, so no import is widened for it.
  * Every other declaration is the pin's own body, transcribed.

  ## Port deltas

  * Imports: the scaffold's nine plus `RightConvCosetSum` (the coset-sum row
    `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps`), `HeckeCosetSeam` (the coset system's
    existence, `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen`) and
    `WhittakerDiagOne` (the two reused proofs above). No `import Mathlib`.
  * Module-level `attribute [local instance] NumberField.AdelicHaar.glBorel
    NumberField.AdelicHaar.borelSpace_glBorel`, as in `RightConvCosetSum.lean:187`: the statements of
    `hint`/`hintf` are `Integrable … (adelicGLHaar (Fin 2) (𝓞 K) K)` and that measure's measurable
    space is the explicit `glBorel`.
  * Body substitutions, all statement-neutral: `continuous_mul_left` → `continuous_const_mul` (two
    sites, `hint` and `hintf`; the v4.34 name, mathlib `Topology/Algebra/Monoid/Defs.lean:124`);
    `integral_finset_sum` → `integral_finsetSum` in `RS12W.sum_whittakerCoefficient_mul_right_eq`
    (the old spelling is deprecated since 2026-04-08); the pin's `letI`/`haveI` walls → `let`/`have`
    (FR-0255's cure — no linter option is installed anywhere in this module).
  * `RS12L.placeEmbed_unipotent`: three arguments of the pin's `simp [...]` lists are never used by
    the port's simp set (`linter.unusedSimpArgs`: `Matrix.one_apply`, `Prod.fst_one`, `Prod.fst_zero`
    in the archimedean component, and `Matrix.one_apply`, `Prod.snd_one`, `Prod.snd_zero` in the two
    finite ones); they are dropped and the residual `1 = 1.1` (`AdeleRing` is a `def` at v4.34) is
    closed by the pin's own trailing `<;> rfl`.
  * `hharch` is dead in the pin's own proof (never referenced); it is spent with `have _ := hharch`
    (FR-0236: no binder renamed, no linter option installed).
  * The pin's `set_option maxHeartbeats 6400000` is **not** carried — see the probe below.

  **Heartbeat probe (measured, never installed**; read with `lake env lean -DautoImplicit=false
  -DmaxHeartbeats=N <module>`): **silent at `N = 75000`, fails at `N = 50000`**
  (`…UnramifiedPackage.lean:563:6: (deterministic) timeout at `elaborator``) — the FR-0260 shape at
  that site, the `rwa [show … from rfl, mul_div_cancel_right₀ _ hπ0]` closing `hψ1`. The natural
  per-declaration cost therefore sits in `(50000, 75000]`, inside the 200000 default; that is why the
  pin's 6.4M `maxHeartbeats` was not needed. Silent at the edit-loop default, where every gate was
  read.

  spec-pin: P2M/Sol/S_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate.lean
-/


import FLTForHuman.AutomorphicForm.Adelic.Cusp.SmoothRealization
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.HeckeEigensystem
import FLTForHuman.AutomorphicForm.Adelic.TwistedOrbital
import FLTForHuman.AutomorphicForm.Adelic.UnitFactorizableOfType
import FLTForHuman.LanglandsTunnell.TateLocal.AddCharLevel
import FLTForHuman.RepTheory.LocalLanglands.HeckeCosetSystem
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import FLTForHuman.NumberTheory.StandardAddChar.GlobalAndInfinite
import FLTForHuman.AutomorphicForm.Adelic.RightConvCosetSum
import FLTForHuman.AutomorphicForm.Adelic.HeckeCosetSeam
import FLTForHuman.AutomorphicForm.Adelic.WhittakerDiagOne

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain
open MeasureTheory NumberField.AdelicHaar Matrix
open LocalGL2 AdelicDock HeckeIntegralSeam
open scoped Classical

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm.SmoothCuspRealizationAt

/-! ## The pin's prelude

The pin's four search-stage namespaces `RS12L`, `RS12W`, `RS12L_e13` and `RS12H` are kept (only the
generation prefix `P2MW.S_…` is dropped, as the port's naming policy requires): the place identities
(`diagZ`/`repSome`/`repInf` against the port's `LocalGL2` coset representatives, and the unipotent
embedding), the coefficient bookkeeping (`RS12W`), the central-scalar dictionary (`RS12L_e13`, the
idèle `zIdele` and the two determinant identities) and the coset equivariance of a Hecke coset
system (`RS12H`). -/

section

namespace RS12L

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem diagZ_one_eq_diagPi (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) :
    UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 1 =
      diagPi ϖ hϖ0 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.diagZ, coe_diagPi]

theorem repSome_eq_localRepSome (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (b : v.adicCompletionIntegers K) :
    UnramifiedWhittaker.repSome (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) b) = localRepSome ϖ hϖ0 b := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.repSome, localRepSome, Matrix.mul_apply, Fin.sum_univ_two]

theorem repInf_eq_localRepInf (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) :
    UnramifiedWhittaker.repInf (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 =
      localRepInf (K := v.adicCompletion K) ϖ hϖ0 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.repInf, localRepInf, Matrix.mul_apply, Fin.sum_univ_two]

theorem placeEmbed_unipotent (xv : v.adicCompletion K) :
    UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) =
      unipotentGL2 (R := AdeleRing (𝓞 K) K) (NumberField.StandardAddChar.adeleSingleAt K v xv) := by
  have h1 : UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) =
      finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (UnramifiedWhittaker.unipotent xv)) := rfl
  rw [h1]
  refine Units.ext ?_
  rw [coe_finEmbed, coe_localEmbed, unipotentGL2_coe]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K ?_ ?_
  · rw [mapMatrix_arch_finMat]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, NumberField.StandardAddChar.adeleSingleAt_apply]
    fin_cases i <;> fin_cases j <;> simp <;> rfl
  · rw [mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply,
        NumberField.StandardAddChar.adeleSingleAt_apply]
      fin_cases i <;> fin_cases j <;>
        simp [UnramifiedWhittaker.unipotent,
          NumberField.StandardAddChar.finAdeleSingleAt_apply_self] <;> rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 K) K v _ hw]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply,
        NumberField.StandardAddChar.adeleSingleAt_apply]
      fin_cases i <;> fin_cases j <;>
        simp [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne K v xv hw] <;> rfl

end RS12L

namespace RS12W

variable (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)

theorem whittakerCoefficient_mul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g k : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (g * k) = whittakerCoefficient F pins ψ (fun y => φ (y * k)) α g := by
  exact DCFN.whittakerCoefficient_mul_right F pins ψ φ α g k

theorem whittakerCoefficient_mul_right_eq_of_forall (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ y, φ (y * k) = φ y) :
    whittakerCoefficient F pins ψ φ α (g * k) = whittakerCoefficient F pins ψ φ α g := by
  rw [whittakerCoefficient_mul_right]
  congr 1
  funext y
  exact hk y

theorem whittakerCoefficient_mul_central (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g c : AdelicGL2 (𝓞 F) F) (ω : ℂ)
    (hcomm : ∀ h : AdelicGL2 (𝓞 F) F, h * c = c * h) (hc : ∀ h, φ (c * h) = ω * φ h) :
    whittakerCoefficient F pins ψ φ α (g * c) = ω * whittakerCoefficient F pins ψ φ α g := by
  let : MeasurableSpace (AdeleRing (𝓞 F) F) := pins.nS
  simp only [whittakerCoefficient]
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, hcomm (unipotentGL2 u * g), hc]
  ring

theorem sum_whittakerCoefficient_mul_right_eq {ι : Type*} [Fintype ι] (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) (r : ι → AdelicGL2 (𝓞 F) F) (a : ℂ)
    (hsum : ∀ h : AdelicGL2 (𝓞 F) F, (∑ j, φ (h * r j)) = a * φ h)
    (hint : ∀ j, WhittakerCoefficientIntegrable F pins ψ (fun y => φ (y * r j)) α g) :
    (∑ j, whittakerCoefficient F pins ψ φ α (g * r j)) = a * whittakerCoefficient F pins ψ φ α g := by
  let : MeasurableSpace (AdeleRing (𝓞 F) F) := pins.nS
  simp only [whittakerCoefficient_mul_right]
  simp only [whittakerCoefficient]
  rw [← integral_finsetSum _ (fun j _ => hint j), ← integral_const_mul]
  congr 1
  funext u
  rw [← Finset.sum_mul, hsum]
  ring

end RS12W

namespace RS12L_e13

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

noncomputable def zIdele (π : v.adicCompletion K) (hπ : π ≠ 0) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (Units.mk0 π hπ))

theorem zIdele_fst (π : v.adicCompletion K) (hπ : π ≠ 0) :
    ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem zIdele_snd_self (π : v.adicCompletion K) (hπ : π ≠ 0) :
    ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = π := by
  change ((localUnit (𝓞 K) K v (Units.mk0 π hπ) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = π
  rw [localUnit_apply_self]; rfl

theorem zIdele_snd_of_ne (π : v.adicCompletion K) (hπ : π ≠ 0) {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  change ((localUnit (𝓞 K) K v (Units.mk0 π hπ) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1
  exact localUnit_apply_of_ne _ _ _ _ hw

private theorem adele_ext {a b : AdeleRing (𝓞 K) K} (h1 : ∀ w, a.1 w = b.1 w) (h2 : ∀ u, a.2 u = b.2 u) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)

theorem placeEmbed_scalarPi (π : v.adicCompletion K) (hπ : π ≠ 0) :
    UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi π hπ) = centralScalar (𝓞 K) K (zIdele K v π hπ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have lhs : ((UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi π hπ) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      AdelicDock.finMat (𝓞 K) K (AdelicDock.localMat (𝓞 K) K v
        ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) i j := rfl
  have hsc : ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![π, 0; 0, π] := rfl
  have rhs : ((centralScalar (𝓞 K) K (zIdele K v π hπ) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (Matrix.scalar (Fin 2) ((zIdele K v π hπ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j := rfl
  rw [lhs, hsc, rhs, Matrix.scalar_apply, Matrix.diagonal_apply]
  refine adele_ext K (fun w => ?_) (fun u => ?_)
  · change (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w = _
    rw [Matrix.one_apply]
    split_ifs <;> rfl
  · change AdelicDock.splice (𝓞 K) K v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j)
        ((!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) u = _
    by_cases hu : u = v
    · subst hu
      rw [AdelicDock.splice_apply_self]
      split_ifs with hij
      · subst hij; rw [zIdele_snd_self]; fin_cases i <;> rfl
      · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl
    · rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply]
      split_ifs with hij
      · rw [zIdele_snd_of_ne K v π hπ hu]; rfl
      · rfl

theorem det_placeEmbed_diagZ_one (π : v.adicCompletion K) (hπ : π ≠ 0) :
    Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ π hπ 1)) = zIdele K v π hπ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (AdelicDock.finMat (𝓞 K) K (AdelicDock.localMat (𝓞 K) K v (!![π ^ (1 : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))).det = _
  set D : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) := !![π ^ (1 : ℤ), 0; 0, 1] with hD
  set M := AdelicDock.finMat (𝓞 K) K (AdelicDock.localMat (𝓞 K) K v D) with hM
  refine Prod.ext ?_ (RestrictedProduct.ext _ _ fun u => ?_)
  ·
    have h := RingHom.map_det (adeleArch (𝓞 K) K) M
    rw [hM, AdelicDock.mapMatrix_arch_finMat, Matrix.det_one] at h
    exact h
  ·
    have h := RingHom.map_det ((finAdeleEval (𝓞 K) K u).comp (adeleFin (𝓞 K) K)) M
    have e : ((finAdeleEval (𝓞 K) K u).comp (adeleFin (𝓞 K) K)).mapMatrix M =
        (finAdeleEval (𝓞 K) K u).mapMatrix ((adeleFin (𝓞 K) K).mapMatrix M) := by
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.coe_comp, Matrix.map_map]
    rw [e, hM, AdelicDock.mapMatrix_fin_finMat] at h
    change ((finAdeleEval (𝓞 K) K u).comp (adeleFin (𝓞 K) K)) M.det = _
    rw [h]
    by_cases hu : u = v
    · subst hu
      rw [AdelicDock.mapMatrix_localMat_self]
      have hdet : D.det = π := by rw [hD, Matrix.det_fin_two_of]; simp
      exact hdet.trans (zIdele_snd_self K u π hπ).symm
    · rw [AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hu, Matrix.det_one]
      exact (zIdele_snd_of_ne K v π hπ hu).symm

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (h : AdelicGL2 (𝓞 K) K) :
    h * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * h :=
  DCFN.centralScalar_comm K z h

end RS12L_e13

namespace RS12H

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι κ : Type*}
    (reps : ι → G) (e : κ ≃ ι) (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset := fun k => h.mem_doubleCoset (e k)
  covers := fun x hx => by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective := fun k₁ k₂ hk => e.injective (h.mk_injective (by simpa using hk))

end RS12H

end

theorem unramified_package_rightConv_sum_translate
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (hRlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      R.toFun (g * k) = R.toFun g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfT : IsFactorizableTestFn K f)
    (S Sf Sψ : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sf ⊆ S) (hSψ : Sψ ⊆ S)
    (hfsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet)
    (hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (r : ℕ) (h : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (hharch : ∀ i, glArch (𝓞 K) K (h i) = 1)
    (hhcomm : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h i)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hxsum : ∀ g, x g = ∑ i, cs i * rightConv K R.toFun f (g * h i))
    (hxint : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g)
    (hxper : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh))
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    ((∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        x (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g) ∧
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v)) ∧
    ∃ (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
      (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
      (b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers K),
      UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) = heckeGen (𝓞 K) K v ∧
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) ∧
      (∀ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1) ∧
      (∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) =
          ψv xv * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) =
          whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
          whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) =
          Θ.toRawCentral.a v * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) =
          Θ.toRawCentral.b v * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g)
  := by
  have hN : Θ.level ≠ ⊥ := Θ.level_ne_bot
  have hRne : ∃ g, R.toFun g ≠ 0 := R.exists_ne_zero
  have hS_good := hS
  have hSf_sub := hSf
  have _ := hharch
  have hUv : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) ∈
        levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K := by
    intro v hv kv
    obtain ⟨hlv, -⟩ := hS_good v hv
    set k : GL (Fin 2) (v.adicCompletion K) := Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv with hkdef
    have hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
      intro i j
      show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ((kv : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
      exact SetLike.coe_mem _
    have hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K := by
      intro i j
      have : k⁻¹ = Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv⁻¹ := by rw [hkdef, map_inv]
      rw [this]
      show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) (((kv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
      exact SetLike.coe_mem _
    have hb : idealBound (𝓞 K) Θ.level v = 1 := idealBound_eq_one_of_not_dvd hN hlv
    show AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v k) ∈ _
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff,
        AdelicDock.mem_localLevelOne_iff]
      refine ⟨⟨hk, ?_, ?_⟩, ⟨hk', ?_, ?_⟩⟩ <;> rw [hb]
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk 1 0
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk 1 1) (one_mem _)
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk' 1 0
      · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk' 1 1) (one_mem _)
    · rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
  have hpure : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        IsHeckeCosetSystem (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) reps ∧
        ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), reps j = UnramifiedWhittaker.placeEmbed K v m := by
    intro v hv
    obtain ⟨hlv, -⟩ := hS_good v hv

    obtain ⟨ϖ, hϖ0, -, -, sec, -, hsysAll⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
    have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hcardO : Fintype.card (Option (𝓞 K ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
      rw [Fintype.card_option, hcard]
    set eO : Option (𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal + 1) := Fintype.equivFinOfCardEq hcardO with heO
    set repsL : Option (𝓞 K ⧸ v.asIdeal) → AdelicGL2 (𝓞 K) K := fun o => AdelicDock.finEmbed (𝓞 K) K
      (AdelicDock.localEmbed (𝓞 K) K v (o.elim (LocalGL2.localRepInf ϖ hϖ0) (fun c' => LocalGL2.localRepSome ϖ hϖ0
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))) with hrepsL
    refine ⟨repsL ∘ eO.symm, RS12H.isHeckeCosetSystem_comp_equiv repsL eO.symm (hsysAll Θ.level hlv), fun j => ?_⟩
    simp only [hrepsL, Function.comp]
    exact ⟨_, rfl⟩
  have hconv : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        x (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g) ∧
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v) := by
    intro v hv
    obtain ⟨reps, hsys, hpr⟩ := hpure v hv
    obtain ⟨hlv, hev⟩ := hS_good v hv
    have hint : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => R.toFun (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
      intro g
      obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT
      have hH := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
      exact ((hR.comp (continuous_const_mul g)).mul hfc).integrable_of_hasCompactSupport hfcs.mul_left
    have hsupp' : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
        z = z₁ * z₂ ∧ z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁ := by
      intro z hz
      obtain ⟨-, z₁, z₂, hzz, hz₂, hcommz⟩ := hfsupp z hz
      exact ⟨z₁, z₂, hzz, hz₂, hcommz v (fun hvS => hv (hSf_sub hvS))⟩
    have key := AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps K v
      (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (hUv v hv) reps hsys hpr R.toFun
      (fun g k hk => hRlev g k hk) (Θ.toRawCentral.a v) ?_ f hsupp' hint h cs (fun i xv => hhcomm i v hv xv)
    · obtain ⟨hK, -, hHecke⟩ := key
      refine ⟨fun kv g => ?_, ?_⟩
      · rw [hxsum, hxsum]; exact hK kv g
      ·
        have hfun : x = fun g => ∑ i, cs i * rightConv K R.toFun f (g * h i) := funext hxsum
        rw [hfun]; exact hHecke
    ·
      exact R.hecke_eigen v hev
  refine ⟨hconv v hv, ?_⟩
  set Wx : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun g => whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g with hWx
  have locdata : ∃ (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
      (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
      (b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers K),
      UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) = heckeGen (𝓞 K) K v ∧
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) ∧
      (∀ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1) ∧
      (∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) = ψv xv * Wx g) ∧
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Wx g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
          Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = Θ.toRawCentral.a v * Wx g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = Θ.toRawCentral.b v * Wx g) := by
    obtain ⟨hlv, hev⟩ := hS_good v hv
    have hvψ : v ∉ Sψ := fun h' => hv (hSψ h')

    obtain ⟨ϖ, hϖ0, hϖval, hgen', sec, hsec, hsysAll⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
    have hgen : UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 1) = heckeGen (𝓞 K) K v := by
      rw [RS12L.diagZ_one_eq_diagPi]; exact hgen'
    have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    set eI : (𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal) := Fintype.equivFinOfCardEq hcard with heI
    set b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers K :=
      fun i => algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec (eI.symm i)) with hb
    set π : v.adicCompletion K := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ with hπdef
    set repsO : Option (𝓞 K ⧸ v.asIdeal) → AdelicGL2 (𝓞 K) K := fun o =>
      UnramifiedWhittaker.placeEmbed K v (o.elim (UnramifiedWhittaker.repInf π hϖ0)
        (fun c' => UnramifiedWhittaker.repSome π hϖ0
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))) with hrepsO
    have hrepsO_eq : repsO = fun o : Option (𝓞 K ⧸ v.asIdeal) => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v
        (o.elim (LocalGL2.localRepInf ϖ hϖ0) (fun c' => LocalGL2.localRepSome ϖ hϖ0
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))) := by
      funext o
      cases o with
      | none => simp only [hrepsO, Option.elim]; rw [RS12L.repInf_eq_localRepInf]; rfl
      | some c' => simp only [hrepsO, Option.elim]; rw [RS12L.repSome_eq_localRepSome]; rfl
    have hsysO : IsHeckeCosetSystem (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) repsO := by
      rw [hrepsO_eq]; exact hsysAll Θ.level hlv

    have hcardO : Fintype.card (Option (𝓞 K ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
      rw [Fintype.card_option, hcard]
    set eO : Option (𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal + 1) := Fintype.equivFinOfCardEq hcardO with heO
    have hsysF := RS12H.isHeckeCosetSystem_comp_equiv repsO eO.symm hsysO
    have hprF : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), (repsO ∘ eO.symm) j = UnramifiedWhittaker.placeEmbed K v m := by
      intro j
      simp only [Function.comp, hrepsO]
      exact ⟨_, rfl⟩
    obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT
    have hH := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
    have hintf : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => R.toFun (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
      fun g => ((hR.comp (continuous_const_mul g)).mul hfc).integrable_of_hasCompactSupport hfcs.mul_left
    have hsupp' : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
        z = z₁ * z₂ ∧ z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁ := by
      intro z hz
      obtain ⟨-, z₁, z₂, hzz, hz₂, hcommz⟩ := hfsupp z hz
      exact ⟨z₁, z₂, hzz, hz₂, hcommz v (fun hvS => hv (hSf_sub hvS))⟩
    obtain ⟨-, hsumreps, -⟩ := AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps K v
      (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (hUv v hv) (repsO ∘ eO.symm) hsysF hprF R.toFun
      (fun g k hk => hRlev g k hk) (Θ.toRawCentral.a v) (R.hecke_eigen v hev) f hsupp' hintf h cs (fun i xv => hhcomm i v hv xv)

    have hsumO : ∀ hh : AdelicGL2 (𝓞 K) K, (∑ o, x (hh * repsO o)) = Θ.toRawCentral.a v * x hh := by
      intro hh
      have h1 := hsumreps hh
      simp only [heckeCosetSum] at h1
      rw [← hxsum hh] at h1
      have h2 : (∑ j, ∑ i, cs i * rightConv K R.toFun f (hh * (repsO ∘ eO.symm) j * h i)) = ∑ j, x (hh * (repsO ∘ eO.symm) j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hxsum]
      rw [h2] at h1
      rw [← h1]
      exact (Equiv.sum_comp eO.symm (fun o => x (hh * repsO o))).symm

    set ψv : AddChar (v.adicCompletion K) ℂ := NumberField.StandardAddChar.psiLocal K v with hψvdef
    have hψ0 : ∀ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1 :=
      fun r => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v _ r.2
    have hψ1 : ∃ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r / π) ≠ 1 := by
      have hlev0 := hSψ0 v hvψ
      obtain ⟨-, xx, hxx, hxx1⟩ := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v ψv
        ⟨0, fun y hy => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v y (by
          rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero])⟩
        (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)
      rw [hlev0, zero_add] at hxx
      have hππ : (π : v.adicCompletion K) = (ϖ : v.adicCompletion K) := rfl
      have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) := by rw [hππ]; exact hϖval
      have hr : xx * π ∈ v.adicCompletionIntegers K := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hvπ]
        calc Valued.v xx * WithZero.exp (-1 : ℤ) ≤ WithZero.exp 1 * WithZero.exp (-1 : ℤ) :=
              mul_le_mul_left hxx _
          _ = 1 := by rw [← WithZero.exp_add]; norm_num
      refine ⟨⟨xx * π, hr⟩, ?_⟩
      have hπ0 : π ≠ 0 := hϖ0
      rwa [show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨xx * π, hr⟩ = xx * π from rfl,
        mul_div_cancel_right₀ _ hπ0]

    have hNw : ∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) = ψv xv * Wx g := by
      intro xv g
      simp only [hWx]
      rw [RS12L.placeEmbed_unipotent, AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K _ _ _ _
        (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).principalInvariant x g (fun β uu => hxper β uu g) 1]
      congr 1
      rw [map_one, one_mul]
      rfl
    have hKw : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Wx g :=
      fun kv g => RS12W.whittakerCoefficient_mul_right_eq_of_forall K _ _ x 1 g _ (fun y => (hconv v hv).1 kv y)
    have hTw : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome π hϖ0
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
          Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf π hϖ0)) = Θ.toRawCentral.a v * Wx g := by
      intro g
      have hWsum := RS12W.sum_whittakerCoefficient_mul_right_eq K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
        x 1 g repsO (Θ.toRawCentral.a v) hsumO (fun o => by
          simpa [WhittakerCoefficientIntegrable, mul_assoc] using hxint 1 (g * repsO o))
      simp only [hWx] at hWsum ⊢
      rw [Fintype.sum_option] at hWsum
      rw [add_comm, ← hWsum]
      congr 1
      simp only [hrepsO, hb, Option.elim]
      exact Equiv.sum_comp eI.symm (fun c' => whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
        (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome π hϖ0
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c'))))))
    have hZw : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        Wx (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi π hϖ0)) = Θ.toRawCentral.b v * Wx g := by
      intro g
      rw [RS12L_e13.placeEmbed_scalarPi]
      set z : (AdeleRing (𝓞 K) K)ˣ := RS12L_e13.zIdele K v π hϖ0 with hzdef
      have hz : Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) = z := by
        rw [← hgen]; exact RS12L_e13.det_placeEmbed_diagZ_one K v π hϖ0

      have hRZ : ∀ g' : AdelicGL2 (𝓞 K) K, R.toFun (centralScalar (𝓞 K) K z * g') =
          ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * R.toFun g' := by
        let : MeasurableSpace (AdelicGL2 (𝓞 K) K) := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)).mS
        let : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨(productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)).μ⟩
        intro g'
        exact R.smoothCusp.1.1.central_transform ⟨z, Subgroup.mem_top z⟩ g'
      have hRb : ∀ g' : AdelicGL2 (𝓞 K) K, R.toFun (centralScalar (𝓞 K) K z * g') = Θ.toRawCentral.b v * R.toFun g' := by
        intro g'
        have := R.central_eigen v hev g'
        rwa [show Matrix.GeneralLinearGroup.det ((productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)).gen v) = z from hz] at this
      obtain ⟨g', hg'⟩ := hRne
      have hξb : ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = Θ.toRawCentral.b v :=
        mul_right_cancel₀ hg' ((hRZ g').symm.trans (hRb g'))
      simp only [hWx]
      exact RS12W.whittakerCoefficient_mul_central K _ _ x 1 g _ _ (RS12L_e13.centralScalar_comm K z)
        (fun hh => by rw [hxZ z hh, hξb])
    exact ⟨ψv, ϖ, hϖ0, b, hgen, hϖval, hψ0, hψ1, hNw, hKw, hTw, hZw⟩
  exact locdata

end AutomorphicForm.SmoothCuspRealizationAt

end
