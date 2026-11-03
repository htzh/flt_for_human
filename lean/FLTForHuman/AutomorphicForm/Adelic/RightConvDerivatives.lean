/-
  The first-order structure of right convolution: along the unipotent flow, and under the complex
  Casimirs.

  Right convolution `rightConv φ f` is an operator on automorphic functions. This module carries its two
  differential properties:

  * `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` — for a
    continuous `φ` and a factorizable test function `f`, the one-parameter family
    `t ↦ rightConv φ f (g * unipotentGL2 (t • v))` has derivative `rightConv φ (∂_v f) g` at `0`, the
    derivative `∂_v f` is again factorizable, and `∂_{a v + b w} f = a ∂_v f + b ∂_w f` where `∂_v` is
    the left derivative `deriv (fun t => f (n(-t v) * ·)) 0`;
  * `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` — for a
    continuous, archimedean-smooth `x` with continuous first and second `archDerivAtComplex`
    derivatives, and any factorizable, arch-bi-finite test function, `rightConv x f` is smooth in the
    same sense and **both complex Casimirs commute past it**:
    `archCasimirAtComplex (rightConv x f) = rightConv (archCasimirAtComplex x) f`, and the same for
    `archCasimirBarAtComplex`.

  Transcribed from two pin `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear.lean`
  * `P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex.lean`

  The pin's file-level labels (`UnipDeriv`, `CommConvC41`) become the subject namespaces below.

  **Visibility follows the pin's**: both rows are flat public surfaces (thirty-four and eighteen
  declarations), so every helper here is a pin-public declaration that `check_port` diffs.

  **Wiring.** `spec/check_port.py` owns every public declaration here: the two wrappers and the two `S_`
  files are the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear.lean
  spec-pin: Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothComplex
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplex
-- The pin's row-3 file imports
-- `Theorems/Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn`
-- (line 7): the differentiation identity for `rightConv` is what row 3 transports the Casimir through,
-- and the port's home for it is `AutomorphicForm/Adelic/ArchDerivRightConvComplex.lean`.
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConvComplex
-- The pin's row-3 file imports `Theorems/Thm_AutomorphicForm_archDerivAtComplex_commutator_…` and
-- `Theorems/Thm_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_…` (lines 11–12): the
-- `𝔰𝔩₂(ℂ)` bracket table and the Casimir/L operator dictionary are what the recombination step
-- consumes, and the port's home for both is `AutomorphicForm/Adelic/ArchCasimirComplex.lean`.
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open Filter Set Topology Complex
open scoped Classical Topology

namespace AutomorphicForm

namespace LocalIntertwining

namespace UnipDeriv

variable (K : Type) [Field K] [NumberField K]

local notation "MS" K:max => mixedEmbedding.mixedSpace K
local notation "eA" K => InfiniteAdeleRing.ringEquiv_mixedSpace K
local notation "Ent" K:max => Fin 2 → Fin 2 → MS K

def nA (s : MS K) : AdelicGL2 (𝓞 K) K :=
  unipotentGL2 (R := AdeleRing (𝓞 K) K) (id (((eA K).symm s, 0) : AdeleRing (𝓞 K) K))

theorem nA_add (s r : MS K) : nA K (s + r) = nA K s * nA K r := by
  rw [nA, nA, nA, ← unipotentGL2_add]
  congr 1
  refine Prod.ext ?_ ?_
  · show (eA K).symm (s + r) = (eA K).symm s + (eA K).symm r; rw [map_add]
  · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) = 0 + 0; rw [add_zero]

theorem nA_zero : nA K 0 = 1 := by
  rw [nA]
  have : (((eA K).symm 0, (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K) = 0 := by
    refine Prod.ext ?_ ?_
    · show (eA K).symm 0 = 0; rw [map_zero]
    · rfl
  rw [this]
  exact unipotentGL2_zero

theorem nA_inv (s : MS K) : (nA K s)⁻¹ = nA K (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← nA_add, add_neg_cancel, nA_zero])

theorem glFin_nA (s : MS K) : glFin (𝓞 K) K (nA K s) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [glFin_apply]
  show ((!![(1 : AdeleRing (𝓞 K) K), ((eA K).symm s, 0); 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
  fin_cases i <;> fin_cases j <;> rfl

theorem glArch_nA (s : MS K) : glArch (𝓞 K) K (nA K s) = unipotentGL2 ((eA K).symm s) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [glArch_apply]
  show ((!![(1 : AdeleRing (𝓞 K) K), ((eA K).symm s, 0); 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 =
    (!![(1 : InfiniteAdeleRing K), (eA K).symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
  fin_cases i <;> fin_cases j <;> rfl

set_option linter.unusedSectionVars false in
theorem continuous_eA : Continuous (eA K) := by
  have h : ((eA K) : InfiniteAdeleRing K → MS K)
      = fun x => (fun (w : {w : InfinitePlace K // w.IsReal}) =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x w.1),
        fun (w : {w : InfinitePlace K // w.IsComplex}) =>
          InfinitePlace.Completion.extensionEmbedding w.1 (x w.1)) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [h]
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp (continuous_apply w.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp (continuous_apply w.1)

set_option linter.unusedSectionVars false in
theorem continuous_eA_symm : Continuous (eA K).symm := by
  refine continuous_pi fun w => ?_
  by_cases hw : w.IsReal
  · have h : ∀ z : MS K, (eA K).symm z w =
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm (z.1 ⟨w, hw⟩) := by
      intro z
      have hy : (eA K) ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
      have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((eA K).symm z w) = z.1 ⟨w, hw⟩ :=
        congrArg (fun p : MS K => p.1 ⟨w, hw⟩) hy
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact h1
    rw [show (fun z : MS K => (eA K).symm z w) = _ from funext h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h : ∀ z : MS K, (eA K).symm z w =
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').symm (z.2 ⟨w, hw'⟩) := by
      intro z
      have hy : (eA K) ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
      have h1 : InfinitePlace.Completion.extensionEmbedding w ((eA K).symm z w) = z.2 ⟨w, hw'⟩ :=
        congrArg (fun p : MS K => p.2 ⟨w, hw'⟩) hy
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').injective
      rw [IsometryEquiv.apply_symm_apply]
      exact h1
    rw [show (fun z : MS K => (eA K).symm z w) = _ from funext h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem continuous_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (unipotentGL2 (R := R)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ unipotentGL2 (R := R)) = fun x => !![(1 : R), x; 0, 1] := by funext x; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x => ((unipotentGL2 (R := R) x)⁻¹ : GL (Fin 2) R).val) = fun x => !![(1 : R), -x; 0, 1] := by
      funext x; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_nA : Continuous (nA K) :=
  (continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).comp
    ((continuous_eA_symm K).prodMk continuous_const)

def N (v : MS K) (m : Ent K) : Ent K := fun i j => if i = 0 then v * m 1 j else 0

set_option linter.unusedSectionVars false in
theorem N_add_smul (a b : ℝ) (v w : MS K) (m : Ent K) : N K (a • v + b • w) m = a • N K v m + b • N K w m := by
  funext i j
  simp only [N, Pi.add_apply, Pi.smul_apply]
  split_ifs
  · rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  · rw [smul_zero, smul_zero, add_zero]

theorem N_smul (a : ℝ) (v : MS K) (m : Ent K) : N K (a • v) m = a • N K v m := by
  have := N_add_smul K a 0 v 0 m
  simpa using this

theorem N_neg (v : MS K) (m : Ent K) : N K (-v) m = -N K v m := by
  have := N_smul K (-1) v m
  simpa using this

def NL (v : MS K) : Ent K →L[ℝ] Ent K :=
  LinearMap.toContinuousLinearMap
    { toFun := N K v
      map_add' := fun m m' => by funext i j; simp only [N, Pi.add_apply]; split_ifs <;> simp [mul_add]
      map_smul' := fun c m => by funext i j; simp only [N, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

theorem NL_apply (v : MS K) (m : Ent K) : NL K v m = N K v m := rfl

set_option linter.unusedSectionVars false in
theorem archEntries_unipotent_mul (s : MS K) (z : GL (Fin 2) (InfiniteAdeleRing K)) :
    archEntries K (unipotentGL2 ((eA K).symm s) * z) = archEntries K z + N K s (archEntries K z) := by
  funext i j
  simp only [archEntries_apply, Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply, N]
  set e : InfiniteAdeleRing K ≃+* MS K := InfiniteAdeleRing.ringEquiv_mixedSpace K with he
  clear_value e
  have h00 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 = 1 := rfl
  have h01 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = e.symm s := rfl
  have h10 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 := rfl
  have h11 : (!![(1 : InfiniteAdeleRing K), e.symm s; 0, 1] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 = 1 := rfl
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, map_add, map_mul, ↓reduceIte]
    rw [h00, h01, map_one, one_mul, RingEquiv.apply_symm_apply]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, add_zero]
    rw [h10, h11, zero_mul, one_mul, zero_add]

section Curve

variable {K}
variable {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
  {Φ : Ent K → ℂ} {f : AdelicGL2 (𝓞 K) K → ℂ}

abbrev E (y : AdelicGL2 (𝓞 K) K) : Ent K := archEntries K (glArch (𝓞 K) K y)

def Lf (Φ : Ent K → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) (v : MS K) (t : ℝ)
    (y : AdelicGL2 (𝓞 K) K) : ℂ :=
  (fderiv ℝ Φ (E y - t • N K v (E y))) (-N K v (E y)) * ff (glFin (𝓞 K) K y)

theorem curve_eq (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (v : MS K) (y : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    f (nA K (-(t • v)) * y) = Φ (E y - t • N K v (E y)) * ff (glFin (𝓞 K) K y) := by
  rw [hf, map_mul, map_mul, glFin_nA, one_mul, glArch_nA, hfa, archEntries_unipotent_mul, N_neg, N_smul, sub_eq_add_neg]

theorem hasDerivAt_curve (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (v : MS K) (y : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (nA K (-(s • v)) * y)) (Lf Φ ff v t y) t := by
  have hfun : (fun s : ℝ => f (nA K (-(s • v)) * y)) =
      fun s => Φ (E y - s • N K v (E y)) * ff (glFin (𝓞 K) K y) :=
    funext fun s => curve_eq hfa hf v y s
  rw [hfun, Lf]
  have hinner : HasDerivAt (fun s : ℝ => E y - s • N K v (E y)) (-N K v (E y)) t := by
    have := ((hasDerivAt_id t).smul_const (N K v (E y))).const_sub (E y)
    simpa using this
  have hdiff : DifferentiableAt ℝ Φ (E y - t • N K v (E y)) :=
    (hΦ.differentiable (by simp)).differentiableAt
  exact (hdiff.hasFDerivAt.comp_hasDerivAt t hinner).mul_const _

theorem deriv_curve (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (v : MS K) (y : AdelicGL2 (𝓞 K) K) :
    deriv (fun s : ℝ => f (nA K (-(s • v)) * y)) 0 = Lf Φ ff v 0 y :=
  (hasDerivAt_curve hΦ hfa hf v y 0).deriv

def Φv (Φ : Ent K → ℂ) (v : MS K) (m : Ent K) : ℂ := (fderiv ℝ Φ m) (-N K v m)

theorem Lf_zero (v : MS K) (y : AdelicGL2 (𝓞 K) K) :
    Lf Φ ff v 0 y = Φv Φ v (archEntries K (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y) := by
  simp only [Lf, Φv, zero_smul, sub_zero]

theorem contDiff_Φv (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : MS K) : ContDiff ℝ (⊤ : ℕ∞) (Φv Φ v) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Φ) := (contDiff_infty_iff_fderiv.1 hΦ).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun m : Ent K => -N K v m := (NL K v).contDiff.neg
  exact h1.clm_apply h2

theorem Φv_eq_zero (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z)) (v : MS K)
    {z : GL (Fin 2) (InfiniteAdeleRing K)} (hz : z ∉ tsupport fa) : Φv Φ v (archEntries K z) = 0 := by
  have hcurve : HasDerivAt (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z))
      (Φv Φ v (archEntries K z)) 0 := by
    have hfun : (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z)) =
        fun s => Φ (archEntries K z - s • N K v (archEntries K z)) := by
      funext s
      rw [hfa, archEntries_unipotent_mul, N_neg, N_smul, sub_eq_add_neg]
    rw [hfun, Φv]
    have hinner : HasDerivAt (fun s : ℝ => archEntries K z - s • N K v (archEntries K z))
        (-N K v (archEntries K z)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (N K v (archEntries K z))).const_sub (archEntries K z)
      simpa using this
    have hdiff : DifferentiableAt ℝ Φ (archEntries K z - (0 : ℝ) • N K v (archEntries K z)) :=
      (hΦ.differentiable (by simp)).differentiableAt
    have := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinner
    simp at this ⊢
    exact this
  have hcont : Continuous fun s : ℝ => unipotentGL2 ((eA K).symm (-(s • v))) * z :=
    (continuous_unipotentGL2.comp ((continuous_eA_symm K).comp (continuous_id.smul continuous_const).neg)).mul
      continuous_const
  have h0 : unipotentGL2 ((eA K).symm (-((0 : ℝ) • v))) * z = z := by
    rw [zero_smul, neg_zero, map_zero, unipotentGL2_zero, one_mul]
  have hev : (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have hmem : (tsupport fa)ᶜ ∈ 𝓝 (unipotentGL2 ((eA K).symm (-((0 : ℝ) • v))) * z) := by
      rw [h0]; exact (isClosed_tsupport fa).isOpen_compl.mem_nhds hz
    filter_upwards [hcont.continuousAt.preimage_mem_nhds hmem] with s hs
    exact image_eq_zero_of_notMem_tsupport hs
  have hzero : HasDerivAt (fun s : ℝ => fa (unipotentGL2 ((eA K).symm (-(s • v))) * z)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hev
  exact hcurve.unique hzero

theorem hasCompactSupport_Φv (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hsupp : HasCompactSupport fa) (v : MS K) : HasCompactSupport fun z => Φv Φ v (archEntries K z) := by
  refine hsupp.mono' fun z hz => ?_
  by_contra hzt
  exact hz (Φv_eq_zero hΦ hfa v hzt)

end Curve

theorem continuous_Lf {Φ : Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsLocallyConstant ff) (v : MS K) :
    Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => Lf Φ ff v p.1 p.2 := by
  have hE : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => E p.2 :=
    (continuous_archEntries K).comp ((continuous_glArch (𝓞 K) K).comp continuous_snd)
  have hN : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => N K v (E p.2) := (NL K v).continuous.comp hE
  have hpt : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => E p.2 - p.1 • N K v (E p.2) :=
    hE.sub (continuous_fst.smul hN)
  have hD : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => fderiv ℝ Φ (E p.2 - p.1 • N K v (E p.2)) :=
    (hΦ.continuous_fderiv (by simp)).comp hpt
  have hff' : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => ff (glFin (𝓞 K) K p.2) :=
    hff.continuous.comp ((continuous_glFin (𝓞 K) K).comp continuous_snd)
  unfold Lf
  exact (hD.clm_apply hN.neg).mul hff'

theorem main (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {Φ : Ent K → ℂ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z)) (hff : IsLocallyConstant ff)
    (hf : ∀ g, f g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (hfc : Continuous f) (hfs : HasCompactSupport f) (v : MS K) (g : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun t : ℝ => rightConv K φ f (g * nA K (t • v))) (rightConv K φ (Lf Φ ff v 0) g) 0 := by
  let _meas : MeasurableSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  have _borel : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have _haar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  have ha : ∀ t : ℝ, rightConv K φ f (g * nA K (t • v)) = ∫ y, φ (g * y) * f (nA K (-(t • v)) * y) ∂μ := by
    intro t
    rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, nA_inv, rightConv_apply]

  set F : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t y => φ (g * y) * f (nA K (-(t • v)) * y) with hF
  set F' : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t y => φ (g * y) * Lf Φ ff v t y with hF'
  have hderiv : ∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), HasDerivAt (fun s => F s y) (F' t y) t := fun y t =>
    (hasDerivAt_curve hΦ hfa hf v y t).const_mul _

  set C : Set (AdelicGL2 (𝓞 K) K) := (fun p : ℝ × AdelicGL2 (𝓞 K) K => nA K (p.1 • v) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport f) with hC
  have hCcpt : IsCompact C :=
    ((isCompact_closedBall (0 : ℝ) 1).prod hfs).image
      (((continuous_nA K).comp (continuous_fst.smul continuous_const)).mul continuous_snd)
  have hout : ∀ y, y ∉ C → ∀ t ∈ Metric.ball (0 : ℝ) 1, F' t y = 0 := by
    intro y hy t ht
    have hoff : ∀ s ∈ Metric.ball (0 : ℝ) 1, f (nA K (-(s • v)) * y) = 0 := by
      intro s hs
      by_contra hne
      apply hy
      refine ⟨(s, nA K (-(s • v)) * y), ⟨Metric.ball_subset_closedBall hs, subset_tsupport _ hne⟩, ?_⟩
      show nA K (s • v) * (nA K (-(s • v)) * y) = y
      rw [← mul_assoc, ← nA_add, add_neg_cancel, nA_zero, one_mul]
    have hev : (fun s : ℝ => f (nA K (-(s • v)) * y)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
      exact hoff s hs
    have hz : HasDerivAt (fun s : ℝ => f (nA K (-(s • v)) * y)) 0 t :=
      (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hev
    have := (hasDerivAt_curve hΦ hfa hf v y t).unique hz
    show φ (g * y) * Lf Φ ff v t y = 0
    rw [this, mul_zero]

  have hF'cont : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => F' p.1 p.2 :=
    ((hcont.comp (continuous_const.mul continuous_snd))).mul (continuous_Lf K hΦ hff v)
  obtain ⟨Mb, hMb⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hCcpt).exists_bound_of_continuousOn
    hF'cont.continuousOn
  have hCm : MeasurableSet C := hCcpt.isClosed.measurableSet
  have hbound_int : Integrable (fun y => if y ∈ C then Mb else 0) μ :=
    (integrableOn_const (C := Mb) hCcpt.measure_lt_top.ne).integrable_indicator hCm
  have h_bound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t y‖ ≤ if y ∈ C then Mb else 0 := by
    refine Eventually.of_forall fun y t ht => ?_
    by_cases hy : y ∈ C
    · rw [ite_eq_left hy]; exact hMb (t, y) ⟨Metric.ball_subset_closedBall ht, hy⟩
    · rw [ite_eq_right hy, hout y hy t ht, norm_zero]

  have hFt : ∀ t : ℝ, Continuous (F t) := fun t =>
    (hcont.comp (continuous_const.mul continuous_id)).mul (hfc.comp (continuous_const.mul continuous_id))
  have hint0 : Integrable (F 0) μ := by
    have hsupp : HasCompactSupport (F 0) := by
      have h1 : HasCompactSupport fun y : AdelicGL2 (𝓞 K) K => f (nA K (-((0 : ℝ) • v)) * y) := by
        rw [zero_smul, neg_zero, nA_zero]; simpa using hfs
      exact h1.mul_left
    exact (hFt 0).integrable_of_hasCompactSupport hsupp
  have hF'0m : AEStronglyMeasurable (F' 0) μ :=
    (hF'cont.comp ((continuous_const : Continuous fun _ : AdelicGL2 (𝓞 K) K => (0 : ℝ)).prodMk
      continuous_id)).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (s := Metric.ball (0 : ℝ) 1) (bound := fun y => if y ∈ C then Mb else 0) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => (hFt t).aestronglyMeasurable) hint0 hF'0m h_bound hbound_int
    (Eventually.of_forall fun y t _ => hderiv y t)

  have hfun : (fun t : ℝ => rightConv K φ f (g * nA K (t • v))) = fun t => ∫ y, F t y ∂μ := funext ha
  have hval : (∫ y, F' 0 y ∂μ) = rightConv K φ (Lf Φ ff v 0) g := by rw [rightConv_apply]
  rw [hfun, ← hval]
  exact key.2

end UnipDeriv


namespace ComplexCasimirComm

open MeasureTheory NumberField.InfinitePlace Complex

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

local notation "G2" => AdelicGL2 (𝓞 F) F

def word (T : ArchDirComplex → (G2 → ℂ) → (G2 → ℂ)) (α : G2 → ℂ) : Fin 10 → (G2 → ℂ) :=
  ![T .H (T .H α), T .H (T .iH α), T .iH (T .H α), T .iH (T .iH α), T .H α, T .iH α,
    T .E (T .Fm α), T .E (T .iFm α), T .iE (T .Fm α), T .iE (T .iFm α)]

def wordR (T : ArchDirComplex → (G2 → ℂ) → (G2 → ℂ)) (α : G2 → ℂ) : Fin 10 → (G2 → ℂ) :=
  ![T .H (T .H α), T .iH (T .H α), T .H (T .iH α), T .iH (T .iH α), T .H α, T .iH α,
    T .Fm (T .E α), T .iFm (T .E α), T .Fm (T .iE α), T .iFm (T .iE α)]

def coef (c : ℂ) : Fin 10 → ℂ :=
  ![-(1 / 16), -(c / 16), -(c / 16), 1 / 16, 1 / 4, c / 4, -(1 / 4), -(c / 4), -(c / 4), 1 / 4]

def sgn : Fin 10 → ℂ := ![1, 1, 1, 1, -1, -1, 1, 1, 1, 1]

theorem archDerivAtComplex_sub_smul {φ ψ : G2 → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) (c : ℂ) :
    archDerivAtComplex hw d (φ - c • ψ) = archDerivAtComplex hw d φ - c • archDerivAtComplex hw d ψ := by
  rw [sub_eq_add_neg, ← neg_smul, archDerivAtComplex_add hφ (hψ.smul _), archDerivAtComplex_smul, neg_smul,
    ← sub_eq_add_neg]

theorem archDerivAtComplex_add_smul {φ ψ : G2 → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) (c : ℂ) :
    archDerivAtComplex hw d (φ + c • ψ) = archDerivAtComplex hw d φ + c • archDerivAtComplex hw d ψ := by
  rw [archDerivAtComplex_add hφ (hψ.smul _), archDerivAtComplex_smul]

theorem casimir_apply_eq_sum {φ : G2 → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (y : G2) :
    archCasimirAtComplex hw φ y = ∑ k : Fin 10, coef (-Complex.I) k * word (archDerivAtComplex hw) φ k y := by
  have h1 : archDelAt hw .H φ = (1 / 2 : ℂ) • (archDerivAtComplex hw .H φ - Complex.I • archDerivAtComplex hw .iH φ) := rfl
  have h2 : archDelAt hw .Fm φ = (1 / 2 : ℂ) • (archDerivAtComplex hw .Fm φ - Complex.I • archDerivAtComplex hw .iFm φ) := rfl
  have sH := hφ.archDerivAtComplex .H
  have siH := hφ.archDerivAtComplex .iH
  have sFm := hφ.archDerivAtComplex .Fm
  have siFm := hφ.archDerivAtComplex .iFm
  unfold archCasimirAtComplex
  rw [h1, h2]
  unfold archDelAt
  simp only [show ArchDir.toComplex .H = ArchDirComplex.H from rfl,
    show ArchDir.toComplexI .H = ArchDirComplex.iH from rfl,
    show ArchDir.toComplex .E = ArchDirComplex.E from rfl,
    show ArchDir.toComplexI .E = ArchDirComplex.iE from rfl]
  rw [archDerivAtComplex_smul, archDerivAtComplex_smul, archDerivAtComplex_smul, archDerivAtComplex_smul,
    archDerivAtComplex_sub_smul hw sH siH, archDerivAtComplex_sub_smul hw sH siH,
    archDerivAtComplex_sub_smul hw sFm siFm, archDerivAtComplex_sub_smul hw sFm siFm]
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, word, coef, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) y -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) y) * Complex.I_mul_I

theorem casimirBar_apply_eq_sum {φ : G2 → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (y : G2) :
    archCasimirBarAtComplex hw φ y = ∑ k : Fin 10, coef Complex.I k * word (archDerivAtComplex hw) φ k y := by
  have h1 : archDelBarAt hw .H φ = (1 / 2 : ℂ) • (archDerivAtComplex hw .H φ + Complex.I • archDerivAtComplex hw .iH φ) := rfl
  have h2 : archDelBarAt hw .Fm φ = (1 / 2 : ℂ) • (archDerivAtComplex hw .Fm φ + Complex.I • archDerivAtComplex hw .iFm φ) := rfl
  have sH := hφ.archDerivAtComplex .H
  have siH := hφ.archDerivAtComplex .iH
  have sFm := hφ.archDerivAtComplex .Fm
  have siFm := hφ.archDerivAtComplex .iFm
  unfold archCasimirBarAtComplex
  rw [h1, h2]
  unfold archDelBarAt
  simp only [show ArchDir.toComplex .H = ArchDirComplex.H from rfl,
    show ArchDir.toComplexI .H = ArchDirComplex.iH from rfl,
    show ArchDir.toComplex .E = ArchDirComplex.E from rfl,
    show ArchDir.toComplexI .E = ArchDirComplex.iE from rfl]
  rw [archDerivAtComplex_smul, archDerivAtComplex_smul, archDerivAtComplex_smul, archDerivAtComplex_smul,
    archDerivAtComplex_add_smul hw sH siH, archDerivAtComplex_add_smul hw sH siH,
    archDerivAtComplex_add_smul hw sFm siFm, archDerivAtComplex_add_smul hw sFm siFm]
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, word, coef, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) y -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) y) * Complex.I_mul_I

section Lin

omit hw

theorem integrable_integrand {x : G2 → ℂ} (hx : Continuous x) {β : G2 → ℂ} (hβ : Continuous β)
    (hβc : HasCompactSupport β) (g : G2) :
    letI : MeasurableSpace G2 := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
    Integrable (fun y => x (g * y) * β y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  let _meas : MeasurableSpace G2 := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  have _borel : BorelSpace G2 := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have _haar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hc : Continuous fun y : G2 => x (g * y) * β y := (hx.comp (continuous_const.mul continuous_id)).mul hβ
  exact hc.integrable_of_hasCompactSupport hβc.mul_left

theorem rightConv_sum_right {m : ℕ} {x : G2 → ℂ} (hx : Continuous x) (β : Fin m → G2 → ℂ)
    (hβ : ∀ k, Continuous (β k)) (hβc : ∀ k, HasCompactSupport (β k)) (c : Fin m → ℂ) (g : G2) :
    rightConv F x (fun y => ∑ k, c k * β k y) g = ∑ k, c k * rightConv F x (β k) g := by
  let _meas : MeasurableSpace G2 := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  simp only [rightConv_apply]
  have hint : ∀ k ∈ Finset.univ, Integrable (fun y => c k * (x (g * y) * β k y))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    fun k _ => (integrable_integrand hx (hβ k) (hβc k) g).const_mul (c k)
  have hfun : (fun y => x (g * y) * ∑ k, c k * β k y) = fun y => ∑ k, c k * (x (g * y) * β k y) := by
    funext y; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [hfun, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

theorem rightConv_sum_left {m : ℕ} (u : Fin m → G2 → ℂ) (hu : ∀ k, Continuous (u k)) {β : G2 → ℂ}
    (hβ : Continuous β) (hβc : HasCompactSupport β) (c : Fin m → ℂ) (g : G2) :
    rightConv F (fun y => ∑ k, c k * u k y) β g = ∑ k, c k * rightConv F (u k) β g := by
  let _meas : MeasurableSpace G2 := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  simp only [rightConv_apply]
  have hint : ∀ k ∈ Finset.univ, Integrable (fun y => c k * (u k (g * y) * β y))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    fun k _ => (integrable_integrand (hu k) hβ hβc g).const_mul (c k)
  have hfun : (fun y => (∑ k, c k * u k (g * y)) * β y) = fun y => ∑ k, c k * (u k (g * y) * β y) := by
    funext y; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [hfun, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

end Lin

def Lf (d : ArchDirComplex) (β : G2 → ℂ) : G2 → ℂ :=
  fun y => deriv (fun t : ℝ => β (archFlowAtComplex hw d (-t) * y)) 0

theorem isFactorizableTestFn_Lf (d : ArchDirComplex) {β : G2 → ℂ} (hβ : IsFactorizableTestFn F β) :
    IsFactorizableTestFn F (Lf hw d β) := by
  obtain ⟨fa, ff, hfa, hff, hβeq⟩ := hβ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.1 fa ff hfa
  refine ⟨fa', ff, hfa', hff, fun y => ?_⟩
  have h1 : Lf hw d β y = deriv (fun t : ℝ => fa (glArch (𝓞 F) F (archFlowAtComplex hw d (-t) * y)) *
      ff (glFin (𝓞 F) F (archFlowAtComplex hw d (-t) * y))) 0 := by
    simp only [Lf, hβeq]
  rw [h1]
  exact congrFun heq y

theorem conv_smooth_and_deriv {x : G2 → ℂ} (hx : Continuous x) (d : ArchDirComplex)
    {β : G2 → ℂ} (hβ : IsFactorizableTestFn F β) :
    IsArchSmoothAtComplex hw (rightConv F x β) ∧
      archDerivAtComplex hw d (rightConv F x β) = rightConv F x (Lf hw d β) :=
  (AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1 x β hx hβ

omit hw in
theorem continuous_conv {x : G2 → ℂ} (hx : Continuous x) {β : G2 → ℂ}
    (hβ : IsFactorizableTestFn F β) : Continuous (rightConv F x β) :=
  (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F x hx β hβ).1

omit hw in
theorem reg {β : G2 → ℂ} (hβ : IsFactorizableTestFn F β) : Continuous β ∧ HasCompactSupport β :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ hβ

theorem main (x : G2 → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (α : G2 → ℂ) (hα : IsFactorizableTestFn F α) :
    IsArchSmoothAtComplex hw (rightConv F x α) ∧
    (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv F x α))) ∧
    (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv F x α)))) ∧
    archCasimirAtComplex hw (rightConv F x α) = rightConv F (archCasimirAtComplex hw x) α ∧
    archCasimirBarAtComplex hw (rightConv F x α) = rightConv F (archCasimirBarAtComplex hw x) α := by
  obtain ⟨hαs, fa, ff, hfa, hff, hαeq, hDα⟩ :=
    AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor F w hw α hα
  have hfactD : ∀ d : ArchDirComplex, IsFactorizableTestFn F (archDerivAtComplex hw d α) := by
    intro d
    obtain ⟨fa', hfa', h⟩ := hDα d
    exact ⟨fa', ff, hfa', hff, h⟩
  have hfactDD : ∀ d d' : ArchDirComplex, IsFactorizableTestFn F (archDerivAtComplex hw d (archDerivAtComplex hw d' α)) := by
    intro d d'
    obtain ⟨-, fa₁, ff₁, hfa₁, hff₁, -, hD⟩ :=
      AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor F w hw _ (hfactD d')
    obtain ⟨fa', hfa', h⟩ := hD d
    exact ⟨fa', ff₁, hfa', hff₁, h⟩
  have hLfact : ∀ d, IsFactorizableTestFn F (Lf hw d α) := fun d => isFactorizableTestFn_Lf hw d hα
  have hLLfact : ∀ d d', IsFactorizableTestFn F (Lf hw d (Lf hw d' α)) := fun d d' => isFactorizableTestFn_Lf hw d (hLfact d')
  have hconvs : IsArchSmoothAtComplex hw (rightConv F x α) := (conv_smooth_and_deriv hw hxc .H hα).1
  have hDconv : ∀ d, archDerivAtComplex hw d (rightConv F x α) = rightConv F x (Lf hw d α) :=
    fun d => (conv_smooth_and_deriv hw hxc d hα).2
  have hDDconv : ∀ d d', archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv F x α)) =
      rightConv F x (Lf hw d (Lf hw d' α)) := by
    intro d d'
    rw [hDconv d', (conv_smooth_and_deriv hw hxc d (hLfact d')).2]
  refine ⟨hconvs, fun d => ?_, fun d d' => ?_, ?_⟩
  · rw [hDconv d]; exact continuous_conv hxc (hLfact d)
  · rw [hDDconv d d']; exact continuous_conv hxc (hLLfact d d')
  have hwordL : ∀ k : Fin 10, word (archDerivAtComplex hw) (rightConv F x α) k =
      rightConv F x (word (Lf hw) α k) := by
    intro k
    fin_cases k <;> simp only [word, Matrix.cons_val_zero, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      first | exact hDDconv _ _ | exact hDconv _
  have hLreg : ∀ k : Fin 10, Continuous (word (Lf hw) α k) ∧ HasCompactSupport (word (Lf hw) α k) := by
    intro k
    fin_cases k <;> simp only [word] <;> first
      | exact reg (hLLfact _ _) | exact reg (hLfact _)
  have hIBP : ∀ (d : ArchDirComplex) {φ γ : G2 → ℂ}, Continuous φ → IsArchSmoothAtComplex hw φ →
      Continuous (archDerivAtComplex hw d φ) → Continuous γ → HasCompactSupport γ → IsArchSmoothAtComplex hw γ →
      Continuous (archDerivAtComplex hw d γ) →
      rightConv F (archDerivAtComplex hw d φ) γ = -rightConv F φ (archDerivAtComplex hw d γ) := by
    intro d φ γ hφ hφs hφ' hγ hγc hγs hγ'
    have h := (AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.2 φ γ
      (fun _ => 1) hφ hφs hφ' hγ hγc hγs hγ' continuous_const (fun _ _ => rfl)
    simp only [mul_one] at h
    rw [h, neg_neg]
  have hα1 := reg hα
  have hDα1 : ∀ d, Continuous (archDerivAtComplex hw d α) ∧ HasCompactSupport (archDerivAtComplex hw d α) :=
    fun d => reg (hfactD d)
  have hDDα1 : ∀ d d', Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' α)) ∧
      HasCompactSupport (archDerivAtComplex hw d (archDerivAtComplex hw d' α)) := fun d d' => reg (hfactDD d d')
  have e2 : ∀ d d', rightConv F (archDerivAtComplex hw d (archDerivAtComplex hw d' x)) α =
      rightConv F x (archDerivAtComplex hw d' (archDerivAtComplex hw d α)) := by
    intro d d'
    rw [hIBP d (hD1 d') (hxs.archDerivAtComplex d') (hD2 d d') hα1.1 hα1.2 hαs (hDα1 d).1,
      hIBP d' hxc hxs (hD1 d') (hDα1 d).1 (hDα1 d).2 (hαs.archDerivAtComplex d) (hDDα1 d' d).1, neg_neg]
  have e1 : ∀ d, rightConv F (archDerivAtComplex hw d x) α = -rightConv F x (archDerivAtComplex hw d α) :=
    fun d => hIBP d hxc hxs (hD1 d) hα1.1 hα1.2 hαs (hDα1 d).1
  have hwordR : ∀ k : Fin 10, rightConv F (word (archDerivAtComplex hw) x k) α =
      sgn k • rightConv F x (wordR (archDerivAtComplex hw) α k) := by
    intro k
    fin_cases k <;> simp [word, wordR, sgn, e1, e2]
  have hxreg : ∀ k : Fin 10, Continuous (word (archDerivAtComplex hw) x k) := by
    intro k
    fin_cases k <;> simp only [word] <;> first | exact hD2 _ _ | exact hD1 _
  have hRreg : ∀ k : Fin 10, Continuous (wordR (archDerivAtComplex hw) α k) ∧ HasCompactSupport (wordR (archDerivAtComplex hw) α k) := by
    intro k
    fin_cases k <;> simp only [wordR] <;> first
      | exact hDDα1 _ _ | exact hDα1 _
  obtain ⟨-, -, cEF, -, -, cEiF, ciEF, -, -, -, -, ciEiF, cHiH, -, -⟩ :=
    AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw α hαs
  have hrecomb : ∀ (c : ℂ) (y : G2), ∑ k : Fin 10, coef c k * (sgn k * wordR (archDerivAtComplex hw) α k y) =
      ∑ k : Fin 10, coef c k * word (archDerivAtComplex hw) α k y := by
    intro c y
    have b1 := congrFun cEF y
    have b2 := congrFun cEiF y
    have b3 := congrFun ciEF y
    have b4 := congrFun ciEiF y
    have b5 := congrFun cHiH y
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at b1 b2 b3 b4 b5
    simp only [word, wordR, coef, sgn, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    linear_combination (1 / 4 : ℂ) * b1 + (c / 4) * b2 + (c / 4) * b3 + (-(1 / 4 : ℂ)) * b4
  have key : ∀ (c : ℂ) (casOp : (G2 → ℂ) → (G2 → ℂ)),
      (∀ (φ : G2 → ℂ), IsArchSmoothAtComplex hw φ → ∀ y, casOp φ y = ∑ k : Fin 10, coef c k * word (archDerivAtComplex hw) φ k y) →
      (∀ y, (∑ k : Fin 10, coef c k * word (Lf hw) α k y) = casOp α y) →
      casOp (rightConv F x α) = rightConv F (casOp x) α := by
    intro c casOp hcas hleft
    funext g
    have s1 : casOp (rightConv F x α) g = rightConv F x (casOp α) g := by
      rw [hcas _ hconvs]
      have : (fun y => ∑ k : Fin 10, coef c k * word (Lf hw) α k y) = casOp α := funext hleft
      rw [← this, rightConv_sum_right hxc _ (fun k => (hLreg k).1) (fun k => (hLreg k).2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hwordL]
    have s2 : rightConv F (casOp x) α g = rightConv F x (casOp α) g := by
      have hx' : casOp x = fun y => ∑ k : Fin 10, coef c k * word (archDerivAtComplex hw) x k y := funext (hcas x hxs)
      have hα' : casOp α = fun y => ∑ k : Fin 10, coef c k * (sgn k * wordR (archDerivAtComplex hw) α k y) := by
        funext y; rw [hrecomb, hcas α hαs]
      rw [hx', rightConv_sum_left _ hxreg hα1.1 hα1.2, hα']
      have hfun : (fun y => ∑ k : Fin 10, coef c k * (sgn k * wordR (archDerivAtComplex hw) α k y)) =
          fun y => ∑ k : Fin 10, (coef c k * sgn k) * wordR (archDerivAtComplex hw) α k y := by
        funext y; refine Finset.sum_congr rfl fun k _ => ?_; ring
      rw [hfun, rightConv_sum_right hxc _ (fun k => (hRreg k).1) (fun k => (hRreg k).2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hwordR]; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [s1, s2]
  have hcent := AutomorphicForm.leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex F w hw α hαs
  have hleft : ∀ y, (∑ k : Fin 10, coef (-Complex.I) k * word (Lf hw) α k y) = archCasimirAtComplex hw α y := by
    intro y
    rw [← (hcent y).1]
    simp only [word, coef, Lf, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    ring
  have hleftBar : ∀ y, (∑ k : Fin 10, coef Complex.I k * word (Lf hw) α k y) = archCasimirBarAtComplex hw α y := by
    intro y
    rw [← (hcent y).2]
    simp only [word, coef, Lf, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    ring
  exact ⟨key (-Complex.I) (archCasimirAtComplex hw) (fun φ hφ y => casimir_apply_eq_sum hw hφ y) hleft,
    key Complex.I (archCasimirBarAtComplex hw) (fun φ hφ y => casimirBar_apply_eq_sum hw hφ y) hleftBar⟩

end ComplexCasimirComm

end LocalIntertwining

open LocalIntertwining.UnipDeriv in
theorem hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    (∀ (v : mixedEmbedding.mixedSpace K) (g : AdelicGL2 (𝓞 K) K),
        HasDerivAt (fun t : ℝ => rightConv K φ f (g * unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)))
          (rightConv K φ (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) g) 0) ∧
    (∀ v : mixedEmbedding.mixedSpace K,
        IsFactorizableTestFn K (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0)) ∧
    (∀ (a b : ℝ) (v w : mixedEmbedding.mixedSpace K) (y : AdelicGL2 (𝓞 K) K),
        deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • (a • v + b • w))), 0) * y)) 0 =
          a * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0 +
            b * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • w)), 0) * y)) 0) := by
  classical
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, ⟨hff, hffs⟩, hfeq⟩ := hf

  have hL : ∀ (v : mixedEmbedding.mixedSpace K) (y : AdelicGL2 (𝓞 K) K),
      deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0 = Lf Φ ff v 0 y :=
    fun v y => deriv_curve hΦ hfa hfeq v y
  refine ⟨fun v g => ?_, fun v => ?_, fun a b v w y => ?_⟩
  · have h := main K φ hcont f hΦ hfa hff hfeq hfc hfs v g
    have hfun : (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) = Lf Φ ff v 0 :=
      funext (hL v)
    rw [hfun]
    exact h
  · refine ⟨fun z => Φv Φ v (archEntries K z), ff, ⟨⟨Φv Φ v, contDiff_Φv hΦ v, fun _ => rfl⟩,
      hasCompactSupport_Φv hΦ hfa hsupp v⟩, ⟨hff, hffs⟩, fun y => ?_⟩
    beta_reduce
    rw [hL v y, Lf_zero]
  · rw [hL, hL, hL, Lf_zero, Lf_zero, Lf_zero]
    simp only [Φv, N_add_smul, neg_add, map_add, map_neg, map_smul, Complex.real_smul]
    ring


open LocalIntertwining.ComplexCasimirComm in
theorem archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAtComplex hw (rightConv K x f) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x f)))) ∧
        archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f ∧
        archCasimirBarAtComplex hw (rightConv K x f) = rightConv K (archCasimirBarAtComplex hw x) f := by
  intro f tys hf _
  exact main hw x hxc hxs hD1 hD2 f hf

end AutomorphicForm
