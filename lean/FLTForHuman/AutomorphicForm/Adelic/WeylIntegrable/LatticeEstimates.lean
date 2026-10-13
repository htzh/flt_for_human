/-
  The lattice, place and archimedean estimates for the Bruhat transversal.

  `apply_weyl_unipotent_eq`/`norm_apply_weyl_unipotent_eq` compute the Weyl–unipotent
  norm as the `α`-weight of `yUnit` times `‖φ (mFactor · g)‖`. `Lattices` and `R2`
  build the uniformizer lattices `latt k`, their `relIndex` bookkeeping and the
  `normProd` product of absolute norms; `Fin` sums the `zetaTerm` ideal count over
  the finite places; `Place`/`Arch` integrate the place weights against the
  archimedean Haar measure. These are the `S4Base`-to-`Asm` middle estimates.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 1330–2089 (pinned `aa2d8b3`), sections `PositiveChar`, `Pointwise`, `Lattices`,
  `R2`, `Fin`, `Place`, `Arch` of the pin namespace `AutomorphicForm.WeylIntegrable`.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.BoxBounds
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicHaar
open NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter Asymptotics TopologicalSpace WithZero M4aS4
open scoped Classical ENNReal NNReal Topology Pointwise nonZeroDivisors

noncomputable section

open scoped Classical

namespace AutomorphicForm
namespace WeylIntegrable

section PositiveChar

variable {G : Type*} [Group G]

-- pin: val_eq_one_of_mul_self_eq_one (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1344)
theorem val_eq_one_of_mul_self_eq_one (α : G →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {e : G} (he : e * e = 1) :
    ((α e : ℝˣ) : ℝ) = 1 := by
  have h : ((α e : ℝˣ) : ℝ) * ((α e : ℝˣ) : ℝ) = 1 := by rw [← Units.val_mul, ← map_mul, he, map_one, Units.val_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · exact absurd (hα e) (by rw [h1]; norm_num)

end PositiveChar

section Pointwise

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

-- pin: apply_weyl_unipotent_eq (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1362)
theorem apply_weyl_unipotent_eq (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (u : 𝔸) (g : AdelicGL2 (𝓞 F) F) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g) =
      ((etaFst μ α hα s (eUnit (selRel F u.1 u.2) * (yUnit (selRel F u.1 u.2))⁻¹) : ℂˣ) : ℂ) *
        ((etaSnd ν α hα s (yUnit (selRel F u.1 u.2)) : ℂˣ) : ℂ) * φ (mFactor F u.1 u.2 * g) := by
  rw [weyl_unipotent_eq F u, mul_assoc, hφ _ (bFactor_mem_borel (selRel F u.1 u.2)) (mFactor F u.1 u.2 * g),
    borelDiagFst_bFactor, borelDiagSnd_bFactor]

-- pin: norm_apply_weyl_unipotent_eq (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1370)
theorem norm_apply_weyl_unipotent_eq (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (u : 𝔸) (g : AdelicGL2 (𝓞 F) F) :
    ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ =
      ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) * ‖φ (mFactor F u.1 u.2 * g)‖ := by
  set h := selRel F u.1 u.2
  set t : ℝ := ((α (yUnit h) : ℝˣ) : ℝ) with ht
  have htpos : 0 < t := hα _
  have he : ((α (eUnit h) : ℝˣ) : ℝ) = 1 := val_eq_one_of_mul_self_eq_one α hα (eUnit_mul_self h)
  have h1 : ‖((etaFst μ α hα s (eUnit h * (yUnit h)⁻¹) : ℂˣ) : ℂ)‖ = t⁻¹ ^ (s.re + 1 / 2) := by
    rw [etaFst_apply, Units.val_mul, norm_mul, hμ, one_mul, norm_cpowChar_apply, map_mul, map_inv, Units.val_mul, he, one_mul,
      Units.val_inv_eq_inv_val, ← ht]
    norm_num
  have h2 : ‖(((etaSnd ν α hα s (yUnit h)) : ℂˣ) : ℂ)‖ = t ^ (-(s.re + 1 / 2)) := by
    rw [etaSnd_apply, Units.val_mul, norm_mul, hν, one_mul, norm_cpowChar_apply, ← ht]
    norm_num
  rw [apply_weyl_unipotent_eq F α hα μ ν s φ hφ u g, norm_mul, norm_mul, h1, h2, Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le,
    ← Real.rpow_add htpos]
  congr 2
  ring

-- pin: norm_apply_weyl_unipotent_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1391)
theorem norm_apply_weyl_unipotent_le (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : 𝔸, ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ ≤
      B * ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) := by
  obtain ⟨B, hB⟩ := exists_bound_mFactor F hφc g
  refine ⟨max B 0, le_max_right _ _, fun u => ?_⟩
  rw [norm_apply_weyl_unipotent_eq F α hα μ ν s φ hμ hν hφ u g, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hB u.1 u.2).trans (le_max_left _ _)) (Real.rpow_nonneg (hα _).le _)

end Pointwise

end AutomorphicForm.WeylIntegrable

end

noncomputable section

open scoped Classical

namespace AutomorphicForm
namespace WeylIntegrable

section Lattices

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

-- pin: fa_mul_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1428)
theorem fa_mul_apply (a b : 𝔸f) (v : HOS) : (a * b) v = a v * b v := rfl

-- pin: mem_intLattice_iff (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1430)
theorem mem_intLattice_iff (t : 𝔸f) : t ∈ intLattice F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

-- pin: mem_integralFiniteAdeles_iff' (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1432)
theorem mem_integralFiniteAdeles_iff' (t : 𝔸f) : t ∈ integralFiniteAdeles (𝓞 F) F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

-- pin: valued_ne_zero_of_unit (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1434)
theorem valued_ne_zero_of_unit (y : (𝔸f)ˣ) (v : HOS) : Valued.v ((y : 𝔸f) v) ≠ 0 := by
  intro h
  have h1 : Valued.v (((y : 𝔸f) * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f)) v) = 1 := by rw [Units.mul_inv]; exact map_one _
  rw [fa_mul_apply, map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

-- pin: apply_ne_zero_of_unit (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1440)
theorem apply_ne_zero_of_unit (y : (𝔸f)ˣ) (v : HOS) : (y : 𝔸f) v ≠ 0 := fun h =>
  valued_ne_zero_of_unit F y v (by rw [h, map_zero])

-- pin: mem_dilate_iff (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1443)
theorem mem_dilate_iff (y : (𝔸f)ˣ) (t : 𝔸f) : t ∈ dilate F y ↔ ∀ v, Valued.v (t v) ≤ Valued.v ((y : 𝔸f) v) := by
  rw [← SetLike.mem_coe, coe_dilate, Set.mem_smul_set]
  constructor
  · rintro ⟨s, hs, rfl⟩ v
    rw [smul_eq_mul, fa_mul_apply, map_mul]
    exact mul_le_of_le_one_right' ((mem_integralFiniteAdeles_iff' F s).mp hs v)
  · intro h
    refine ⟨((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t, (mem_integralFiniteAdeles_iff' F _).mpr fun v => ?_, ?_⟩
    · rw [fa_mul_apply, map_mul]
      have hy := valued_ne_zero_of_unit F y v
      have hyv : (y : 𝔸f) v * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v = 1 := by rw [← fa_mul_apply, Units.mul_inv]; rfl
      have hinv : Valued.v (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v) = (Valued.v ((y : 𝔸f) v))⁻¹ := by
        rw [← inv_eq_of_mul_eq_one_right hyv, map_inv₀]
      rw [hinv]
      calc (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v (t v) ≤ (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v ((y : 𝔸f) v) :=
            mul_le_mul' le_rfl (h v)
        _ = 1 := inv_mul_cancel₀ hy
    · show (y : 𝔸f) * (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t) = t
      rw [← mul_assoc, Units.mul_inv, one_mul]

-- pin: intLattice_le_dilate (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1463)
theorem intLattice_le_dilate {y : (𝔸f)ˣ} (hy : ∀ v, 1 ≤ Valued.v ((y : 𝔸f) v)) : intLattice F ≤ dilate F y := fun t ht =>
  (mem_dilate_iff F y t).mpr fun v => (((mem_intLattice_iff F t).mp ht v).trans (hy v))

-- pin: isCompact_dilate (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1466)
theorem isCompact_dilate (y : (𝔸f)ˣ) : IsCompact (dilate F y : Set 𝔸f) := by
  rw [coe_dilate]
  exact (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

-- pin: relIndex_dilate_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1470)
theorem relIndex_dilate_ne_zero (y : (𝔸f)ˣ) : (intLattice F).relIndex (dilate F y) ≠ 0 := by
  have : CompactSpace (dilate F y) := isCompact_iff_compactSpace.mp (isCompact_dilate F y)
  have hopen : IsOpen (((intLattice F).addSubgroupOf (dilate F y) : AddSubgroup (dilate F y)) : Set (dilate F y)) :=
    (isOpen_integralFiniteAdeles F).preimage continuous_subtype_val
  have := AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

-- pin: unif (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1477)
def unif (v : HOS) : F := Classical.choose (v.valuation_exists_uniformizer F)

-- pin: valuation_unif (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1479)
theorem valuation_unif (v : HOS) : v.valuation F (unif F v) = exp (-1 : ℤ) := Classical.choose_spec (v.valuation_exists_uniformizer F)

-- pin: valued_unif (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1481)
theorem valued_unif (v : HOS) : Valued.v ((unif F v : F) : v.adicCompletion F) = exp (-1 : ℤ) := by
  rw [valuedAdicCompletion_eq_valuation', valuation_unif]

-- pin: unif_coe_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1484)
theorem unif_coe_ne_zero (v : HOS) : ((unif F v : F) : v.adicCompletion F) ≠ 0 := fun h => by
  have := valued_unif F v; rw [h, map_zero] at this; exact exp_ne_zero this.symm

-- pin: unifFun (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1487)
def unifFun (k : HOS →₀ ℕ) (v : HOS) : v.adicCompletion F := ((unif F v : F) : v.adicCompletion F) ^ (-(k v : ℤ))

-- pin: valued_unifFun (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1489)
theorem valued_unifFun (k : HOS →₀ ℕ) (v : HOS) : Valued.v (unifFun F k v) = exp (k v : ℤ) := by
  rw [unifFun, map_zpow₀, valued_unif, ← exp_zsmul]; congr 1; ring

-- pin: unifFun_of_notMem (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1492)
theorem unifFun_of_notMem (k : HOS →₀ ℕ) {v : HOS} (hv : v ∉ k.support) : unifFun F k v = 1 := by
  rw [unifFun, Finsupp.notMem_support_iff.mp hv]; simp

-- pin: unifIdele (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1495)
def unifIdele (k : HOS →₀ ℕ) : (𝔸f)ˣ where
  val := RestrictedProduct.mk (unifFun F k) (Filter.eventually_cofinite.mpr
    ((k.support.finite_toSet).subset fun v hv => by
      by_contra h; exact hv (by rw [unifFun_of_notMem F k h]; exact one_mem _)))
  inv := RestrictedProduct.mk (fun v => (unifFun F k v)⁻¹) (Filter.eventually_cofinite.mpr
    ((k.support.finite_toSet).subset fun v hv => by
      by_contra h; exact hv (by rw [unifFun_of_notMem F k h, inv_one]; exact one_mem _)))
  val_inv := Subtype.ext (funext fun v => mul_inv_cancel₀ (zpow_ne_zero _ (unif_coe_ne_zero F v)))
  inv_val := Subtype.ext (funext fun v => inv_mul_cancel₀ (zpow_ne_zero _ (unif_coe_ne_zero F v)))

-- pin: unifIdele_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1505)
theorem unifIdele_apply (k : HOS →₀ ℕ) (v : HOS) : ((unifIdele F k : (𝔸f)ˣ) : 𝔸f) v = unifFun F k v := rfl

-- pin: valued_unifIdele (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1507)
theorem valued_unifIdele (k : HOS →₀ ℕ) (v : HOS) : Valued.v (((unifIdele F k : (𝔸f)ˣ) : 𝔸f) v) = exp (k v : ℤ) :=
  valued_unifFun F k v

-- pin: latt (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1510)
def latt (k : HOS →₀ ℕ) : AddSubgroup 𝔸f := dilate F (unifIdele F k)

-- pin: mem_latt_iff (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1512)
theorem mem_latt_iff (k : HOS →₀ ℕ) (t : 𝔸f) : t ∈ latt F k ↔ ∀ v, Valued.v (t v) ≤ exp (k v : ℤ) := by
  rw [latt, mem_dilate_iff]; simp only [valued_unifIdele]

-- pin: one_le_valued_unifIdele (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1515)
theorem one_le_valued_unifIdele (k : HOS →₀ ℕ) (v : HOS) : 1 ≤ Valued.v (((unifIdele F k : (𝔸f)ˣ) : 𝔸f) v) := by
  rw [valued_unifIdele, ← exp_zero, exp_le_exp]; exact_mod_cast Nat.zero_le _

-- pin: intLattice_le_latt (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1518)
theorem intLattice_le_latt (k : HOS →₀ ℕ) : intLattice F ≤ latt F k := intLattice_le_dilate F (one_le_valued_unifIdele F k)

-- pin: latt_mono (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1520)
theorem latt_mono {k k' : HOS →₀ ℕ} (h : k ≤ k') : latt F k ≤ latt F k' := fun t ht =>
  (mem_latt_iff F k' t).mpr fun v => ((mem_latt_iff F k t).mp ht v).trans (exp_le_exp.mpr (by exact_mod_cast h v))

-- pin: relIndex_latt_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1523)
theorem relIndex_latt_ne_zero (k : HOS →₀ ℕ) : (intLattice F).relIndex (latt F k) ≠ 0 := relIndex_dilate_ne_zero F _

-- pin: isCompact_latt (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1525)
theorem isCompact_latt (k : HOS →₀ ℕ) : IsCompact (latt F k : Set 𝔸f) := isCompact_dilate F _

-- pin: dilate_eq_latt (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1527)
theorem dilate_eq_latt (y : (𝔸f)ˣ) (hy : ∀ v, 1 ≤ Valued.v ((y : 𝔸f) v)) :
    ∃ k : HOS →₀ ℕ, dilate F y = latt F k ∧ ∀ v, exp (k v : ℤ) = Valued.v ((y : 𝔸f) v) := by

  have hfin : {v : HOS | Valued.v ((y : 𝔸f) v) ≠ 1}.Finite := by
    refine ((show RestrictedProduct (fun v : HOS => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite from (y : 𝔸f)).eventually).subset fun v hv => ?_
    intro hint
    exact hv (le_antisymm ((mem_adicCompletionIntegers _ _ _).mp hint) (hy v))
  let f : HOS → ℕ := fun v => (log (Valued.v ((y : 𝔸f) v))).toNat
  have hf : ∀ v, exp (f v : ℤ) = Valued.v ((y : 𝔸f) v) := fun v => by
    have hne := valued_ne_zero_of_unit F y v
    have hlog : 0 ≤ log (Valued.v ((y : 𝔸f) v)) := by rw [← exp_le_exp, exp_log hne, exp_zero]; exact hy v
    simp only [f, Int.toNat_of_nonneg hlog, exp_log hne]
  have hsupp : f.support ⊆ {v : HOS | Valued.v ((y : 𝔸f) v) ≠ 1} := fun v hv h1 => by
    apply hv
    show (log (Valued.v ((y : 𝔸f) v))).toNat = 0
    rw [h1, log_one, Int.toNat_zero]
  refine ⟨Finsupp.ofSupportFinite f (hfin.subset hsupp), ?_, fun v => ?_⟩
  · ext t
    rw [mem_dilate_iff, mem_latt_iff]
    simp only [Finsupp.ofSupportFinite_coe, hf]
  · rw [Finsupp.ofSupportFinite_coe]; exact hf v

end Lattices

end AutomorphicForm.WeylIntegrable

end

noncomputable section

open scoped Classical

namespace AutomorphicForm
namespace WeylIntegrable

section R2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

-- pin: singleFin (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1577)
def singleFin (v₀ : HOS) (t : v₀.adicCompletion F) : 𝔸f :=
  show RestrictedProduct (fun v : HOS => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite from
    RestrictedProduct.mk (Pi.single v₀ t) (Filter.eventually_cofinite.mpr ((Set.finite_singleton v₀).subset fun v hv => by
      by_contra h
      exact hv (by rw [Pi.single_eq_of_ne h]; exact zero_mem _)))

-- pin: singleFin_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1584)
theorem singleFin_apply (v₀ : HOS) (t : v₀.adicCompletion F) (v : HOS) : singleFin F v₀ t v = Pi.single v₀ t v := rfl

-- pin: singleFin_apply_same (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1586)
theorem singleFin_apply_same (v₀ : HOS) (t : v₀.adicCompletion F) : singleFin F v₀ t v₀ = t := by
  rw [singleFin_apply, Pi.single_eq_same]

-- pin: singleFin_apply_of_ne (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1589)
theorem singleFin_apply_of_ne (v₀ : HOS) (t : v₀.adicCompletion F) {v : HOS} (h : v ≠ v₀) : singleFin F v₀ t v = 0 := by
  rw [singleFin_apply, Pi.single_eq_of_ne h]

-- pin: singleFin_sub (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1592)
theorem singleFin_sub (v₀ : HOS) (t t' : v₀.adicCompletion F) : singleFin F v₀ t - singleFin F v₀ t' = singleFin F v₀ (t - t') :=
  Subtype.ext (funext fun v => by
    show singleFin F v₀ t v - singleFin F v₀ t' v = singleFin F v₀ (t - t') v
    simp only [singleFin_apply, Pi.single_sub, Pi.sub_apply])

-- pin: toCompl (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1597)
def toCompl (v₀ : HOS) : F →+* v₀.adicCompletion F :=
  ((adicCompletion.equiv F v₀).symm.toRingHom.comp
    (UniformSpace.Completion.coeRingHom :
      WithVal (v₀.valuation F) →+* (v₀.valuation F).Completion)).comp
    (WithVal.equiv (v₀.valuation F)).symm.toRingHom

-- pin: valued_toCompl (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1603)
theorem valued_toCompl (v₀ : HOS) (x : F) : Valued.v (toCompl F v₀ x) = v₀.valuation F x := valuedAdicCompletion_eq_valuation' v₀ x

-- pin: stepElt (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1605)
def stepElt (k : HOS →₀ ℕ) (v₀ : HOS) (r : 𝓞 F) : 𝔸f := singleFin F v₀ (toCompl F v₀ ((r : F) * unif F v₀ ^ (-((k v₀ : ℤ) + 1))))

-- pin: valued_toCompl_mul_unif_zpow (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1607)
theorem valued_toCompl_mul_unif_zpow (k : HOS →₀ ℕ) (v₀ : HOS) (x : F) :
    Valued.v (toCompl F v₀ (x * unif F v₀ ^ (-((k v₀ : ℤ) + 1)))) = v₀.valuation F x * exp ((k v₀ : ℤ) + 1) := by
  rw [valued_toCompl, map_mul, map_zpow₀, valuation_unif, ← exp_zsmul]
  congr 2; ring

-- pin: valued_stepElt_same (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1612)
theorem valued_stepElt_same (k : HOS →₀ ℕ) (v₀ : HOS) (r : 𝓞 F) :
    Valued.v (stepElt F k v₀ r v₀) = v₀.valuation F (r : F) * exp ((k v₀ : ℤ) + 1) := by
  rw [stepElt, singleFin_apply_same, valued_toCompl_mul_unif_zpow]

-- pin: stepElt_mem (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1616)
theorem stepElt_mem (k : HOS →₀ ℕ) (v₀ : HOS) (r : 𝓞 F) : stepElt F k v₀ r ∈ latt F (k + Finsupp.single v₀ 1) := by
  rw [mem_latt_iff]
  intro v
  by_cases hv : v = v₀
  · subst hv
    rw [valued_stepElt_same, Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    exact mul_le_of_le_one_left' (valuation_le_one v (r := r))
  · rw [stepElt, singleFin_apply_of_ne F _ _ hv, map_zero]; exact zero_le

-- pin: sub_mem_asIdeal_of_stepElt_sub_mem (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1626)
theorem sub_mem_asIdeal_of_stepElt_sub_mem (k : HOS →₀ ℕ) (v₀ : HOS) {r r' : 𝓞 F}
    (h : stepElt F k v₀ r - stepElt F k v₀ r' ∈ latt F k) : r - r' ∈ v₀.asIdeal := by
  rw [← valuation_lt_one_iff_mem (K := F), ← exp_zero]
  have hv := (mem_latt_iff F k _).mp h v₀
  rw [stepElt, stepElt, singleFin_sub, singleFin_apply_same, ← map_sub, ← sub_mul, valued_toCompl_mul_unif_zpow] at hv
  have hcast : ((r : F) - (r' : F)) = ((r - r' : 𝓞 F) : F) := by push_cast; ring
  rw [hcast] at hv

  by_contra hlt
  rw [not_lt] at hlt
  have : exp ((k v₀ : ℤ) + 1) ≤ exp (k v₀ : ℤ) :=
    le_trans (by simpa using mul_le_mul' hlt (le_refl (exp ((k v₀ : ℤ) + 1)))) hv
  rw [exp_le_exp] at this
  linarith

-- pin: relIndex_latt_latt_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1641)
theorem relIndex_latt_latt_ne_zero (k k' : HOS →₀ ℕ) : (latt F k).relIndex (latt F k') ≠ 0 := fun h0 =>
  relIndex_latt_ne_zero F k' (AddSubgroup.relIndex_eq_zero_of_le_left (intLattice_le_latt F k) h0)

-- pin: absNorm_le_relIndex_step (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1644)
theorem absNorm_le_relIndex_step (k : HOS →₀ ℕ) (v₀ : HOS) :
    Ideal.absNorm v₀.asIdeal ≤ (latt F k).relIndex (latt F (k + Finsupp.single v₀ 1)) := by
  set L := latt F k
  set L' := latt F (k + Finsupp.single v₀ 1)
  have hLL' : L ≤ L' := latt_mono F le_self_add
  have hidx : (L.addSubgroupOf L').index = L.relIndex L' := rfl
  have : Finite (L' ⧸ L.addSubgroupOf L') := by
    apply Nat.finite_of_card_ne_zero
    rw [← AddSubgroup.index_eq_card, hidx]
    exact relIndex_latt_latt_ne_zero F _ _

  let ψ : 𝓞 F ⧸ v₀.asIdeal → L' ⧸ L.addSubgroupOf L' := fun c =>
    QuotientAddGroup.mk ⟨stepElt F k v₀ c.out, stepElt_mem F k v₀ _⟩
  have hψ : Function.Injective ψ := by
    intro c c' hcc'
    have hmem : -(⟨stepElt F k v₀ c.out, stepElt_mem F k v₀ _⟩ : L') + ⟨stepElt F k v₀ c'.out, stepElt_mem F k v₀ _⟩ ∈ L.addSubgroupOf L' :=
      QuotientAddGroup.eq.mp hcc'
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    have hmem' : stepElt F k v₀ c'.out - stepElt F k v₀ c.out ∈ L := by
      simpa only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroupClass.coe_sub, neg_add_eq_sub]
        using hmem
    have := sub_mem_asIdeal_of_stepElt_sub_mem F k v₀ hmem'
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this
    rw [← Ideal.Quotient.mk_out c', ← Ideal.Quotient.mk_out c]
    exact this.symm
  calc Ideal.absNorm v₀.asIdeal = Nat.card (𝓞 F ⧸ v₀.asIdeal) := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ ≤ Nat.card (L' ⧸ L.addSubgroupOf L') := Nat.card_le_card_of_injective ψ hψ
    _ = L.relIndex L' := by rw [← AddSubgroup.index_eq_card, hidx]

-- pin: absNorm_pow_le_relIndex (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1673)
theorem absNorm_pow_le_relIndex (k : HOS →₀ ℕ) (v₀ : HOS) (n : ℕ) :
    Ideal.absNorm v₀.asIdeal ^ n ≤ (latt F k).relIndex (latt F (k + Finsupp.single v₀ n)) := by
  induction n with
  | zero => simp [AddSubgroup.relIndex_self]
  | succ n ih =>
    rw [pow_succ, Finsupp.single_add, ← add_assoc,
      ← AddSubgroup.relIndex_mul_relIndex (hHK := latt_mono F (le_self_add : k ≤ k + Finsupp.single v₀ n))
        (hKL := latt_mono F (le_self_add : k + Finsupp.single v₀ n ≤ k + Finsupp.single v₀ n + Finsupp.single v₀ 1))]
    exact Nat.mul_le_mul ih (absNorm_le_relIndex_step F _ v₀)

-- pin: normProd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1683)
def normProd (k : HOS →₀ ℕ) : ℕ := k.prod fun v n => Ideal.absNorm v.asIdeal ^ n

-- pin: normProd_single_add (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1685)
theorem normProd_single_add {a : HOS} {b : ℕ} {f : HOS →₀ ℕ} (ha : a ∉ f.support) (hb : b ≠ 0) :
    normProd F (Finsupp.single a b + f) = Ideal.absNorm a.asIdeal ^ b * normProd F f := by
  have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
    ext v
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_insert, Finsupp.single_apply]
    by_cases hv : a = v
    · subst hv; simp [hb]
    · simp [hv, Ne.symm hv]
  have hva : ∀ v ∈ f.support, (Finsupp.single a b + f) v = f v := fun v hv => by
    have : a ≠ v := fun h => ha (h ▸ hv)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne this.symm, zero_add]
  simp only [normProd, Finsupp.prod]
  rw [hsupp, Finset.prod_insert ha, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp ha, add_zero]
  congr 1
  exact Finset.prod_congr rfl fun v hv => by rw [hva v hv]

-- pin: one_le_normProd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1701)
theorem one_le_normProd (k : HOS →₀ ℕ) : 1 ≤ normProd F k := by
  rw [normProd, Finsupp.prod]
  exact Finset.one_le_prod fun v _ => Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot))

-- pin: normProd_le_relIndex (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1706)
theorem normProd_le_relIndex (k : HOS →₀ ℕ) : normProd F k ≤ (intLattice F).relIndex (latt F k) := by
  induction k using Finsupp.induction with
  | zero => exact Nat.one_le_iff_ne_zero.mpr (relIndex_latt_ne_zero F 0)
  | single_add a b f ha hb ih =>
    rw [normProd_single_add F ha hb, add_comm (Finsupp.single a b) f,
      ← AddSubgroup.relIndex_mul_relIndex (hHK := intLattice_le_latt F f) (hKL := latt_mono F (le_self_add : f ≤ f + Finsupp.single a b)),
      mul_comm]
    exact Nat.mul_le_mul ih (absNorm_pow_le_relIndex F f a b)

end R2

end AutomorphicForm.WeylIntegrable

end

noncomputable section

open scoped Classical ENNReal Topology nonZeroDivisors

namespace AutomorphicForm
namespace WeylIntegrable

section Fin

variable (F : Type) [Field F] [NumberField F]

local notation "HOS" => HeightOneSpectrum (𝓞 F)

-- pin: countable_ideal (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1741)
theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext I; simp
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable

-- pin: countable_heightOneSpectrum (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1747)
scoped instance countable_heightOneSpectrum : Countable HOS := by
  have := countable_ideal F
  exact Function.Injective.countable (f := fun v : HOS => v.asIdeal) fun v w h => HeightOneSpectrum.ext h

-- pin: countable_finsupp (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1751)
scoped instance countable_finsupp : Countable (HOS →₀ ℕ) := inferInstance

-- pin: idealOf (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1753)
def idealOf (k : HOS →₀ ℕ) : Ideal (𝓞 F) := k.prod fun v n => v.asIdeal ^ n

omit [NumberField F] in
-- pin: idealOf_ne_bot (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1756)
theorem idealOf_ne_bot (k : HOS →₀ ℕ) : idealOf F k ≠ ⊥ := by
  rw [idealOf, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot

-- pin: absNorm_idealOf (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1760)
theorem absNorm_idealOf (k : HOS →₀ ℕ) : Ideal.absNorm (idealOf F k) = normProd F k := by
  rw [idealOf, normProd, Finsupp.prod, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl fun v _ => map_pow _ _ _

-- pin: coe_idealOf (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1764)
theorem coe_idealOf (k : HOS →₀ ℕ) :
    (idealOf F k : FractionalIdeal (𝓞 F)⁰ F) =
      (k.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero).prod fun v (n : ℤ) => ((v.asIdeal : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ^ n := by
  rw [Finsupp.prod_mapRange_index (fun _ => zpow_zero _), idealOf, Finsupp.prod, Finsupp.prod,
    ← FractionalIdeal.coeIdealHom_apply, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow, zpow_natCast]

-- pin: idealOf_injective (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1772)
theorem idealOf_injective : Function.Injective (idealOf F) := by
  intro k k' h
  ext v
  have hc : FractionalIdeal.count F v (idealOf F k : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.count F v (idealOf F k' : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [h]
  rw [coe_idealOf, coe_idealOf, FractionalIdeal.count_finsuppProd, FractionalIdeal.count_finsuppProd, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hc
  exact_mod_cast hc

-- pin: idealCount (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1781)
def idealCount (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

-- pin: idealCount_nonneg (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1783)
theorem idealCount_nonneg (n : ℕ) : 0 ≤ idealCount F n := Nat.cast_nonneg _

-- pin: tendsto_sum_idealCount_div (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1785)
theorem tendsto_sum_idealCount_div :
    ∃ C : ℝ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, idealCount F k) / n) atTop (𝓝 C) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr fun n => ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, idealCount, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

-- pin: zetaTerm (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1797)
def zetaTerm (t : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else idealCount F n / (n : ℝ) ^ t

-- pin: zetaTerm_nonneg (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1799)
theorem zetaTerm_nonneg (t : ℝ) (n : ℕ) : 0 ≤ zetaTerm F t n := by
  unfold zetaTerm; split_ifs
  · exact le_rfl
  · exact div_nonneg (idealCount_nonneg F n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

-- pin: summable_zetaTerm (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1804)
theorem summable_zetaTerm {t : ℝ} (ht : 1 < t) : Summable (zetaTerm F t) := by
  obtain ⟨C, hC⟩ := tendsto_sum_idealCount_div F
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, idealCount F k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine isBigO_of_div_tendsto_nhds ?_ C ?_
    · refine Filter.eventually_atTop.mpr ⟨1, fun n hn h => ?_⟩
      exfalso
      rw [Real.rpow_one] at h
      exact (Nat.cast_ne_zero.mpr (by omega) : (n : ℝ) ≠ 0) h
    · refine hC.congr fun n => ?_
      simp only [Pi.div_apply, Real.rpow_one]
  have hL := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (t : ℂ)) hO (idealCount_nonneg F) zero_le_one
    (by simpa using ht)
  have hn := hL.norm
  refine hn.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  unfold zetaTerm
  split_ifs with h
  · rfl
  · rw [Complex.norm_of_nonneg (idealCount_nonneg F n), Complex.ofReal_re]

-- pin: tsum_fibre_card_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1824)
theorem tsum_fibre_card_mul (ψ : ℕ → ℝ≥0∞) :
    ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ψ (Ideal.absNorm I.1) =
      ∑' n : ℕ, (Nat.card {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} : ℝ≥0∞) * ψ n := by
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => Ideal.absNorm I.1), ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  have : Finite {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} :=
    Finite.of_injective (fun I => (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
      (fun I J h => Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => x.1) h)))
  have := Fintype.ofFinite {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n}
  have hconst : ∀ I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n},
      ψ (Ideal.absNorm ((Equiv.sigmaFiberEquiv fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => Ideal.absNorm I.1) ⟨n, I⟩).1) = ψ n :=
    fun I => by rw [Equiv.sigmaFiberEquiv_apply, I.2]
  rw [tsum_congr hconst, tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

-- pin: card_fibre_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1839)
theorem card_fibre_le (n : ℕ) :
    (Nat.card {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} : ℝ≥0∞) ≤ ENNReal.ofReal (idealCount F n) := by
  rw [idealCount, ENNReal.ofReal_natCast]
  have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  exact_mod_cast Nat.card_le_card_of_injective
    (fun I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} => (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
    (fun I J h => Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => x.1) h)))

-- pin: tsum_normProd_rpow_neg_lt_top (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1847)
theorem tsum_normProd_rpow_neg_lt_top {t : ℝ} (ht : 1 < t) : ∑' k : HOS →₀ ℕ, ((normProd F k : ℝ≥0∞) ^ (-t)) < ∞ := by
  have ht0 : 0 < t := zero_lt_one.trans ht

  let ι : (HOS →₀ ℕ) → {I : Ideal (𝓞 F) // I ≠ ⊥} := fun k => ⟨idealOf F k, idealOf_ne_bot F k⟩
  have hι : Function.Injective ι := fun k k' h => idealOf_injective F (congrArg Subtype.val h)
  let ψ : ℕ → ℝ≥0∞ := fun n => (n : ℝ≥0∞) ^ (-t)
  have h1 : ∑' k : HOS →₀ ℕ, ((normProd F k : ℝ≥0∞) ^ (-t)) = ∑' k, ψ (Ideal.absNorm (ι k).1) := by
    refine tsum_congr fun k => ?_; simp only [ψ, ι, absNorm_idealOf]
  have h2 : ∑' k, ψ (Ideal.absNorm (ι k).1) ≤ ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ψ (Ideal.absNorm I.1) :=
    ENNReal.tsum_comp_le_tsum_of_injective hι (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => ψ (Ideal.absNorm I.1))

  have h3 : ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ψ (Ideal.absNorm I.1) ≤ ∑' n, ENNReal.ofReal (zetaTerm F t n) := by
    rw [tsum_fibre_card_mul]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      have : Nat.card {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = 0} = 0 := by
        rw [Nat.card_eq_zero]; left
        exact ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
      rw [this, Nat.cast_zero, zero_mul]; exact bot_le
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hψ : ψ n = ENNReal.ofReal ((n : ℝ) ^ t)⁻¹ := by
        simp only [ψ]
        rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos hnpos, Real.rpow_neg hnpos.le, ]
      rw [hψ, zetaTerm, ite_eq_right (by omega), div_eq_mul_inv,
        ENNReal.ofReal_mul (idealCount_nonneg F n)]
      exact mul_le_mul' (card_fibre_le F n) le_rfl
  have h4 : ∑' n, ENNReal.ofReal (zetaTerm F t n) = ENNReal.ofReal (∑' n, zetaTerm F t n) :=
    (ENNReal.ofReal_tsum_of_nonneg (zetaTerm_nonneg F t) (summable_zetaTerm F ht)).symm
  calc ∑' k : HOS →₀ ℕ, ((normProd F k : ℝ≥0∞) ^ (-t)) ≤ ∑' n, ENNReal.ofReal (zetaTerm F t n) := h1.le.trans (h2.trans h3)
    _ < ∞ := by rw [h4]; exact ENNReal.ofReal_lt_top

-- pin: tsum_relIndex_rpow_lt_top (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1879)
theorem tsum_relIndex_rpow_lt_top {a : ℝ} (ha : 2 < a) :
    ∑' k : HOS →₀ ℕ, (((intLattice F).relIndex (latt F k) : ℝ≥0∞) ^ (1 - a)) < ∞ := by
  have ht : 1 < a - 1 := by linarith
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_) (tsum_normProd_rpow_neg_lt_top F ht)
  rw [show (1 - a) = -(a - 1) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (by exact_mod_cast normProd_le_relIndex F k) (by linarith))

end Fin

end AutomorphicForm.WeylIntegrable

end

noncomputable section

open scoped ENNReal NNReal

namespace AutomorphicForm
namespace WeylIntegrable

attribute [local instance] M4aS4.placeBorel M4aS4.infMS

section Place

variable {F : Type} [Field F] [NumberField F]

-- pin: placeWeight (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1912)
def placeWeight (w : InfinitePlace F) (r : ℝ) (y : w.Completion) : ℝ := (max 1 ‖y‖) ^ (-r)

omit [NumberField F] in
-- pin: placeWeight_nonneg (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1915)
theorem placeWeight_nonneg (w : InfinitePlace F) (r : ℝ) (y : w.Completion) : 0 ≤ placeWeight w r y :=
  Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _

omit [NumberField F] in
-- pin: placeWeight_le_one (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1919)
theorem placeWeight_le_one (w : InfinitePlace F) {r : ℝ} (hr : 0 ≤ r) (y : w.Completion) : placeWeight w r y ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (neg_nonpos.mpr hr)

omit [NumberField F] in
-- pin: continuous_placeWeight (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1923)
theorem continuous_placeWeight (w : InfinitePlace F) (r : ℝ) : Continuous (placeWeight w r) :=
  (continuous_const.max continuous_norm).rpow_const fun _ => Or.inl (zero_lt_one.trans_le (le_max_left _ _)).ne'

-- pin: integrable_max_one_norm_rpow_neg (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1926)
theorem integrable_max_one_norm_rpow_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ} (hr : (Module.finrank ℝ E : ℝ) < r) :
    Integrable (fun x : E => (max 1 ‖x‖) ^ (-r)) μ := by
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr.le
  have hmeas : Continuous fun x : E => (max 1 ‖x‖) ^ (-r) :=
    (continuous_const.max continuous_norm).rpow_const fun _ => Or.inl (zero_lt_one.trans_le (le_max_left _ _)).ne'
  refine ((integrable_one_add_norm hr).const_mul ((2 : ℝ) ^ r)).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hm : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
  have hm0 : (0 : ℝ) < max 1 ‖x‖ := zero_lt_one.trans_le hm
  have h1 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hm0.le _), Real.rpow_neg hm0.le, Real.rpow_neg h1.le, ← div_eq_mul_inv,
    le_div_iff₀ (Real.rpow_pos_of_pos h1 _), ← Real.inv_rpow hm0.le, ← Real.mul_rpow (inv_nonneg.mpr hm0.le) h1.le]
  calc ((max 1 ‖x‖)⁻¹ * (1 + ‖x‖)) ^ r ≤ (2 : ℝ) ^ r := by
        refine Real.rpow_le_rpow (by positivity) ?_ hr0
        rw [inv_mul_le_iff₀ hm0]
        calc 1 + ‖x‖ ≤ max 1 ‖x‖ + max 1 ‖x‖ := add_le_add hm (le_max_right _ _)
          _ = max 1 ‖x‖ * 2 := by ring
    _ = (2 : ℝ) ^ r := rfl

omit [NumberField F] in

-- pin: norm_ringEquivRealOfIsReal_symm (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1947)
theorem norm_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) :
    ‖(Completion.ringEquivRealOfIsReal hw).symm t‖ = ‖t‖ := by
  set e := Completion.ringEquivRealOfIsReal hw
  have hnorm : ∀ a : w.Completion, ‖e a‖ = ‖a‖ := fun a => by
    calc ‖e a‖ = dist (e a) (e 0) := by rw [map_zero, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  rw [← hnorm (e.symm t), RingEquiv.apply_symm_apply]

omit [NumberField F] in

-- pin: norm_ringEquivComplexOfIsComplex_symm (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1958)
theorem norm_ringEquivComplexOfIsComplex_symm {w : InfinitePlace F} (hw : w.IsComplex) (t : ℂ) :
    ‖(Completion.ringEquivComplexOfIsComplex hw).symm t‖ = ‖t‖ := by
  set e := Completion.ringEquivComplexOfIsComplex hw
  have hnorm : ∀ a : w.Completion, ‖e a‖ = ‖a‖ := fun a => by
    calc ‖e a‖ = dist (e a) (e 0) := by rw [map_zero, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbedding w).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  rw [← hnorm (e.symm t), RingEquiv.apply_symm_apply]

omit [NumberField F] in

-- pin: integrable_placeWeight (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1969)
theorem integrable_placeWeight (w : InfinitePlace F) {b : ℝ} (hb : 1 < b) : Integrable (placeWeight w (b * w.mult)) (placeMeasure F w) := by
  have hcont := continuous_placeWeight w (b * w.mult)
  unfold placeMeasure
  split_ifs with hw
  ·
    unfold placeMeasureReal
    have he : Measurable ⇑(Completion.ringEquivRealOfIsReal hw).symm := (Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable
    rw [integrable_map_measure hcont.aestronglyMeasurable he.aemeasurable]
    have hmult : (b * w.mult : ℝ) = b := by rw [InfinitePlace.mult, ite_eq_left hw]; push_cast; ring
    have : (placeWeight w (b * w.mult)) ∘ ⇑(Completion.ringEquivRealOfIsReal hw).symm = fun t : ℝ => (max 1 ‖t‖) ^ (-b) := by
      ext t; simp only [Function.comp_apply, placeWeight, norm_ringEquivRealOfIsReal_symm, hmult]
    rw [this]
    exact integrable_max_one_norm_rpow_neg volume (by rw [Module.finrank_self]; exact_mod_cast hb)
  ·
    unfold placeMeasureComplex
    have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have he : Measurable ⇑(Completion.ringEquivComplexOfIsComplex hw').symm :=
      (Completion.isometryEquivComplexOfIsComplex hw').symm.continuous.measurable
    rw [integrable_map_measure hcont.aestronglyMeasurable he.aemeasurable]
    have hmult : (b * w.mult : ℝ) = 2 * b := by rw [InfinitePlace.mult, ite_eq_right hw]; push_cast; ring
    have : (placeWeight w (b * w.mult)) ∘ ⇑(Completion.ringEquivComplexOfIsComplex hw').symm = fun t : ℂ => (max 1 ‖t‖) ^ (-(2 * b)) := by
      ext t; simp only [Function.comp_apply, placeWeight, norm_ringEquivComplexOfIsComplex_symm, hmult]
    rw [this]
    exact integrable_max_one_norm_rpow_neg volume (by rw [Complex.finrank_real_complex]; push_cast; linarith)

end Place

section Arch

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

-- pin: archWeight (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2007)
def archWeight (b : ℝ) (x : 𝔸∞) : ℝ := ∏ w : InfinitePlace F, placeWeight w (b * w.mult) (x w)

-- pin: archWeight_nonneg (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2009)
theorem archWeight_nonneg (b : ℝ) (x : 𝔸∞) : 0 ≤ archWeight F b x := Finset.prod_nonneg fun w _ => placeWeight_nonneg w _ _

-- pin: continuous_archWeight (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2011)
theorem continuous_archWeight (b : ℝ) : Continuous (archWeight F b) :=
  continuous_finsetProd _ fun w _ => (continuous_placeWeight w _).comp (continuous_apply w)

-- pin: measurable_archWeight (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2014)
theorem measurable_archWeight (b : ℝ) : Measurable (archWeight F b) := (continuous_archWeight F b).measurable

-- pin: integrable_archWeight (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2016)
theorem integrable_archWeight {b : ℝ} (hb : 1 < b) : Integrable (archWeight F b) (archMeasure F) := by
  unfold archMeasure archWeight
  exact Integrable.fintype_prod_dep fun w => integrable_placeWeight w hb

-- pin: archSlab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2020)
def archSlab : Set 𝔸 := slab F Set.univ (integralFiniteAdeles (𝓞 F) F)

-- pin: mem_archSlab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2022)
theorem mem_archSlab {u : 𝔸} : u ∈ archSlab F ↔ u.2 ∈ integralFiniteAdeles (𝓞 F) F := by
  simp [archSlab, mem_slab]

-- pin: isClosed_archSlab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2025)
theorem isClosed_archSlab : IsClosed (archSlab F) := isClosed_slab F isClosed_univ (isClosed_integralFiniteAdeles F)

-- pin: measurableSet_archSlab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2027)
theorem measurableSet_archSlab : MeasurableSet (archSlab F) := (isClosed_archSlab F).measurableSet

-- pin: continuous_adeleFst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2029)
theorem continuous_adeleFst : Continuous (fun u : 𝔸 => u.1 : 𝔸 → 𝔸∞) := continuous_fst

-- pin: measurable_adeleFst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2031)
theorem measurable_adeleFst : Measurable (fun u : 𝔸 => u.1 : 𝔸 → 𝔸∞) := (continuous_adeleFst F).measurable

-- pin: margMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2033)
def margMeasure : Measure 𝔸∞ := Measure.map (fun u : 𝔸 => u.1) ((adelicAddHaar (𝓞 F) F).restrict (archSlab F))

-- pin: margMeasure_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2035)
theorem margMeasure_apply {S : Set 𝔸∞} (hS : MeasurableSet S) : margMeasure F S = adelicAddHaar (𝓞 F) F (slab F S (integralFiniteAdeles (𝓞 F) F)) := by
  rw [margMeasure, Measure.map_apply (measurable_adeleFst F) hS, Measure.restrict_apply ((measurable_adeleFst F) hS)]
  congr 1
  ext u; simp [archSlab, mem_slab]

-- pin: isFiniteMeasureOnCompacts_margMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2040)
scoped instance isFiniteMeasureOnCompacts_margMeasure : IsFiniteMeasureOnCompacts (margMeasure F) := by
  have : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  refine ⟨fun K hK => ?_⟩
  rw [margMeasure_apply F hK.measurableSet]
  have hc : IsCompact (slab F K (integralFiniteAdeles (𝓞 F) F)) := by
    have : slab F K (integralFiniteAdeles (𝓞 F) F) = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) '' (K ×ˢ integralFiniteAdeles (𝓞 F) F) := by
      ext x; simp only [mem_slab]
      exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
    rw [this]
    exact (hK.prod (isCompact_integralFiniteAdeles F)).image continuous_id
  exact hc.measure_lt_top

-- pin: isAddLeftInvariant_margMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2052)
scoped instance isAddLeftInvariant_margMeasure : (margMeasure F).IsAddLeftInvariant := by
  have : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  refine ⟨fun t => ?_⟩
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply (measurable_const_add t) hS, margMeasure_apply F hS, margMeasure_apply F (measurable_const_add t hS)]

  have : slab F ((fun x => t + x) ⁻¹' S) (integralFiniteAdeles (𝓞 F) F) = (fun u : 𝔸 => toAdele F t 0 + u) ⁻¹' slab F S (integralFiniteAdeles (𝓞 F) F) := by
    ext u
    simp only [mem_slab, Set.mem_preimage]
    have h1 : (toAdele F t 0 + u).1 = t + u.1 := rfl
    have h2 : (toAdele F t 0 + u).2 = 0 + u.2 := rfl
    rw [h1, h2, zero_add]
  rw [this, measure_preimage_add]

-- pin: margMeasure_eq_smul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2066)
theorem margMeasure_eq_smul : margMeasure F = Measure.addHaarScalarFactor (margMeasure F) (infMeasure F) • infMeasure F :=
  Measure.isAddLeftInvariant_eq_smul (margMeasure F) (infMeasure F)

-- pin: hasFiniteIntegral_archWeight_infMeasure (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2069)
theorem hasFiniteIntegral_archWeight_infMeasure {b : ℝ} (hb : 1 < b) : HasFiniteIntegral (archWeight F b) (infMeasure F) :=
  (integrable_archWeight F hb).hasFiniteIntegral

-- pin: lintegral_archSlab_comp_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2072)
theorem lintegral_archSlab_comp_fst (h : 𝔸∞ → ℝ≥0∞) (hm : Measurable h) :
    ∫⁻ u in archSlab F, h u.1 ∂(adelicAddHaar (𝓞 F) F) = ∫⁻ x, h x ∂(margMeasure F) := by
  rw [margMeasure, lintegral_map hm (measurable_adeleFst F)]

-- pin: lintegral_archSlab_archWeight_lt_top (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2076)
theorem lintegral_archSlab_archWeight_lt_top {b : ℝ} (hb : 1 < b) :
    ∫⁻ u in archSlab F, ENNReal.ofReal (archWeight F b u.1) ∂(adelicAddHaar (𝓞 F) F) < ∞ := by
  rw [lintegral_archSlab_comp_fst F _ (measurable_archWeight F b).ennreal_ofReal, margMeasure_eq_smul, lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (archWeight_nonneg F b))).mp (hasFiniteIntegral_archWeight_infMeasure F hb)

end Arch

end AutomorphicForm.WeylIntegrable

end
