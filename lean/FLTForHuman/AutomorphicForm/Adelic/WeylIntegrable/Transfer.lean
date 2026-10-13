/-
  The Bruhat/transfer algebra: a `SelRel` idempotent `ε`, the elementary matrices `bMat`,
  `mMat`, `mInvMat`, and the passage from the generic comm-ring framing to the adèle ring.

  `SelRel ε y z x` records the relations (`ε² = ε`, `yz = 1`, `(1-ε)y = 1-ε`, `εy = εx`)
  satisfied by the idempotent attached to an adèlic point; `bFactor h` is the Borel
  matrix it produces and `mFactor` the complementary `M`-factor. The adèlic sections
  build `selE`/`selY`/`selZ` from the big archimedean/finite places so that `selRel`
  holds, and compute the Weyl–unipotent decomposition `w⁻¹ n(u) = bFactor · mFactor`
  used in the Bruhat-transversal estimates.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 871–1107 (pinned `aa2d8b3`), sections `Generic`, `Adelic`, `Generic2`, `Adelic2`
  of the pin namespace `AutomorphicForm.WeylIntegrable`.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Coset
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain Matrix
open IsDedekindDomain.HeightOneSpectrum
open scoped Classical

noncomputable section

namespace AutomorphicForm

namespace WeylIntegrable

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}

-- pin: SelRel (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:875)
structure SelRel (ε y z x : A) : Prop where
  idem : ε * ε = ε
  yz : y * z = 1
  small : (1 - ε) * y = 1 - ε
  big : ε * y = ε * x

-- pin: bMat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:881)
def bMat (ε y z : A) : Matrix (Fin 2) (Fin 2) A := !![1 - ε - ε * z, ε; 0, y]

-- pin: mMat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:883)
def mMat (ε z x : A) : Matrix (Fin 2) (Fin 2) A := !![ε, 1 - ε; 1 - ε + ε * z, (1 - ε) * x + ε]

-- pin: mInvMat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:885)
def mInvMat (ε z x : A) : Matrix (Fin 2) (Fin 2) A :=
  !![(2 * ε - 1) * ((1 - ε) * x + ε), -((2 * ε - 1) * (1 - ε)); -((2 * ε - 1) * (1 - ε + ε * z)), (2 * ε - 1) * ε]

-- pin: det_bMat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:888)
theorem det_bMat (h : SelRel ε y z x) : (bMat ε y z).det = 1 - 2 * ε := by
  rw [bMat, Matrix.det_fin_two_of]
  linear_combination h.small - ε * h.yz

-- pin: one_sub_two_mul_sq (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:892)
theorem one_sub_two_mul_sq (h : SelRel ε y z x) : (1 - 2 * ε) * (1 - 2 * ε) = 1 := by
  linear_combination 4 * h.idem

-- pin: isUnit_det_bMat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:895)
theorem isUnit_det_bMat (h : SelRel ε y z x) : IsUnit (bMat ε y z).det := by
  rw [det_bMat h]; exact (Units.mkOfMulEqOne _ _ (one_sub_two_mul_sq h)).isUnit

-- pin: bFactor (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:898)
def bFactor (h : SelRel ε y z x) : GL (Fin 2) A := Matrix.nonsingInvUnit (bMat ε y z) (isUnit_det_bMat h)

-- pin: coe_bFactor (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:900)
@[scoped simp] theorem coe_bFactor (h : SelRel ε y z x) : (bFactor h : Matrix (Fin 2) (Fin 2) A) = bMat ε y z := rfl

-- pin: bFactor_mem_borel (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:902)
theorem bFactor_mem_borel (h : SelRel ε y z x) : bFactor h ∈ borelSubgroup A := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  simp [bMat]

-- pin: borelDiagFst_bFactor_val (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:906)
theorem borelDiagFst_bFactor_val (h : SelRel ε y z x) :
    ((borelDiagFst ⟨bFactor h, bFactor_mem_borel h⟩ : Aˣ) : A) = 1 - ε - ε * z := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 0 0 = _
  simp [bMat]

-- pin: borelDiagSnd_bFactor_val (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:911)
theorem borelDiagSnd_bFactor_val (h : SelRel ε y z x) :
    ((borelDiagSnd ⟨bFactor h, bFactor_mem_borel h⟩ : Aˣ) : A) = y := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 1 1 = _
  simp [bMat]

-- pin: bMat_mul_mMat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:916)
theorem bMat_mul_mMat (h : SelRel ε y z x) : bMat ε y z * mMat ε z x = !![0, 1; 1, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bMat, mMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-2) * h.idem
  · linear_combination (2 + z - x) * h.idem
  · linear_combination h.small + ε * h.yz
  · linear_combination x * h.small + h.big

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

-- pin: toAdele' (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:936)
def toAdele' (a : 𝔸∞) (b : 𝔸f) : 𝔸 := (a, b)

-- pin: finOfIntegral (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:938)
def finOfIntegral (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : 𝔸f :=
  show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk f (.of_forall hf)

-- pin: finOfIntegral_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:944)
@[scoped simp] theorem finOfIntegral_apply (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : finOfIntegral F f hf v = f v := rfl

-- pin: BigInf (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:947)
def BigInf (a : 𝔸∞) (w : InfinitePlace F) : Prop := 1 < ‖a w‖

-- pin: BigFin (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:949)
def BigFin (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : Prop := b v ∉ v.adicCompletionIntegers F

omit [NumberField F] in
-- pin: ne_zero_of_bigInf (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:952)
theorem ne_zero_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : a w ≠ 0 := by
  intro h0; rw [BigInf, h0, norm_zero] at h; exact (not_lt.mpr zero_le_one) h

omit [NumberField F] in
-- pin: norm_inv_lt_one_of_bigInf (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:956)
theorem norm_inv_lt_one_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : ‖(a w)⁻¹‖ < 1 := by
  rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h

-- pin: one_lt_valued_of_bigFin (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:959)
theorem one_lt_valued_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : 1 < Valued.v (b v) := by
  rw [BigFin, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h; exact h

-- pin: ne_zero_of_bigFin (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:962)
theorem ne_zero_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : b v ≠ 0 := by
  intro h0; have := one_lt_valued_of_bigFin F h; rw [h0, map_zero] at this; exact (not_lt.mpr zero_le_one) this

-- pin: inv_mem_of_bigFin (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:965)
theorem inv_mem_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : (b v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ((Valuation.one_lt_val_iff _ (ne_zero_of_bigFin F h)).mp (one_lt_valued_of_bigFin F h)).le

-- pin: selE (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:969)
def selE (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then 1 else 0)
  (finOfIntegral F (fun v => if BigFin F b v then 1 else 0) fun v => by split_ifs <;> simp [one_mem, zero_mem])

-- pin: selZ (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:972)
def selZ (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then (a w)⁻¹ else 1)
  (finOfIntegral F (fun v => if BigFin F b v then (b v)⁻¹ else 1) fun v => by
    split_ifs with h
    · exact inv_mem_of_bigFin F h
    · exact one_mem _)

end Adelic

section Generic2

variable {A : Type*} [CommRing A] {ε y z x : A}

-- pin: yUnit (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:985)
def yUnit (h : SelRel ε y z x) : Aˣ :=
  ⟨y, ε * z + (1 - ε), by linear_combination ε * h.yz + h.small, by linear_combination ε * h.yz + h.small⟩

-- pin: coe_yUnit (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:988)
@[scoped simp] theorem coe_yUnit (h : SelRel ε y z x) : (yUnit h : A) = y := rfl
-- pin: coe_yUnit_inv (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:989)
theorem coe_yUnit_inv (h : SelRel ε y z x) : (((yUnit h)⁻¹ : Aˣ) : A) = ε * z + (1 - ε) := rfl

-- pin: eUnit (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:991)
def eUnit (h : SelRel ε y z x) : Aˣ := ⟨1 - 2 * ε, 1 - 2 * ε, one_sub_two_mul_sq h, one_sub_two_mul_sq h⟩

-- pin: coe_eUnit (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:993)
@[scoped simp] theorem coe_eUnit (h : SelRel ε y z x) : (eUnit h : A) = 1 - 2 * ε := rfl

-- pin: eUnit_mul_self (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:995)
theorem eUnit_mul_self (h : SelRel ε y z x) : eUnit h * eUnit h = 1 := Units.ext (one_sub_two_mul_sq h)

-- pin: borelDiagFst_bFactor (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:997)
theorem borelDiagFst_bFactor (h : SelRel ε y z x) : borelDiagFst ⟨bFactor h, bFactor_mem_borel h⟩ = eUnit h * (yUnit h)⁻¹ := by
  apply Units.ext
  rw [borelDiagFst_bFactor_val, Units.val_mul, coe_eUnit, coe_yUnit_inv]
  linear_combination (2 * z - 2) * h.idem

-- pin: borelDiagSnd_bFactor (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1002)
theorem borelDiagSnd_bFactor (h : SelRel ε y z x) : borelDiagSnd ⟨bFactor h, bFactor_mem_borel h⟩ = yUnit h :=
  Units.ext (borelDiagSnd_bFactor_val h)

-- pin: mMat_mul_mInvMat (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1005)
theorem mMat_mul_mInvMat (h : SelRel ε y z x) : mMat ε z x * mInvMat ε z x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mMat, mInvMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (4 - (2 * ε - 1) * x + (2 * ε - 1) * z) * h.idem
  · ring
  · ring
  · linear_combination (4 + (2 * ε - 1) * z - (2 * ε - 1) * x) * h.idem

end Generic2

section Adelic2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

-- pin: selY (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1025)
def selY (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then a w else 1)
  (show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk (fun v => if BigFin F b v then b v else 1)
      ((show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from b).eventually.mono
        fun v hv => by
          rw [ite_eq_right (show ¬ BigFin F b v from not_not.mpr hv)]
          exact one_mem _))

-- pin: selE_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1035)
theorem selE_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selE F a b).1 w = if BigInf F a w then 1 else 0 := rfl
-- pin: selE_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1036)
theorem selE_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v = if BigFin F b v then 1 else 0 := rfl
-- pin: selY_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1037)
theorem selY_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selY F a b).1 w = if BigInf F a w then a w else 1 := rfl
-- pin: selY_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1038)
theorem selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selY F a b).2 v = if BigFin F b v then b v else 1 := rfl
-- pin: selZ_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1039)
theorem selZ_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selZ F a b).1 w = if BigInf F a w then (a w)⁻¹ else 1 := rfl
-- pin: selZ_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1040)
theorem selZ_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v = if BigFin F b v then (b v)⁻¹ else 1 := rfl
-- pin: toAdele'_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1041)
theorem toAdele'_fst (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).1 = a := rfl
-- pin: toAdele'_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1042)
theorem toAdele'_snd (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).2 = b := rfl

-- pin: mul_fst_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1044)
theorem mul_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u * u').1 w = u.1 w * u'.1 w := rfl
-- pin: mul_snd_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1045)
theorem mul_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u * u').2 v = u.2 v * u'.2 v := rfl
-- pin: sub_fst_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1046)
theorem sub_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u - u').1 w = u.1 w - u'.1 w := rfl
-- pin: sub_snd_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1047)
theorem sub_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u - u').2 v = u.2 v - u'.2 v := rfl
-- pin: one_fst_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1048)
theorem one_fst_apply (w : InfinitePlace F) : (1 : 𝔸).1 w = 1 := rfl
-- pin: one_snd_apply (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1049)
theorem one_snd_apply (v : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸).2 v = 1 := rfl

-- pin: adele_ext (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1051)
theorem adele_ext {u u' : 𝔸} (h1 : ∀ w, u.1 w = u'.1 w) (h2 : ∀ v, u.2 v = u'.2 v) : u = u' :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

-- pin: selRel (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1054)
theorem selRel (a : 𝔸∞) (b : 𝔸f) : SelRel (selE F a b) (selY F a b) (selZ F a b) (toAdele' F a b) where
  idem := adele_ext F (fun w => by rw [mul_fst_apply, selE_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, selE_snd]; split_ifs <;> simp)
  yz := adele_ext F
    (fun w => by
      rw [mul_fst_apply, selY_fst, selZ_fst, one_fst_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigInf F h)
      · exact mul_one 1)
    (fun v => by
      rw [mul_snd_apply, selY_snd, selZ_snd, one_snd_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigFin F h)
      · exact mul_one 1)
  small := adele_ext F
    (fun w => by rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, selY_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, selY_snd]; split_ifs <;> simp)
  big := adele_ext F
    (fun w => by rw [mul_fst_apply, mul_fst_apply, selE_fst, selY_fst, toAdele'_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, mul_snd_apply, selE_snd, selY_snd, toAdele'_snd]; split_ifs <;> simp)

-- pin: adelicWeyl_inv' (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1075)
theorem adelicWeyl_inv' : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

-- pin: coe_adelicWeyl_mul_unipotent (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1078)
theorem coe_adelicWeyl_mul_unipotent (u : 𝔸) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, u] := by
  rw [adelicWeyl_inv', Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  have hw : ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, 0] := by
    ext i j
    rw [adelicWeyl, globalPoints_apply]
    fin_cases i <;> fin_cases j <;> simp [gl2Weyl]
  rw [hw]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

-- pin: mFactor (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1089)
def mFactor (a : 𝔸∞) (b : 𝔸f) : AdelicGL2 (𝓞 F) F :=
  (bFactor (selRel F a b))⁻¹ * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (toAdele' F a b))

-- pin: weyl_unipotent_eq (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1092)
theorem weyl_unipotent_eq (u : 𝔸) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u = bFactor (selRel F u.1 u.2) * mFactor F u.1 u.2 := by
  rw [mFactor, mul_inv_cancel_left]; rfl

-- pin: coe_mFactor (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1096)
theorem coe_mFactor (a : 𝔸∞) (b : 𝔸f) : ((mFactor F a b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) =
    mMat (selE F a b) (selZ F a b) (toAdele' F a b) := by
  rw [mFactor, Matrix.GeneralLinearGroup.coe_mul, coe_adelicWeyl_mul_unipotent, ← bMat_mul_mMat (selRel F a b),
    ← Matrix.mul_assoc, Matrix.GeneralLinearGroup.coe_inv, coe_bFactor, Matrix.nonsing_inv_mul _ (isUnit_det_bMat (selRel F a b)),
    Matrix.one_mul]

-- pin: coe_mFactor_inv (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:1102)
theorem coe_mFactor_inv (a : 𝔸∞) (b : 𝔸f) : (((mFactor F a b)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) =
    mInvMat (selE F a b) (selZ F a b) (toAdele' F a b) := by
  rw [Matrix.GeneralLinearGroup.coe_inv, coe_mFactor]
  exact Matrix.inv_eq_right_inv (mMat_mul_mInvMat (selRel F a b))

end Adelic2

end WeylIntegrable

end AutomorphicForm

end
