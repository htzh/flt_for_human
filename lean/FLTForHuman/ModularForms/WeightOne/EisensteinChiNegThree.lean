/-
  The `χ₋₃` weight-one Eisenstein series is modular (SET-6 order 2).

  Five headlines are public — `EisensteinWeightOne.e1Chi3IsModular`,
  `EisensteinWeightOne.chiNegThree_mul`, `EisensteinWeightOne.coeff_e1Chi3`,
  `EisensteinWeightOne.tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal` and
  `ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul` — each stated verbatim
  from its pinned `Theorems/` wrapper. The proof is ported from
  `P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean` (3,816 lines), adapted from mathlib `v4.33.0`
  to `v4.34.0`. The vocabulary (`chiNegThree`, `sigmaChi`, `e1Chi3`, `E1Chi3IsModular`) is imported
  from `Defs/EisensteinChiNegThree.lean`, not redefined.

  **Two blocks that this module used to carry `private` have moved to their own homes** (2026-10-20,
  homing standard `topics/TOPIC-mathlib-module-homing.md` §3). The pin's `S_` file for this module is
  a *composite*: its `section File_FLT_*` markers are the pin's own module boundaries, and two of the
  blocks concatenated into it are other modules' developments, not helpers of this headline.

  * `FLT.AnalyticCore.Gamma0Three` (forty declarations, `File_FLT_AnalyticCore_TwoGeneratorSweep`) →
    `FLTForHuman/NumberTheory/ModularForms/Gamma0Three.lean`, public, with the frontier headline
    `CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three`. The pin writes that development into
    five `S_` files.
  * `ModularCurve.Numerics` (twenty-two declarations, `File_FLT_ModularCurve_Numerics_NuThree`) →
    `FLTForHuman/ModularCurve/Numerics/NuThree.lean`, public, with the two frontier headlines
    `ModularCurve.nuThree_prime` and `ModularCurve.nuThree_mul_of_coprime` — both of which were
    *counted as ported* while sitting here `private`.

  **A third block is imported rather than transplanted.** The `A₂` theta development of
  `File_FLT_AnalyticCore_RankTwoPoissonSummation` (thirty-two declarations: `hexTheta`,
  the Poisson summation `inner_poisson`/`outer_poisson`/`summable_middle`, the `cpow`
  half-power helpers and `hexTheta_fricke`) already had a home: the port's
  `Analysis/Theta/HexagonalLattice.lean`, transcribed from
  `S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean`. The copy here was
  proof-identical modulo `private`, so it is deleted (365 lines) and the module is imported
  and its namespace opened. `HexagonalLattice` is itself a node of the D-S cone, so this is
  the one import that both removes a duplicate and gives that module its consumer.

  Both are imported below and their scopes opened. Helpers stay `private` unless one of the other
  homed blocks or `Reserve/ModularForms/WeightOne/ChiNegThreeDead.lean` needs them across a module
  boundary; the ones that had to be exposed are pin declarations, so `check_port.py` now verifies
  seventy statements of this module instead of five. **Everything unreachable from the five headlines
  has left**: the dead set (95 declarations, 944 lines, including all the pin's sharpness witnesses and
  superseded routes) is on the shelf `Reserve/ModularForms/WeightOne/ChiNegThreeDead.lean`, moved by
  `tools/deps/move_dead.py`. What remains here is the live core. The headlines checked here are the ones listed in
  `spec-pin:` below — the four `Theorems/` wrappers, and the three `S_` files the text was transcribed
  from (their statements spell the coefficients differently from the wrappers, so both are needed for
  the checker). The last two wrappers name no `S_` file: their statements are stated verbatim from
  their wrappers and their proofs are derived here from this module's own material, not transcribed.
  `ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul` is the residual of
  `S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean` — that `S_` file is an
  earlier generation of the same theta/lattice-sum modules transcribed here (107 of its 112
  statements are identical to this module's), so only its `thetaForm` packaging is new.

  spec-pin: Theorems/Thm_EisensteinWeightOne_e1Chi3IsModular.lean
  spec-pin: Theorems/Thm_EisensteinWeightOne_chiNegThree_mul.lean
  spec-pin: Theorems/Thm_EisensteinWeightOne_coeff_e1Chi3.lean
  spec-pin: Theorems/Thm_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.lean
  spec-pin: Theorems/Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean
  spec-pin: P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean
  spec-pin: P2M/Sol/S_EisensteinWeightOne_chiNegThree_mul.lean
  spec-pin: P2M/Sol/S_EisensteinWeightOne_coeff_e1Chi3.lean

  The development has two halves:

  * the analytic half (`FLT.EisensteinWeightOne` and
    `FLT.AnalyticCore`): the hexagonal theta series
    `hexTheta σ = ∑'_{x,y} e^{2πiσ(x²+xy+y²)}` and its Poisson-summation
    functional equation (**imported**, see above), its values at the fixed points of
    `T` and `U₃` (`hexThetaH` and the slash laws), and the resulting weight-one
    modularity on `Γ₀(3)`;
  * the arithmetic half: the representation count `reprCount n` of `n` by
    `x² + xy + y²`, the ring of integers `HexInt = ℤ[ζ₃]` as a Euclidean
    domain, the splitting law for primes `p ≡ 1 (mod 3)`, and the identification
    `reprCount n = coeff n e1Chi3`.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_e1Chi3IsModular.lean

  v4.34 drifts hit here: `if_neg` → `ite_eq_right`, `if_pos` → `ite_eq_left`,
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, and scoped `simp`/`ext` attributes
  made plain (single-file port). The pin's local `set_option maxRecDepth 16384`
  on `reprCount_twentyone` is **not** transcribed.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import FLTForHuman.ModularForms.Defs.EisensteinChiNegThree
import FLTForHuman.ModularCurve.Numerics.NuThree
import FLTForHuman.NumberTheory.ModularForms.Gamma0Three
import FLTForHuman.Analysis.Theta.HexagonalLattice

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open EisensteinWeightOne

-- The `A₂` theta development is `Analysis/Theta/HexagonalLattice.lean` (public, and a D-S cone
-- node); this file used to carry a private transplant of it. Opened for the proofs that name
-- `hexTheta`, `hexThetaTerm`, `inner_poisson`, `hexTheta_fricke` and the `cpow` helpers.
open A2HexPoisson

-- The Γ₀(3) generation engine is `CongruenceSubgroup.Gamma0Three` (its own module); this
-- file used to carry a private transplant of it. Opened here for the proofs that name
-- `U₃`, `gens`, `apply_one_one_ne_zero` and the qualified `Gamma0Three.repOfLabel`.
open CongruenceSubgroup.Gamma0Three
open scoped CongruenceSubgroup.Gamma0Three

section File_FLT_Modularity_EisensteinWeightOne

namespace FLT
namespace EisensteinWeightOne

open Finset Nat Finset.Nat ArithmeticFunction CongruenceSubgroup
open scoped Finset Nat Finset.Nat ArithmeticFunction CongruenceSubgroup

@[simp] private theorem chiNegThree_zero : chiNegThree 0 = 0 := rfl

@[simp] theorem chiNegThree_one : chiNegThree 1 = 1 := rfl

@[simp] private theorem chiNegThree_two : chiNegThree 2 = -1 := rfl

@[simp] theorem chiNegThree_three : chiNegThree 3 = 0 := rfl

private theorem chiNegThree_mod (n : ℕ) : chiNegThree (n % 3) = chiNegThree n := by
  simp only [chiNegThree, Nat.mod_mod_of_dvd n (dvd_refl 3)]

theorem chiNegThree_mul (m n : ℕ) : chiNegThree (m * n) = chiNegThree m * chiNegThree n := by
  simp only [chiNegThree]
  rw [Nat.mul_mod]
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with h | h | h <;> rcases hn with h' | h' | h' <;> rw [h, h'] <;> decide

private theorem chiNegThree_pow (p j : ℕ) : chiNegThree (p ^ j) = chiNegThree p ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, chiNegThree_mul, ih, pow_succ]

@[simp] private theorem sigmaChi_zero : sigmaChi 0 = 0 := by simp [sigmaChi]

def chiNegThreeArith : ArithmeticFunction ℤ :=
  ⟨chiNegThree, chiNegThree_zero⟩

@[simp] private theorem chiNegThreeArith_apply {n : ℕ} : chiNegThreeArith n = chiNegThree n := rfl

def zetaInt : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else 1, rfl⟩

@[simp] private theorem zetaInt_apply {n : ℕ} : zetaInt n = if n = 0 then 0 else 1 := rfl

private theorem isMultiplicative_chiNegThreeArith : chiNegThreeArith.IsMultiplicative :=
  ⟨chiNegThree_one, fun {m n} _ => chiNegThree_mul m n⟩

private theorem isMultiplicative_zetaInt : zetaInt.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hm, hn, Nat.mul_ne_zero hm hn]

private theorem sigmaChi_eq_mul_apply (n : ℕ) : sigmaChi n = (zetaInt * chiNegThreeArith) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  unfold sigmaChi
  calc ∑ d ∈ n.divisors, chiNegThree d
      = ∑ d ∈ n.divisors, chiNegThree (n / d) := (Nat.sum_div_divisors n chiNegThree).symm
    _ = ∑ d ∈ n.divisors, zetaInt d * chiNegThreeArith (n / d) :=
        Finset.sum_congr rfl fun d hd => by
          have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
          simp [hd0]
    _ = ∑ x ∈ n.divisorsAntidiagonal, zetaInt x.1 * chiNegThreeArith x.2 :=
        (Nat.sum_divisorsAntidiagonal fun d e => zetaInt d * chiNegThreeArith e).symm
    _ = (zetaInt * chiNegThreeArith) n := ArithmeticFunction.mul_apply.symm

private theorem isMultiplicative_zetaInt_mul_chi :
    (zetaInt * chiNegThreeArith).IsMultiplicative :=
  isMultiplicative_zetaInt.mul isMultiplicative_chiNegThreeArith

theorem sigmaChi_mul_of_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    sigmaChi (m * n) = sigmaChi m * sigmaChi n := by
  simp only [sigmaChi_eq_mul_apply]
  exact isMultiplicative_zetaInt_mul_chi.map_mul_of_coprime h

theorem sigmaChi_one : sigmaChi 1 = 1 := by decide

theorem coeff_e1Chi3 (n : ℕ) :
    PowerSeries.coeff n e1Chi3 = if n = 0 then 1 else 6 * sigmaChi n := by
  rw [e1Chi3, PowerSeries.coeff_mk]

@[simp] private theorem constantCoeff_e1Chi3 : PowerSeries.constantCoeff e1Chi3 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_e1Chi3]
  simp

theorem coeff_e1Chi3_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n e1Chi3 = 6 * sigmaChi n := by
  rw [coeff_e1Chi3, ite_eq_right hn]

theorem coeff_one_e1Chi3 : PowerSeries.coeff 1 e1Chi3 = 6 := by
  rw [coeff_e1Chi3]
  norm_num [sigmaChi_one]

end FLT.EisensteinWeightOne

end File_FLT_Modularity_EisensteinWeightOne

section File_FLT_AnalyticCore_LatticeSumPlumbing

open Complex Real Set

namespace FLT
namespace AnalyticCore
namespace LatticeSum

def hexForm (v : ℤ × ℤ) : ℤ :=
  v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2

@[simp] lemma hexForm_mk (m n : ℤ) : hexForm (m, n) = m ^ 2 + m * n + n ^ 2 := rfl

lemma hexForm_nonneg (v : ℤ × ℤ) : 0 ≤ hexForm v := by
  obtain ⟨a, b⟩ := v
  simp only [hexForm_mk]
  nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]

private lemma hexForm_eq_zero_iff (v : ℤ × ℤ) : hexForm v = 0 ↔ v = (0, 0) := by
  obtain ⟨a, b⟩ := v
  simp only [hexForm_mk, Prod.mk.injEq]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
  · rintro ⟨rfl, rfl⟩; ring

lemma sq_add_sq_le_two_mul_hexForm (v : ℤ × ℤ) :
    v.1 ^ 2 + v.2 ^ 2 ≤ 2 * hexForm v := by
  obtain ⟨a, b⟩ := v
  simp only [hexForm_mk]
  nlinarith [sq_nonneg (a + b)]

def hexFormNat (v : ℤ × ℤ) : ℕ :=
  (hexForm v).toNat

@[simp] private lemma coe_hexFormNat (v : ℤ × ℤ) : (hexFormNat v : ℤ) = hexForm v :=
  Int.toNat_of_nonneg (hexForm_nonneg v)

lemma hexFormNat_eq_iff (v : ℤ × ℤ) (n : ℕ) : hexFormNat v = n ↔ hexForm v = (n : ℤ) := by
  rw [← coe_hexFormNat, Int.natCast_inj]

@[simp] private lemma hexFormNat_zero : hexFormNat (0, 0) = 0 := by
  rw [hexFormNat_eq_iff]; rfl

noncomputable def latticeTerm (τ : ℂ) (v : ℤ × ℤ) : ℂ :=
  Complex.exp (2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * τ)

private lemma norm_latticeTerm (τ : ℂ) (v : ℤ × ℤ) :
    ‖latticeTerm τ v‖ = Real.exp (-(2 * π * (hexFormNat v : ℝ) * τ.im)) := by
  rw [latticeTerm, show (2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * τ)
      = ((2 * π * (hexFormNat v : ℝ) : ℝ) : ℂ) * τ * Complex.I by push_cast; ring]
  rw [Complex.norm_exp, mul_I_re, im_ofReal_mul]

lemma norm_latticeTerm_le_of_le_im {T : ℝ} (hT : 0 < T) {τ : ℂ} (hτ : T ≤ τ.im) (v : ℤ × ℤ) :
    ‖latticeTerm τ v‖ ≤
      Real.exp (-(π * T * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * T * (v.2 : ℝ) ^ 2)) := by
  rw [norm_latticeTerm, ← Real.exp_add, Real.exp_le_exp]
  have hQ : (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 ≤ 2 * (hexFormNat v : ℝ) := by
    have := sq_add_sq_le_two_mul_hexForm v
    have h2 : ((2 * hexForm v : ℤ) : ℝ) = 2 * (hexFormNat v : ℝ) := by
      push_cast [coe_hexFormNat]; ring_nf
      norm_cast
      simp [coe_hexFormNat]
    calc (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 = ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * hexForm v : ℤ) : ℝ) := by exact_mod_cast this
      _ = 2 * (hexFormNat v : ℝ) := h2
  have hQ0 : (0 : ℝ) ≤ (hexFormNat v : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ π * T),
    mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 2 * π * (hexFormNat v : ℝ))]

private lemma summable_gaussian_int {t : ℝ} (ht : 0 < t) :
    Summable fun m : ℤ ↦ Real.exp (-(π * t * (m : ℝ) ^ 2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 ht 0
  simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero, neg_mul, mul_assoc] using h

lemma summable_gaussian_prod {t : ℝ} (ht : 0 < t) :
    Summable fun v : ℤ × ℤ ↦
      Real.exp (-(π * t * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * t * (v.2 : ℝ) ^ 2)) :=
  (summable_gaussian_int ht).mul_of_nonneg (summable_gaussian_int ht)
    (fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ (Real.exp_pos _).le)

private theorem summable_latticeTerm {τ : ℂ} (hτ : 0 < τ.im) : Summable (latticeTerm τ) :=
  (summable_gaussian_prod hτ).of_norm_bounded (norm_latticeTerm_le_of_le_im hτ le_rfl)

noncomputable def latticeSum (τ : ℂ) : ℂ :=
  ∑' v : ℤ × ℤ, latticeTerm τ v

noncomputable def repCount (n : ℕ) : ℕ :=
  (hexFormNat ⁻¹' {n}).ncard

@[simp] theorem repCount_zero : repCount 0 = 1 := by
  have h : hexFormNat ⁻¹' {0} = {((0 : ℤ), (0 : ℤ))} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hexFormNat_eq_iff, Int.natCast_zero,
      hexForm_eq_zero_iff]
  rw [repCount, h, Set.ncard_singleton]

private lemma tsum_fiber_eq (τ : ℂ) (n : ℕ) :
    ∑' v : (hexFormNat ⁻¹' {n}), latticeTerm τ v
      = (repCount n : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * τ) := by
  have hconst : ∀ v : (hexFormNat ⁻¹' {n}),
      latticeTerm τ v = Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * τ) := by
    rintro ⟨v, hv⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hv
    simp [latticeTerm, hv]
  rw [tsum_congr hconst, tsum_const, Nat.card_coe_set_eq, nsmul_eq_mul, repCount]

private theorem hasSum_repCount_qpow {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ ↦ (repCount n : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * τ))
      (latticeSum τ) := by
  have h := ((summable_latticeTerm hτ).hasSum).tsum_fiberwise hexFormNat
  simp only [tsum_fiber_eq τ] at h
  exact h

private theorem latticeSum_eq_tsum_repCount {τ : ℂ} (hτ : 0 < τ.im) :
    latticeSum τ
      = ∑' n : ℕ, (repCount n : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * τ) :=
  (hasSum_repCount_qpow hτ).tsum_eq.symm

open FLT.EisensteinWeightOne in

def RepresentationCountAgrees : Prop :=
  ∀ n : ℕ, (repCount n : ℤ) = PowerSeries.coeff n e1Chi3

open FLT.EisensteinWeightOne in

theorem latticeSum_eq_e1Chi3_qSeries (hW1 : RepresentationCountAgrees) (z : UpperHalfPlane) :
    latticeSum z
      = ∑' n : ℕ, ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
          Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * (z : ℂ)) := by
  rw [latticeSum_eq_tsum_repCount (UpperHalfPlane.coe_im z ▸ z.2)]
  refine tsum_congr fun n ↦ ?_
  congr 1
  rw [← hW1 n]
  push_cast
  rfl

end FLT.AnalyticCore.LatticeSum

end File_FLT_AnalyticCore_LatticeSumPlumbing

section File_FLT_AnalyticCore_RankTwoPoissonSummation

set_option autoImplicit false

open Complex Real

open scoped Topology

namespace FLT
namespace AnalyticCore

noncomputable section

def frickeFixedPoint : ℂ := I / (Real.sqrt 3 : ℂ)

lemma sqrt_three_ne_zero : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'

end

end FLT.AnalyticCore

end File_FLT_AnalyticCore_RankTwoPoissonSummation

section File_FLT_AnalyticCore_TwoGeneratorSweep

set_option autoImplicit false

open Matrix CongruenceSubgroup Subgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold Pointwise

namespace FLT
namespace AnalyticCore

def chi3 (γ : SL(2, ℤ)) : ℤ :=
  if (γ 1 1 : ZMod 3) = 1 then 1 else -1

private lemma chi3_eq_one_or_neg_one (γ : SL(2, ℤ)) : chi3 γ = 1 ∨ chi3 γ = -1 := by
  unfold chi3; split <;> simp

private lemma chi3_mul_self (γ : SL(2, ℤ)) : chi3 γ * chi3 γ = 1 := by
  rcases chi3_eq_one_or_neg_one γ with h | h <;> rw [h] <;> norm_num

@[simp] private lemma chi3_one : chi3 1 = 1 := by unfold chi3; norm_num

@[simp] private lemma chi3_T : chi3 ModularGroup.T = 1 := by
  unfold chi3; rw [show (ModularGroup.T 1 1 : ZMod 3) = 1 by decide]; simp

@[simp] private lemma chi3_U₃ : chi3 U₃ = 1 := by
  unfold chi3; rw [show (U₃ 1 1 : ZMod 3) = 1 by decide]; simp

@[simp] lemma chi3_neg_one : chi3 (-1 : SL(2, ℤ)) = -1 := by
  unfold chi3; rw [show ((-1 : SL(2, ℤ)) 1 1 : ZMod 3) = 2 by decide]; decide

private lemma apply_one_one_ne_zero_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) :
    (γ 1 1 : ZMod 3) ≠ 0 :=
  Gamma0Three.apply_one_one_ne_zero γ (Gamma0_mem.mp hγ)

private lemma coe_mul_apply_one_one {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) (hδ : δ ∈ Gamma0 3) :
    ((γ * δ) 1 1 : ZMod 3) = (γ 1 1 : ZMod 3) * (δ 1 1 : ZMod 3) := by
  have := map_mul (Gamma0Map 3) (⟨γ, hγ⟩ : Gamma0 3) (⟨δ, hδ⟩ : Gamma0 3)
  simpa [Gamma0Map] using this

private theorem chi3_mul {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) (hδ : δ ∈ Gamma0 3) :
    chi3 (γ * δ) = chi3 γ * chi3 δ := by
  have key : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
  unfold chi3
  rw [coe_mul_apply_one_one hγ hδ]
  rcases key _ (apply_one_one_ne_zero_of_mem hγ) with h1 | h1 <;>
    rcases key _ (apply_one_one_ne_zero_of_mem hδ) with h2 | h2 <;>
      rw [h1, h2] <;> decide

private theorem chi3_eq_one_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 3) : chi3 γ = 1 := by
  unfold chi3
  rw [((Gamma1_mem 3 γ).mp hγ).2.1]
  simp

section Sweep

variable (F : ℍ → ℂ)

theorem slash_neg_one :
    F ∣[(1 : ℤ)] (-1 : SL(2, ℤ)) = ((chi3 (-1 : SL(2, ℤ)) : ℤ) : ℂ) • F := by
  rw [chi3_neg_one]
  ext τ
  rw [ModularForm.SL_slash_apply]
  have hsmul : ((-1 : SL(2, ℤ)) • τ : ℍ) = τ := by
    rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, ModularGroup.SL_neg_smul, one_smul]
  have hden : denom (-1 : SL(2, ℤ)) τ = -1 := by
    rw [ModularGroup.denom_apply]
    norm_num [show ((-1 : SL(2, ℤ)) 1 0) = 0 from rfl, show ((-1 : SL(2, ℤ)) 1 1) = -1 from rfl]
  rw [hsmul, hden]
  have hpow : ((-1 : ℂ)) ^ (-(1 : ℤ)) = -1 := by norm_num
  rw [hpow]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem slash_eq_chi3_smul
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) :
    F ∣[(1 : ℤ)] γ = (chi3 γ : ℂ) • F := by

  let p : (g : SL(2, ℤ)) → g ∈ Subgroup.closure gens → Prop :=
    fun g _ => F ∣[(1 : ℤ)] g = (chi3 g : ℂ) • F

  have hmem_iff : ∀ {g : SL(2, ℤ)}, g ∈ Subgroup.closure gens ↔ g ∈ Gamma0 3 := by
    intro g; rw [closure_T_U_neg_one_eq]
  refine Subgroup.closure_induction (k := gens) (p := p) ?_ ?_ ?_ ?_ (hmem_iff.mpr hγ)
  ·
    rintro x (rfl | rfl | rfl)
    · show F ∣[(1 : ℤ)] ModularGroup.T = (chi3 ModularGroup.T : ℂ) • F
      rw [hT, chi3_T]; simp
    · show F ∣[(1 : ℤ)] U₃ = (chi3 U₃ : ℂ) • F
      rw [hU, chi3_U₃]; simp
    · exact slash_neg_one F
  ·
    show F ∣[(1 : ℤ)] (1 : SL(2, ℤ)) = (chi3 1 : ℂ) • F
    rw [SlashAction.slash_one, chi3_one]
    simp
  ·
    intro x y hx hy hpx hpy
    show F ∣[(1 : ℤ)] (x * y) = (chi3 (x * y) : ℂ) • F
    have hx' : x ∈ Gamma0 3 := hmem_iff.mp hx
    have hy' : y ∈ Gamma0 3 := hmem_iff.mp hy
    calc F ∣[(1 : ℤ)] (x * y) = (F ∣[(1 : ℤ)] x) ∣[(1 : ℤ)] y := by
            rw [SlashAction.slash_mul]
      _ = ((chi3 x : ℂ) • F) ∣[(1 : ℤ)] y := by rw [hpx]
      _ = (chi3 x : ℂ) • (F ∣[(1 : ℤ)] y) := by rw [ModularForm.SL_smul_slash]
      _ = (chi3 x : ℂ) • ((chi3 y : ℂ) • F) := by rw [hpy]
      _ = ((chi3 x * chi3 y : ℤ) : ℂ) • F := by rw [smul_smul]; norm_num
      _ = (chi3 (x * y) : ℂ) • F := by rw [← chi3_mul hx' hy']
  ·
    intro x hx hpx
    show F ∣[(1 : ℤ)] x⁻¹ = (chi3 x⁻¹ : ℂ) • F
    have hx' : x ∈ Gamma0 3 := hmem_iff.mp hx
    have hxinv : x⁻¹ ∈ Gamma0 3 := inv_mem hx'

    have hchi : chi3 x⁻¹ = chi3 x := by
      have h1 : chi3 (x⁻¹ * x) = chi3 x⁻¹ * chi3 x := chi3_mul hxinv hx'
      rw [inv_mul_cancel, chi3_one] at h1
      rcases chi3_eq_one_or_neg_one x with h | h <;>
        rcases chi3_eq_one_or_neg_one x⁻¹ with h' | h' <;> rw [h, h'] <;> rw [h, h'] at h1 <;>
          omega

    have h2 : (F ∣[(1 : ℤ)] x) ∣[(1 : ℤ)] x⁻¹ = ((chi3 x : ℂ) • F) ∣[(1 : ℤ)] x⁻¹ := by
      rw [hpx]
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      ModularForm.SL_smul_slash] at h2

    have h3 := congrArg (fun G => (chi3 x : ℂ) • G) h2
    simp only [smul_smul] at h3
    rw [show ((chi3 x : ℂ) * (chi3 x : ℂ)) = ((chi3 x * chi3 x : ℤ) : ℂ) by push_cast; ring,
      chi3_mul_self] at h3
    rw [hchi]
    simpa using h3.symm

private theorem slash_eq_self_of_mem_Gamma1
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 3) :
    F ∣[(1 : ℤ)] γ = F := by
  rw [slash_eq_chi3_smul F hT hU (Gamma1_in_Gamma0 3 hγ), chi3_eq_one_of_mem_Gamma1 hγ]
  simp

end Sweep

section Packaging

def slashInvariantForm_of_T_U (F : ℍ → ℂ)
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F) :
    SlashInvariantForm (Gamma1 3) 1 where
  toFun := F
  slash_action_eq' := by
    rintro γ ⟨δ, hδ, rfl⟩

    exact slash_eq_self_of_mem_Gamma1 F hT hU hδ

@[simp] private lemma coe_slashInvariantForm_of_T_U (F : ℍ → ℂ)
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F) :
    ⇑(slashInvariantForm_of_T_U F hT hU) = F := rfl

private theorem e1Chi3IsModular_of_analytic_inputs (F : ℍ → ℂ)
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F)
    (hholo : MDiff F)
    (hbdd : ∀ c : OnePoint ℝ, IsCusp c ((Gamma1 3 : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) → c.IsBoundedAt F 1)
    (hq : ∀ z : ℍ, F z = ∑' n : ℕ,
      ((PowerSeries.coeff n _root_.EisensteinWeightOne.e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))) :
    _root_.EisensteinWeightOne.E1Chi3IsModular := by
  exact ⟨{ slashInvariantForm_of_T_U F hT hU with
            holo' := hholo
            bdd_at_cusps' := fun {c} hc => hbdd c hc }, fun z => hq z⟩

end Packaging

end FLT.AnalyticCore

end File_FLT_AnalyticCore_TwoGeneratorSweep

section File_FLT_AnalyticCore_EisensteinModularityAssembly

set_option autoImplicit false

open Complex Real Matrix CongruenceSubgroup Subgroup ModularForm UpperHalfPlane
open FLT.AnalyticCore.LatticeSum FLT.EisensteinWeightOne
open scoped MatrixGroups ModularForm Manifold

namespace FLT
namespace AnalyticCore

noncomputable section

private lemma latticeTerm_eq_hexThetaTerm (τ : ℂ) (v : ℤ × ℤ) :
    latticeTerm τ v = hexThetaTerm τ v := by
  unfold latticeTerm hexThetaTerm
  congr 1
  have h : ((hexFormNat v : ℤ) : ℂ) = (v.1 : ℂ) ^ 2 + (v.1 : ℂ) * (v.2 : ℂ) + (v.2 : ℂ) ^ 2 := by
    rw [coe_hexFormNat]
    unfold hexForm
    push_cast
    ring
  push_cast at h
  rw [h]
  ring

theorem latticeSum_eq_hexTheta (τ : ℂ) : latticeSum τ = hexTheta τ :=
  tsum_congr fun v => latticeTerm_eq_hexThetaTerm τ v

def hexThetaH : ℍ → ℂ := fun τ => latticeSum (τ : ℂ)

@[simp] lemma hexThetaH_apply (τ : ℍ) : hexThetaH τ = latticeSum (τ : ℂ) := rfl

private lemma hexThetaH_eq_hexTheta (τ : ℍ) : hexThetaH τ = hexTheta (τ : ℂ) :=
  latticeSum_eq_hexTheta _

private lemma hexThetaTerm_add_one (σ : ℂ) (v : ℤ × ℤ) :
    hexThetaTerm (σ + 1) v = hexThetaTerm σ v := by
  rw [← latticeTerm_eq_hexThetaTerm, ← latticeTerm_eq_hexThetaTerm]
  unfold latticeTerm
  rw [show 2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * (σ + 1)
      = 2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * σ
        + (hexFormNat v : ℂ) * (2 * (π : ℂ) * Complex.I) by ring,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

private theorem hexTheta_add_one (σ : ℂ) : hexTheta (σ + 1) = hexTheta σ :=
  tsum_congr fun v => hexThetaTerm_add_one σ v

theorem hexThetaH_slash_T : hexThetaH ∣[(1 : ℤ)] ModularGroup.T = hexThetaH := by
  funext z
  refine (slash_action_eq'_iff 1 hexThetaH ModularGroup.T z).mpr ?_
  rw [show ModularGroup.T 1 0 = 0 from rfl, show ModularGroup.T 1 1 = 1 from rfl,
    modular_T_smul]
  simp only [Int.cast_zero, Int.cast_one, zero_mul, zero_add, zpow_one, one_mul]
  show latticeSum (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = latticeSum (z : ℂ)
  rw [UpperHalfPlane.coe_vadd, latticeSum_eq_hexTheta, latticeSum_eq_hexTheta,
    Complex.ofReal_one, add_comm, hexTheta_add_one]

private lemma sqrt_three_mul_sqrt_three : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

private lemma U_denom_ne_zero {z : ℂ} (hz : 0 < z.im) : (-3 : ℂ) * z + 1 ≠ 0 := by
  intro h
  have him : ((-3 : ℂ) * z + 1).im = -3 * z.im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [h] at him
  simp only [Complex.zero_im] at him
  nlinarith

private lemma U_smul_eq_fricke_translate_fricke {z : ℂ} (hz : 0 < z.im) :
    z / ((-3) * z + 1) = -1 / (3 * (-1 / (3 * z) + 1)) := by
  have hz0 : z ≠ 0 := ne_zero_of_im_pos hz
  have hden : (-3 : ℂ) * z + 1 ≠ 0 := U_denom_ne_zero hz

  have h1 : (3 : ℂ) * (-1 / (3 * z) + 1) = (3 * z - 1) / z := by
    field_simp
    ring
  have h2 : ((3 : ℂ) * z - 1) / z ≠ 0 := by
    refine div_ne_zero (fun h => hden ?_) hz0
    linear_combination -h
  rw [h1, div_eq_div_iff hden h2, mul_div_assoc', div_eq_iff hz0]
  ring

private lemma fricke_double_multiplier {z : ℂ} (hz : 0 < z.im) :
    -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
      * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z) = (-3) * z + 1 := by
  have hz0 : z ≠ 0 := ne_zero_of_im_pos hz
  have key : (-1 / (3 * z) + 1) * z = z - 1 / 3 := by
    field_simp
    ring
  calc -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
        * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z)
      = (Complex.I * Complex.I) * (((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))
          * ((-1 / (3 * z) + 1) * z) := by ring
    _ = (-1) * 3 * (z - 1 / 3) := by rw [Complex.I_mul_I, sqrt_three_mul_sqrt_three, key]
    _ = (-3) * z + 1 := by ring

theorem hexTheta_U_law {z : ℂ} (hz : 0 < z.im) :
    hexTheta (z / ((-3) * z + 1)) = ((-3) * z + 1) * hexTheta z := by

  have hσ : 0 < (-1 / (3 * z)).im := im_neg_one_div_three_mul_pos hz
  have hσ1 : 0 < (-1 / (3 * z) + 1).im := by
    rwa [Complex.add_im, Complex.one_im, add_zero]
  calc hexTheta (z / ((-3) * z + 1))
      = hexTheta (-1 / (3 * (-1 / (3 * z) + 1))) := by
        rw [U_smul_eq_fricke_translate_fricke hz]
    _ = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
          * hexTheta (-1 / (3 * z) + 1) := hexTheta_fricke hσ1
    _ = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
          * hexTheta (-1 / (3 * z)) := by rw [hexTheta_add_one]
    _ = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
          * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z * hexTheta z) := by
        rw [hexTheta_fricke hz]
    _ = ((-3) * z + 1) * hexTheta z := by
        rw [show -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
              * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z * hexTheta z)
            = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
              * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z) * hexTheta z by ring,
          fricke_double_multiplier hz]

private lemma coe_U_smul (z : ℍ) : ((U₃ • z : ℍ) : ℂ) = (z : ℂ) / ((-3) * (z : ℂ) + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [show U₃ 0 0 = 1 from rfl, show U₃ 0 1 = 0 from rfl,
    show U₃ 1 0 = -3 from rfl, show U₃ 1 1 = 1 from rfl, eq_intCast]
  push_cast
  rw [one_mul, add_zero]

theorem hexThetaH_slash_U : hexThetaH ∣[(1 : ℤ)] U₃ = hexThetaH := by
  funext z
  refine (slash_action_eq'_iff 1 hexThetaH U₃ z).mpr ?_
  have hz : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  rw [U₃_one_zero, U₃_one_one]
  push_cast
  rw [zpow_one]
  show latticeSum ((U₃ • z : ℍ) : ℂ) = _ * latticeSum (z : ℂ)
  rw [coe_U_smul, latticeSum_eq_hexTheta, latticeSum_eq_hexTheta, hexTheta_U_law hz]

def thetaBound : ℝ :=
  ∑' v : ℤ × ℤ, Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2))

private theorem norm_latticeSum_le_of_one_le_im {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖latticeSum τ‖ ≤ thetaBound := by
  have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos hτ

  have hdom : ∀ v : ℤ × ℤ, ‖latticeTerm τ v‖
      ≤ Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2)) := by
    intro v
    have h := norm_latticeTerm_le_of_le_im one_pos hτ v
    simpa only [mul_one, one_mul] using h

  have hgauss : Summable fun v : ℤ × ℤ =>
      Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2)) := by
    simpa only [mul_one, one_mul] using summable_gaussian_prod one_pos
  have hsum_norm : Summable fun v : ℤ × ℤ => ‖latticeTerm τ v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hgauss
  calc ‖latticeSum τ‖ ≤ ∑' v : ℤ × ℤ, ‖latticeTerm τ v‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' v : ℤ × ℤ, Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2)) :=
        hsum_norm.tsum_le_tsum hdom hgauss
    _ = thetaBound := rfl

private theorem isBoundedAtImInfty_hexThetaH : IsBoundedAtImInfty hexThetaH := by
  refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨thetaBound, 1, fun z hz => ?_⟩
  exact norm_latticeSum_le_of_one_le_im (by rwa [UpperHalfPlane.coe_im])

private lemma im_add_natCast_div_three (w : ℂ) (n : ℕ) : ((w + (n : ℂ)) / 3).im = w.im / 3 := by
  rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
  simp [Complex.add_im]

private lemma norm_neg_I_div_sqrt_three_le_one :
    ‖(-Complex.I / ((Real.sqrt 3 : ℝ) : ℂ))‖ ≤ 1 := by
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 3), div_le_one (by linarith)]
  exact h3

private theorem hexThetaH_slash_repOfLabel_apply (k : ZMod 3) (z : ℍ) :
    (hexThetaH ∣[(1 : ℤ)] Gamma0Three.repOfLabel (some k)) z
      = (-Complex.I / ((Real.sqrt 3 : ℝ) : ℂ)) * hexTheta (((z : ℂ) + (k.val : ℂ)) / 3) := by
  have hz : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos

  have hden_im : ((z : ℂ) + (k.val : ℂ)).im = (z : ℂ).im := by
    simp only [Complex.add_im, Complex.natCast_im, add_zero]
  have hden_ne : (z : ℂ) + (k.val : ℂ) ≠ 0 := by
    intro h
    rw [← Complex.zero_im, ← h, hden_im] at hz
    exact lt_irrefl _ hz

  have hσ_im : 0 < (((z : ℂ) + (k.val : ℂ)) / 3).im := by
    rw [im_add_natCast_div_three]
    positivity

  have hsmul : ((Gamma0Three.repOfLabel (some k) • z : ℍ) : ℂ)
      = -1 / ((z : ℂ) + (k.val : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [show Gamma0Three.repOfLabel (some k) 0 0 = 0 from rfl,
      show Gamma0Three.repOfLabel (some k) 0 1 = -1 from rfl,
      show Gamma0Three.repOfLabel (some k) 1 0 = 1 from rfl,
      show Gamma0Three.repOfLabel (some k) 1 1 = (k.val : ℤ) from rfl, eq_intCast]
    push_cast
    rw [zero_mul, zero_add, one_mul]

  have hdenom : denom (Gamma0Three.repOfLabel (some k)) z = (z : ℂ) + (k.val : ℂ) := by
    rw [ModularGroup.denom_apply,
      show Gamma0Three.repOfLabel (some k) 1 0 = 1 from rfl,
      show Gamma0Three.repOfLabel (some k) 1 1 = (k.val : ℤ) from rfl]
    push_cast
    rw [one_mul]

  have hfricke : hexTheta (-1 / ((z : ℂ) + (k.val : ℂ)))
      = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3)
        * hexTheta (((z : ℂ) + (k.val : ℂ)) / 3) := by
    have h := hexTheta_fricke hσ_im
    rw [show (3 : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3) = (z : ℂ) + (k.val : ℂ) by ring] at h
    exact h

  have hmul : -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3)
      * ((z : ℂ) + (k.val : ℂ))⁻¹ = -Complex.I / ((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [eq_div_iff sqrt_three_ne_zero,
      show -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3)
          * ((z : ℂ) + (k.val : ℂ))⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)
        = -Complex.I * (((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))
          * (((z : ℂ) + (k.val : ℂ)) * ((z : ℂ) + (k.val : ℂ))⁻¹) / 3 by ring,
      sqrt_three_mul_sqrt_three, mul_inv_cancel₀ hden_ne]
    ring

  rw [ModularForm.SL_slash_apply, hdenom, _root_.zpow_neg, zpow_one]
  show latticeSum ((Gamma0Three.repOfLabel (some k) • z : ℍ) : ℂ) * _ = _
  rw [hsmul, latticeSum_eq_hexTheta, hfricke]
  linear_combination (hexTheta (((z : ℂ) + (k.val : ℂ)) / 3)) * hmul

private theorem isBoundedAtImInfty_hexThetaH_slash (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (hexThetaH ∣[(1 : ℤ)] γ) := by

  set r := Gamma0Three.repOfLabel (Gamma0Three.label γ) with hr
  have hδ : γ * r⁻¹ ∈ Gamma0 3 :=
    (Gamma0Three.mul_inv_repOfLabel_mem_iff γ (Gamma0Three.label γ)).mpr rfl
  have hfact : γ = γ * r⁻¹ * r := (inv_mul_cancel_right γ r).symm
  rw [hfact, SlashAction.slash_mul,
    slash_eq_chi3_smul hexThetaH hexThetaH_slash_T hexThetaH_slash_U hδ,
    ModularForm.SL_smul_slash]

  refine Filter.BoundedAtFilter.smul _ ?_

  rcases hcase : Gamma0Three.label γ with _ | k
  ·
    rw [hr, hcase, Gamma0Three.repOfLabel_none, SlashAction.slash_one]
    exact isBoundedAtImInfty_hexThetaH
  ·
    rw [hr, hcase]
    refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨thetaBound, 3, fun z hz => ?_⟩
    rw [hexThetaH_slash_repOfLabel_apply k z, norm_mul]
    have him : 1 ≤ (((z : ℂ) + (k.val : ℂ)) / 3).im := by
      rw [im_add_natCast_div_three, UpperHalfPlane.coe_im, le_div_iff₀ (by norm_num)]
      linarith
    have hbound : ‖hexTheta (((z : ℂ) + (k.val : ℂ)) / 3)‖ ≤ thetaBound := by
      rw [← latticeSum_eq_hexTheta]
      exact norm_latticeSum_le_of_one_le_im him
    calc ‖(-Complex.I / ((Real.sqrt 3 : ℝ) : ℂ))‖ * ‖hexTheta (((z : ℂ) + (k.val : ℂ)) / 3)‖
        ≤ 1 * thetaBound :=
          mul_le_mul norm_neg_I_div_sqrt_three_le_one hbound (norm_nonneg _) zero_le_one
      _ = thetaBound := one_mul _

theorem hexThetaH_isBoundedAt_cusp (c : OnePoint ℝ)
    (hc : IsCusp c ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt hexThetaH 1 := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  refine (OnePoint.isBoundedAt_iff rfl).mpr ?_
  exact isBoundedAtImInfty_hexThetaH_slash γ

private theorem e1Chi3IsModular_of_mdiff_of_repCount
    (hholo : MDiff hexThetaH) (hW1 : RepresentationCountAgrees) :
    E1Chi3IsModular :=
  e1Chi3IsModular_of_analytic_inputs hexThetaH
    hexThetaH_slash_T
    hexThetaH_slash_U
    hholo
    (fun c hc => hexThetaH_isBoundedAt_cusp c hc)
    (fun z => latticeSum_eq_e1Chi3_qSeries hW1 z)

end

end FLT.AnalyticCore

end File_FLT_AnalyticCore_EisensteinModularityAssembly

section File_FLT_AnalyticCore_ThetaHolomorphy

set_option autoImplicit false

open Complex Real Filter
open FLT.AnalyticCore.LatticeSum FLT.EisensteinWeightOne
open scoped Manifold Topology

namespace FLT
namespace AnalyticCore

noncomputable section

private lemma differentiable_latticeTerm (v : ℤ × ℤ) :
    Differentiable ℂ fun τ : ℂ => latticeTerm τ v := by
  unfold latticeTerm
  fun_prop

private lemma isOpen_lt_im (T : ℝ) : IsOpen {z : ℂ | T < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem differentiableOn_latticeSum_of_lt_im {T : ℝ} (hT : 0 < T) :
    DifferentiableOn ℂ latticeSum {z : ℂ | T < z.im} := by
  have h := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (v : ℤ × ℤ) (τ : ℂ) => latticeTerm τ v)
    (summable_gaussian_prod hT)
    (fun v => (differentiable_latticeTerm v).differentiableOn)
    (isOpen_lt_im T)
    (fun v w hw => norm_latticeTerm_le_of_le_im hT (le_of_lt hw) v)
  exact h

theorem differentiableAt_latticeSum {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ latticeSum τ := by
  have hT : (0 : ℝ) < τ.im / 2 := by positivity
  have hmem : τ ∈ {z : ℂ | τ.im / 2 < z.im} := by
    simp only [Set.mem_ofPred_eq]
    linarith
  exact (differentiableOn_latticeSum_of_lt_im hT).differentiableAt
    ((isOpen_lt_im _).mem_nhds hmem)

private theorem differentiableOn_latticeSum :
    DifferentiableOn ℂ latticeSum {z : ℂ | 0 < z.im} :=
  fun _ hz => (differentiableAt_latticeSum hz).differentiableWithinAt

theorem mdifferentiable_hexThetaH : MDiff hexThetaH := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := latticeSum) differentiableOn_latticeSum
    (fun z hz => ?_)
  simp [hexThetaH, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

private theorem e1Chi3IsModular_of_repCount (hW1 : RepresentationCountAgrees) :
    E1Chi3IsModular :=
  e1Chi3IsModular_of_mdiff_of_repCount mdifferentiable_hexThetaH hW1

end

end FLT.AnalyticCore

end File_FLT_AnalyticCore_ThetaHolomorphy

section File_FLT_AnalyticCore_RepresentationNumberIdentity

namespace FLT
namespace AnalyticCore

open Finset FLT.EisensteinWeightOne

def hexForm (x y : ℤ) : ℤ := x * x + x * y + y * y

theorem four_mul_hexForm (x y : ℤ) :
    4 * hexForm x y = (2 * x + y) ^ 2 + 3 * y ^ 2 := by
  unfold hexForm; ring

theorem hexForm_nonneg (x y : ℤ) : 0 ≤ hexForm x y := by
  nlinarith [four_mul_hexForm x y, sq_nonneg (2 * x + y), sq_nonneg y]

private theorem hexForm_eq_zero_iff {x y : ℤ} : hexForm x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h4 := four_mul_hexForm x y
    rw [h, mul_zero] at h4
    have hy : y = 0 := by nlinarith [sq_nonneg (2 * x + y), sq_nonneg y]
    have hx : x = 0 := by nlinarith [sq_nonneg (2 * x + y), sq_nonneg y]
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem hexForm_swap (x y : ℤ) : hexForm y x = hexForm x y := by
  unfold hexForm; ring

noncomputable def reprBox (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)

noncomputable def reprSols (n : ℕ) : Finset (ℤ × ℤ) :=
  (reprBox n).filter fun p => hexForm p.1 p.2 = (n : ℤ)

noncomputable def reprCount (n : ℕ) : ℕ := (reprSols n).card

private theorem snd_abs_le_of_hexForm_eq {x y : ℤ} {n : ℕ} (h : hexForm x y = (n : ℤ)) :
    -(n : ℤ) ≤ y ∧ y ≤ (n : ℤ) := by
  have h4 : (2 * x + y) ^ 2 + 3 * y ^ 2 = 4 * (n : ℤ) := by
    rw [← four_mul_hexForm, h]
  have h3 : 3 * y ^ 2 ≤ 4 * (n : ℤ) := by nlinarith [sq_nonneg (2 * x + y)]
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  constructor
  · nlinarith [sq_nonneg (y + (n : ℤ)), sq_nonneg y]
  · nlinarith [sq_nonneg (y - (n : ℤ)), sq_nonneg y]

private theorem mem_reprBox_of_hexForm_eq {x y : ℤ} {n : ℕ} (h : hexForm x y = (n : ℤ)) :
    (x, y) ∈ reprBox n := by
  have hy := snd_abs_le_of_hexForm_eq h
  have hx := snd_abs_le_of_hexForm_eq (x := y) (y := x) (by rwa [hexForm_swap])
  simp only [reprBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hx.1, hx.2⟩, ⟨hy.1, hy.2⟩⟩

theorem mem_reprSols_iff {p : ℤ × ℤ} {n : ℕ} :
    p ∈ reprSols n ↔ hexForm p.1 p.2 = (n : ℤ) := by
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    exact Finset.mem_filter.mpr ⟨by simpa using mem_reprBox_of_hexForm_eq hp, hp⟩

private theorem reprCount_zero : reprCount 0 = 1 := by decide

theorem reprCount_one : reprCount 1 = 6 := by decide

theorem reprCount_eq_coeff_e1Chi3_zero :
    (reprCount 0 : ℤ) = PowerSeries.coeff 0 e1Chi3 := by
  rw [reprCount_zero, coeff_e1Chi3]; norm_num

theorem reprCount_eq_coeff_e1Chi3_one :
    (reprCount 1 : ℤ) = PowerSeries.coeff 1 e1Chi3 := by
  rw [reprCount_one, coeff_one_e1Chi3]; norm_num

def ReprCountEqCoeffE1Chi3 : Prop :=
  ∀ n : ℕ, (reprCount n : ℤ) = PowerSeries.coeff n e1Chi3

end FLT.AnalyticCore

end File_FLT_AnalyticCore_RepresentationNumberIdentity

section File_FLT_AnalyticCore_SplittingLawHalf

namespace FLT
namespace AnalyticCore

open Finset FLT.EisensteinWeightOne

private theorem hexForm_mul (a b c d : ℤ) :
    hexForm a b * hexForm c d = hexForm (a * c - b * d) (a * d + b * c + b * d) := by
  simp only [hexForm]; ring

private theorem hexForm_smul (c x y : ℤ) : hexForm (c * x) (c * y) = c ^ 2 * hexForm x y := by
  simp only [hexForm]; ring

section Inert

variable {p : ℕ}

private theorem not_isRoot_of_inert (hp : p.Prime) (h2 : p % 3 = 2) (t : ZMod p) :
    t ^ 2 + t + 1 ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro ht
  have hp3 : p ≠ 3 := by rintro rfl; omega
  have hord : orderOf t = 3 :=
    (ModularCurve.sq_add_self_add_one_eq_zero_iff_orderOf_eq_three hp hp3 t).mp ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact one_ne_zero (α := ZMod p) (by linear_combination ht)
  have hdvd : (3 : ℕ) ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one ht0
  have := hp.two_le
  omega

private theorem inert_dvd_right_of_dvd_hexForm (hp : p.Prime) (h2 : p % 3 = 2) {x y : ℤ}
    (h : (p : ℤ) ∣ hexForm x y) : (p : ℤ) ∣ y := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  by_contra hy
  have hyu : (y : ZMod p) * (y : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hy
  have hQ : (x : ZMod p) ^ 2 + (x : ZMod p) * (y : ZMod p) + (y : ZMod p) ^ 2 = 0 := by
    have h' : ((hexForm x y : ℤ) : ZMod p) = 0 := h
    push_cast [hexForm] at h'
    linear_combination h'
  refine not_isRoot_of_inert hp h2 ((x : ZMod p) * (y : ZMod p)⁻¹) ?_
  linear_combination ((y : ZMod p)⁻¹ * (y : ZMod p)⁻¹) * hQ +
    (-((x : ZMod p) * (y : ZMod p)⁻¹) - 1 - (y : ZMod p) * (y : ZMod p)⁻¹) * hyu

private theorem inert_dvd_of_dvd_hexForm (hp : p.Prime) (h2 : p % 3 = 2) {x y : ℤ}
    (h : (p : ℤ) ∣ hexForm x y) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  refine ⟨?_, inert_dvd_right_of_dvd_hexForm hp h2 h⟩
  exact inert_dvd_right_of_dvd_hexForm hp h2 (x := y) (y := x) (by rwa [hexForm_swap])

theorem inert_sq_dvd_of_dvd_hexForm (hp : p.Prime) (h2 : p % 3 = 2) {x y : ℤ}
    (h : (p : ℤ) ∣ hexForm x y) : (p : ℤ) ^ 2 ∣ hexForm x y := by
  obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ := inert_dvd_of_dvd_hexForm hp h2 h
  exact ⟨hexForm x' y', by rw [hexForm_smul]⟩

private theorem reprCount_eq_zero_of_inert (hp : p.Prime) (h2 : p % 3 = 2) :
    reprCount p = 0 := by
  rw [reprCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨x, y⟩ hxy
  have hQ : hexForm x y = (p : ℤ) := mem_reprSols_iff.mp hxy
  have hpd : (p : ℤ) ∣ hexForm x y := by rw [hQ]
  have hsq : (p : ℤ) ^ 2 ∣ (p : ℤ) := by
    have h' := inert_sq_dvd_of_dvd_hexForm hp h2 hpd
    rwa [hQ] at h'
  have hple : (p : ℤ) ^ 2 ≤ (p : ℤ) := Int.le_of_dvd (by exact_mod_cast hp.pos) hsq
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  nlinarith

private theorem reprSols_sq_mul_of_inert (hp : p.Prime) (h2 : p % 3 = 2) (m : ℕ) :
    reprSols (p ^ 2 * m)
      = (reprSols m).image fun q => ((p : ℤ) * q.1, (p : ℤ) * q.2) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_image, mem_reprSols_iff, Prod.mk.injEq, Prod.exists]
  constructor
  · intro hQ
    have hpd : (p : ℤ) ∣ hexForm x y := by
      rw [hQ]; push_cast; exact ⟨(p : ℤ) * m, by ring⟩
    obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ := inert_dvd_of_dvd_hexForm hp h2 hpd
    refine ⟨x', y', ?_, rfl, rfl⟩
    have hp0 : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.pos.ne')
    refine mul_left_cancel₀ hp0 ?_
    rw [← hexForm_smul, hQ]; push_cast; ring
  · rintro ⟨u, v, hQ, rfl, rfl⟩
    rw [hexForm_smul, hQ]; push_cast; ring

private theorem reprCount_sq_mul_of_inert (hp : p.Prime) (h2 : p % 3 = 2) (m : ℕ) :
    reprCount (p ^ 2 * m) = reprCount m := by
  rw [reprCount, reprCount, reprSols_sq_mul_of_inert hp h2 m]
  refine Finset.card_image_of_injOn fun q _ q' _ h => ?_
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (mul_left_cancel₀ hp0 h.1) (mul_left_cancel₀ hp0 h.2)

end Inert

private theorem hexForm_ramified_ascent (u v : ℤ) :
    hexForm (2 * u + v) (v - u) = 3 * hexForm u v := by
  simp only [hexForm]; ring

private theorem three_dvd_sub_of_dvd_hexForm {x y : ℤ} (h : (3 : ℤ) ∣ hexForm x y) :
    (3 : ℤ) ∣ x - y := by
  have hsq : (3 : ℤ) ∣ (x - y) ^ 2 := by
    obtain ⟨c, hc⟩ := h
    refine ⟨c - x * y, ?_⟩
    simp only [hexForm] at hc
    linear_combination hc
  exact (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow hsq

private theorem reprSols_three_mul (m : ℕ) :
    reprSols (3 * m) = (reprSols m).image fun q => (2 * q.1 + q.2, q.2 - q.1) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_image, mem_reprSols_iff, Prod.mk.injEq, Prod.exists]
  constructor
  · intro hQ
    have h3 : (3 : ℤ) ∣ hexForm x y := by rw [hQ]; push_cast; exact ⟨m, by ring⟩
    obtain ⟨u, hu⟩ := three_dvd_sub_of_dvd_hexForm h3

    refine ⟨u, y + u, ?_, by linarith, by ring⟩
    refine mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) ?_
    rw [← hexForm_ramified_ascent]
    have hx : 2 * u + (y + u) = x := by linarith
    have hy : (y + u) - u = y := by ring
    rw [hx, hy, hQ]; push_cast; ring
  · rintro ⟨u, v, hQ, rfl, rfl⟩
    rw [hexForm_ramified_ascent, hQ]; push_cast; ring

theorem reprCount_three_mul (m : ℕ) : reprCount (3 * m) = reprCount m := by
  rw [reprCount, reprCount, reprSols_three_mul m]
  refine Finset.card_image_of_injOn fun q _ q' _ h => ?_
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  exact Prod.ext (by linarith) (by linarith)

private theorem sigmaChi_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigmaChi (p ^ k) = ∑ j ∈ Finset.range (k + 1), chiNegThree p ^ j := by
  rw [sigmaChi, Nat.divisors_prime_pow hp, Finset.sum_map]
  exact Finset.sum_congr rfl fun j _ => chiNegThree_pow p j

private theorem sigmaChi_three_pow (k : ℕ) : sigmaChi (3 ^ k) = 1 := by
  rw [sigmaChi_prime_pow (by norm_num) k]
  rw [show chiNegThree 3 = 0 from chiNegThree_three]
  rw [Finset.sum_congr rfl fun j _ => zero_pow_eq j]
  simp

private theorem sigmaChi_inert_pow {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) (k : ℕ) :
    sigmaChi (p ^ k) = if Even k then 1 else 0 := by
  rw [sigmaChi_prime_pow hp k]
  have hchi : chiNegThree p = -1 := by
    simp [chiNegThree, h2]
  rw [hchi, neg_one_geom_sum]
  rcases Nat.even_or_odd k with hk | hk
  · rw [ite_eq_left hk, ite_eq_right (Nat.not_even_iff_odd.mpr hk.add_one)]
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hk), ite_eq_left hk.add_one]

private theorem reprCount_three_pow (k : ℕ) : reprCount (3 ^ k) = 6 := by
  induction k with
  | zero => simpa using reprCount_one
  | succ k ih => rw [pow_succ, mul_comm, reprCount_three_mul, ih]

private theorem reprCount_inert_pow {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) (k : ℕ) :
    reprCount (p ^ k) = if Even k then 6 else 0 := by
  have heven : ∀ j : ℕ, reprCount (p ^ (2 * j)) = 6 := by
    intro j
    induction j with
    | zero => simpa using reprCount_one
    | succ j ih =>
      have hstep : p ^ (2 * (j + 1)) = p ^ 2 * p ^ (2 * j) := by ring
      rw [hstep, reprCount_sq_mul_of_inert hp h2, ih]
  have hodd : ∀ j : ℕ, reprCount (p ^ (2 * j + 1)) = 0 := by
    intro j
    induction j with
    | zero => simpa using reprCount_eq_zero_of_inert hp h2
    | succ j ih =>
      have hstep : p ^ (2 * (j + 1) + 1) = p ^ 2 * p ^ (2 * j + 1) := by ring
      rw [hstep, reprCount_sq_mul_of_inert hp h2, ih]
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, hj⟩ := hk
    rw [ite_eq_left ⟨j, hj⟩, hj, ← two_mul, heven]
  · obtain ⟨j, hj⟩ := hk
    rw [ite_eq_right (Nat.not_even_iff_odd.mpr ⟨j, hj⟩), hj, hodd]

def OrbitCountMultiplicative : Prop :=
  ∀ m n : ℕ, Nat.Coprime m n → 6 * reprCount (m * n) = reprCount m * reprCount n

def SplitPrimePowCount : Prop :=
  ∀ p k : ℕ, p.Prime → p % 3 = 1 → reprCount (p ^ k) = 6 * (k + 1)

private theorem sigmaChi_split_pow {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) (k : ℕ) :
    sigmaChi (p ^ k) = k + 1 := by
  rw [sigmaChi_prime_pow hp k]
  have hchi : chiNegThree p = 1 := by
    simp [chiNegThree, h1]
  rw [hchi]
  simp

theorem reprCountEqCoeffE1Chi3_of_residuals
    (hmul : OrbitCountMultiplicative) (hsplit : SplitPrimePowCount) :
    ReprCountEqCoeffE1Chi3 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact reprCount_eq_coeff_e1Chi3_zero
  | one => exact reprCount_eq_coeff_e1Chi3_one
  | prime_pow p k hp hk =>
    have hp' : p.Prime := hp
    have hpk : p ^ k ≠ 0 := pow_ne_zero k hp'.pos.ne'
    rw [coeff_e1Chi3_of_ne_zero hpk]
    rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h0 | h1 | h2
    ·
      have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp').mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
      subst hp3
      rw [reprCount_three_pow, sigmaChi_three_pow]
      norm_num
    ·
      rw [hsplit p k hp' h1, sigmaChi_split_pow hp' h1]
      push_cast
      ring
    ·
      rw [reprCount_inert_pow hp' h2, sigmaChi_inert_pow hp' h2]
      rcases Nat.even_or_odd k with hk' | hk'
      · rw [ite_eq_left hk', ite_eq_left hk']; norm_num
      · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hk'),
          ite_eq_right (Nat.not_even_iff_odd.mpr hk')]
        norm_num
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hab0 : a * b ≠ 0 := Nat.mul_ne_zero ha0 hb0
    refine mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0) ?_
    have hkey : (6 : ℤ) * (reprCount (a * b) : ℤ)
        = (reprCount a : ℤ) * (reprCount b : ℤ) := by
      exact_mod_cast hmul a b hab
    rw [hkey, iha, ihb, coeff_e1Chi3_of_ne_zero ha0, coeff_e1Chi3_of_ne_zero hb0,
      coeff_e1Chi3_of_ne_zero hab0, sigmaChi_mul_of_coprime a b hab]
    ring

end FLT.AnalyticCore

end File_FLT_AnalyticCore_SplittingLawHalf

section File_FLT_AnalyticCore_OrbitCountMultiplicative

namespace FLT
namespace AnalyticCore

open Finset

@[ext]
structure HexInt where

  re : ℤ

  im : ℤ
  deriving DecidableEq

namespace HexInt

private instance : Zero HexInt := ⟨⟨0, 0⟩⟩

@[simp] private theorem re_zero : (0 : HexInt).re = 0 := rfl
@[simp] private theorem im_zero : (0 : HexInt).im = 0 := rfl

private instance : One HexInt := ⟨⟨1, 0⟩⟩

@[simp] private theorem re_one : (1 : HexInt).re = 1 := rfl
@[simp] private theorem im_one : (1 : HexInt).im = 0 := rfl

private instance : Add HexInt := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp] private theorem re_add (z w : HexInt) : (z + w).re = z.re + w.re := rfl
@[simp] private theorem im_add (z w : HexInt) : (z + w).im = z.im + w.im := rfl

private instance : Neg HexInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] private theorem re_neg (z : HexInt) : (-z).re = -z.re := rfl
@[simp] private theorem im_neg (z : HexInt) : (-z).im = -z.im := rfl

private instance : Mul HexInt :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re + z.im * w.im⟩⟩

@[simp] private theorem re_mul (z w : HexInt) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] private theorem im_mul (z w : HexInt) :
    (z * w).im = z.re * w.im + z.im * w.re + z.im * w.im := rfl

private instance addCommGroup : AddCommGroup HexInt := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec HexInt ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec HexInt ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec HexInt ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp] private theorem re_sub (z w : HexInt) : (z - w).re = z.re - w.re := rfl
@[simp] private theorem im_sub (z w : HexInt) : (z - w).im = z.im - w.im := rfl

private instance addGroupWithOne : AddGroupWithOne HexInt :=
  { HexInt.addCommGroup with
    natCast := fun n => ⟨(n : ℤ), 0⟩
    intCast := fun n => ⟨n, 0⟩ }

private instance commRing : CommRing HexInt := by
  refine
  { HexInt.addGroupWithOne with
    npow := @npowRec HexInt ⟨1⟩ ⟨(· * ·)⟩
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

private instance : Nontrivial HexInt :=
  ⟨⟨0, 1, fun h => one_ne_zero (α := ℤ) (by simpa using congrArg HexInt.re h.symm)⟩⟩

@[simp] private theorem re_intCast (n : ℤ) : (n : HexInt).re = n := by cases n <;> rfl
@[simp] private theorem im_intCast (n : ℤ) : (n : HexInt).im = 0 := by cases n <;> rfl
@[simp] private theorem re_natCast (n : ℕ) : (n : HexInt).re = n := rfl
@[simp] private theorem im_natCast (n : ℕ) : (n : HexInt).im = 0 := rfl

def conj (z : HexInt) : HexInt := ⟨z.re + z.im, -z.im⟩

@[simp] private theorem re_conj (z : HexInt) : z.conj.re = z.re + z.im := rfl
@[simp] private theorem im_conj (z : HexInt) : z.conj.im = -z.im := rfl

@[simp] private theorem conj_zero : (0 : HexInt).conj = 0 := by ext <;> simp [conj]

private def norm (z : HexInt) : ℤ := hexForm z.re z.im

@[simp] private theorem norm_mk (a b : ℤ) : norm ⟨a, b⟩ = hexForm a b := rfl

@[simp] private theorem norm_zero : (0 : HexInt).norm = 0 := rfl

@[simp] private theorem norm_one : (1 : HexInt).norm = 1 := rfl

@[simp] private theorem norm_intCast (n : ℤ) : (n : HexInt).norm = n ^ 2 := by
  simp only [norm, re_intCast, im_intCast, hexForm]; ring

@[simp] private theorem norm_natCast (n : ℕ) : ((n : ℕ) : HexInt).norm = (n : ℤ) ^ 2 := by
  simp only [norm, re_natCast, im_natCast, hexForm]; ring

private theorem norm_mul (z w : HexInt) : (z * w).norm = z.norm * w.norm := by
  simp only [norm, re_mul, im_mul, hexForm]; ring

private def normHom : HexInt →* ℤ where
  toFun := norm
  map_one' := norm_one
  map_mul' := norm_mul

@[simp] private theorem normHom_apply (z : HexInt) : normHom z = z.norm := rfl

theorem norm_nonneg (z : HexInt) : 0 ≤ z.norm := hexForm_nonneg _ _

private theorem norm_eq_zero_iff {z : HexInt} : z.norm = 0 ↔ z = 0 := by
  rw [norm, hexForm_eq_zero_iff, HexInt.ext_iff, re_zero, im_zero]

private theorem norm_pos {z : HexInt} (hz : z ≠ 0) : 0 < z.norm :=
  lt_of_le_of_ne (norm_nonneg z) fun h => hz (norm_eq_zero_iff.mp h.symm)

private theorem mul_conj (z : HexInt) : z * z.conj = (z.norm : HexInt) := by
  ext <;> simp only [re_mul, im_mul, re_conj, im_conj, re_intCast, im_intCast, norm,
    hexForm] <;> ring

private theorem norm_conj (z : HexInt) : z.conj.norm = z.norm := by
  simp only [norm, re_conj, im_conj, hexForm]; ring

private theorem norm_dvd_norm {z w : HexInt} (h : z ∣ w) : z.norm ∣ w.norm := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.norm, norm_mul z c⟩

theorem isUnit_iff_norm_eq_one {z : HexInt} : IsUnit z ↔ z.norm = 1 := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp h
    have h1 : z.norm * w.norm = 1 := by rw [← norm_mul, hw, norm_one]
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨w.norm, h1.symm⟩) with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ norm_nonneg z) (by norm_num)
  · intro h
    exact isUnit_of_dvd_one ⟨z.conj, (show z * z.conj = 1 by
      rw [mul_conj, h, Int.cast_one]).symm⟩

private def nearestDiv (u n : ℤ) : ℤ := (2 * u + n) / (2 * n)

private theorem nearestDiv_bound {n : ℤ} (hn : 0 < n) (u : ℤ) :
    -n ≤ 2 * (u - n * nearestDiv u n) ∧ 2 * (u - n * nearestDiv u n) < n := by
  have h2n : (0 : ℤ) < 2 * n := by linarith
  have hdiv := Int.mul_ediv_add_emod (2 * u + n) (2 * n)
  have hge := Int.emod_nonneg (2 * u + n) (by positivity : (2 : ℤ) * n ≠ 0)
  have hlt := Int.emod_lt_of_pos (2 * u + n) h2n
  have key : 2 * (u - n * nearestDiv u n) = (2 * u + n) % (2 * n) - n := by
    unfold nearestDiv
    linear_combination -hdiv
  constructor <;> rw [key] <;> linarith

private instance : Div HexInt :=
  ⟨fun x y => ⟨nearestDiv (x * y.conj).re y.norm, nearestDiv (x * y.conj).im y.norm⟩⟩

private theorem div_def (x y : HexInt) :
    x / y = ⟨nearestDiv (x * y.conj).re y.norm, nearestDiv (x * y.conj).im y.norm⟩ := rfl

private theorem div_zero' (x : HexInt) : x / 0 = 0 := by
  ext <;> simp [div_def, nearestDiv]

private instance : Mod HexInt := ⟨fun x y => x - y * (x / y)⟩

private theorem mod_def (x y : HexInt) : x % y = x - y * (x / y) := rfl

private theorem norm_mod_lt (x : HexInt) {y : HexInt} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  have hn : 0 < y.norm := norm_pos hy

  have hkey : (x % y) * y.conj = x * y.conj - (y.norm : HexInt) * (x / y) := by
    rw [mod_def, sub_mul, mul_comm y (x / y), mul_assoc, mul_conj]; ring
  have hre : ((x % y) * y.conj).re
      = (x * y.conj).re - y.norm * nearestDiv (x * y.conj).re y.norm := by
    rw [hkey]
    simp only [re_sub, re_mul, im_mul, im_intCast, re_intCast, div_def]
    ring
  have him : ((x % y) * y.conj).im
      = (x * y.conj).im - y.norm * nearestDiv (x * y.conj).im y.norm := by
    rw [hkey]
    simp only [im_sub, re_mul, im_mul, im_intCast, re_intCast, div_def]
    ring

  obtain ⟨hA1, hA2⟩ := nearestDiv_bound hn (x * y.conj).re
  obtain ⟨hB1, hB2⟩ := nearestDiv_bound hn (x * y.conj).im
  set A := ((x % y) * y.conj).re with hA_def
  set B := ((x % y) * y.conj).im with hB_def
  rw [← hre] at hA1 hA2
  rw [← him] at hB1 hB2

  have hbound : 4 * hexForm A B ≤ 3 * y.norm ^ 2 := by
    have h1 : (0 : ℤ) ≤ (y.norm - 2 * A) * (y.norm + 2 * A) := by nlinarith
    have h2 : (0 : ℤ) ≤ (y.norm - 2 * B) * (y.norm + 2 * B) := by nlinarith
    have h3 : (0 : ℤ) ≤ (y.norm - 2 * A) * (y.norm + 2 * B) := by nlinarith
    have h4 : (0 : ℤ) ≤ (y.norm + 2 * A) * (y.norm - 2 * B) := by nlinarith
    simp only [hexForm]
    nlinarith

  have hprod : hexForm A B = (x % y).norm * y.norm := by
    rw [hA_def, hB_def]
    have : ((x % y) * y.conj).norm = (x % y).norm * y.norm := by
      rw [norm_mul, norm_conj]
    simpa [norm] using this
  rw [hprod] at hbound
  nlinarith

private theorem natAbs_norm_mod_lt (x : HexInt) {y : HexInt} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := norm_mod_lt x hy
  have h1 := norm_nonneg (x % y)
  have h2 := norm_nonneg y
  omega

private theorem natAbs_norm_le_natAbs_norm_mul (a : HexInt) {b : HexInt} (hb : b ≠ 0) :
    a.norm.natAbs ≤ (a * b).norm.natAbs := by
  have h1 : a.norm ≤ (a * b).norm := by
    rw [norm_mul]
    have hb1 : 1 ≤ b.norm := norm_pos hb
    nlinarith [norm_nonneg a]
  have h2 := norm_nonneg a
  omega

private instance : EuclideanDomain HexInt :=
  { HexInt.commRing, (inferInstance : Nontrivial HexInt) with
    quotient := (· / ·)
    quotient_zero := div_zero'
    remainder := (· % ·)
    quotient_mul_add_remainder_eq := fun a b => by rw [mod_def]; ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := fun a _ hb => natAbs_norm_mod_lt a hb
    mul_left_not_lt := fun a _ hb => not_lt.mpr (natAbs_norm_le_natAbs_norm_mul a hb) }

def unitFinset : Finset HexInt :=
  {⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, -1⟩}

private theorem card_unitFinset : unitFinset.card = 6 := by decide

theorem norm_eq_one_iff_mem {z : HexInt} : z.norm = 1 ↔ z ∈ unitFinset := by
  constructor
  · intro h
    obtain ⟨a, b⟩ := z
    have hab : hexForm a b = ((1 : ℕ) : ℤ) := by exact_mod_cast h
    have hb := snd_abs_le_of_hexForm_eq hab
    have ha := snd_abs_le_of_hexForm_eq (x := b) (y := a) (by rwa [hexForm_swap])
    push_cast at ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    interval_cases a <;> interval_cases b <;> revert h <;> decide
  · intro h
    fin_cases h <;> decide

private theorem exists_nat_prime_dvd_of_dvd_natCast {π : HexInt} (hπ : Prime π) :
    ∀ k : ℕ, k ≠ 0 → π ∣ (k : HexInt) → ∃ q : ℕ, q.Prime ∧ π ∣ (q : HexInt) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk0 hπk
    rcases eq_or_ne k 1 with rfl | hk1
    · exact absurd (isUnit_of_dvd_one (by simpa using hπk)) hπ.not_isUnit
    have hkp : k.minFac.Prime := Nat.minFac_prime hk1
    have hkd : k.minFac ∣ k := Nat.minFac_dvd k
    have hsplit : (k : HexInt) = (k.minFac : HexInt) * ((k / k.minFac : ℕ) : HexInt) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hkd]
    rcases hπ.dvd_or_dvd (hsplit ▸ hπk) with h | h
    · exact ⟨k.minFac, hkp, h⟩
    · refine ih (k / k.minFac) (Nat.div_lt_self (by omega) hkp.one_lt)
        (Nat.div_pos (Nat.le_of_dvd (by omega) hkd) hkp.pos).ne' h

private theorem exists_nat_prime_dvd {π : HexInt} (hπ : Prime π) :
    ∃ q : ℕ, q.Prime ∧ π ∣ (q : HexInt) := by
  have h0 : π.norm ≠ 0 := fun h => hπ.ne_zero (norm_eq_zero_iff.mp h)
  have hnn := norm_nonneg π
  have hπk : π ∣ ((π.norm.toNat : ℕ) : HexInt) := by
    have h1 : π ∣ π * π.conj := dvd_mul_right _ _
    rw [mul_conj] at h1
    rwa [show ((π.norm.toNat : ℕ) : HexInt) = ((π.norm : ℤ) : HexInt) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]]
  exact exists_nat_prime_dvd_of_dvd_natCast hπ π.norm.toNat (by omega) hπk

private theorem norm_eq_of_prime_of_dvd {π : HexInt} (hπ : Prime π) {p : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ π.norm) : π.norm = (p : ℤ) ∨ π.norm = (p : ℤ) ^ 2 := by
  obtain ⟨q, hq, hπq⟩ := exists_nat_prime_dvd hπ

  have hnq : π.norm ∣ (q : ℤ) ^ 2 := by
    have := norm_dvd_norm hπq
    rwa [norm_natCast] at this

  have h0 : π.norm ≠ 0 := fun h => hπ.ne_zero (norm_eq_zero_iff.mp h)
  have h1 : π.norm ≠ 1 := fun h => hπ.not_isUnit (isUnit_iff_norm_eq_one.mpr h)
  have hnn := norm_nonneg π
  have hnat : π.norm.toNat ∣ q ^ 2 := by
    have : ((π.norm.toNat : ℕ) : ℤ) ∣ ((q ^ 2 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnn]; push_cast; exact hnq
    exact_mod_cast this
  obtain ⟨j, hj2, hjeq⟩ := (Nat.dvd_prime_pow hq).mp hnat

  have hpnat : p ∣ π.norm.toNat := by
    have : ((p : ℕ) : ℤ) ∣ ((π.norm.toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnn]; exact hdvd
    exact_mod_cast this
  rw [hjeq] at hpnat
  have hpq : p = q := by
    have := hp.dvd_of_dvd_pow hpnat
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp this
  subst hpq

  have hcast : π.norm = ((p ^ j : ℕ) : ℤ) := by
    rw [← hjeq, Int.toNat_of_nonneg hnn]
  interval_cases j
  ·
    exfalso
    apply h1
    simp only [pow_zero, Nat.cast_one] at hcast
    exact hcast
  · left; rw [hcast]; push_cast; ring
  · right; rw [hcast]; push_cast; ring

private theorem exists_dvd_norm_eq {γ : HexInt} (hγ : γ ≠ 0) {p : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ γ.norm) :
    ∃ δ : HexInt, δ ∣ γ ∧ (δ.norm = (p : ℤ) ∨ δ.norm = (p : ℤ) ^ 2) := by
  obtain ⟨f, hfprime, hfprod⟩ := UniqueFactorizationMonoid.exists_prime_factors γ hγ

  have hnormprod : (f.map norm).prod = γ.norm := by
    have h1 : (f.map norm).prod = (f.prod).norm := by
      rw [show (f.map norm) = f.map normHom from rfl, ← MonoidHom.map_multiset_prod]
      rfl
    rw [h1]

    obtain ⟨u, hu⟩ := hfprod
    rw [← hu, norm_mul, isUnit_iff_norm_eq_one.mp u.isUnit, mul_one]

  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨x, hxmem, hpx⟩ := hpprime.exists_mem_multiset_dvd (hnormprod ▸ hdvd)
  obtain ⟨π, hπmem, rfl⟩ := Multiset.mem_map.mp hxmem
  have hπ : Prime π := hfprime π hπmem
  refine ⟨π, ?_, norm_eq_of_prime_of_dvd hπ hp hpx⟩
  exact (Multiset.dvd_prod hπmem).trans hfprod.dvd

private theorem exists_factorization :
    ∀ m n : ℕ, Nat.Coprime m n → ∀ γ : HexInt, γ.norm = (m : ℤ) * (n : ℤ) →
      ∃ α β : HexInt, γ = α * β ∧ α.norm = (m : ℤ) ∧ β.norm = (n : ℤ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hmn γ hγ

    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · have hn1 : n = 1 := by simpa using hmn
      subst hn1
      have hγ0 : γ = 0 := norm_eq_zero_iff.mp (by simpa using hγ)
      exact ⟨0, 1, by simp [hγ0], by simp, by simp⟩
    rcases eq_or_ne m 1 with rfl | hm1
    · exact ⟨1, γ, by simp, by simp, by simpa using hγ⟩

    have hm2 : 2 ≤ m := by omega
    set p := m.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime hm1
    have hpm : p ∣ m := Nat.minFac_dvd m
    have hγ0 : γ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hγ
      rcases mul_eq_zero.mp hγ.symm with h' | h'
      · have : m = 0 := by exact_mod_cast h'
        omega
      · have hn0 : n = 0 := by exact_mod_cast h'
        rw [hn0] at hmn
        have := Nat.coprime_zero_right m |>.mp hmn
        omega
    have hpγ : (p : ℤ) ∣ γ.norm := by
      rw [hγ]
      exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpm) _
    obtain ⟨δ, hδγ, hδnorm⟩ := exists_dvd_norm_eq hγ0 hp hpγ
    obtain ⟨γ', rfl⟩ := hδγ

    rcases hδnorm with hδp | hδp
    ·
      have hlt : m / p < m := Nat.div_lt_self (by omega) hp.one_lt
      have hdvd' : m / p ∣ m := ⟨p, (Nat.div_mul_cancel hpm).symm⟩
      have hcop : Nat.Coprime (m / p) n := Nat.Coprime.coprime_dvd_left hdvd' hmn
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
      have hγ' : γ'.norm = ((m / p : ℕ) : ℤ) * (n : ℤ) := by
        have h1 : (p : ℤ) * γ'.norm = (m : ℤ) * (n : ℤ) := by
          rw [← hδp, ← norm_mul]; exact hγ
        have h2 : ((m / p : ℕ) : ℤ) * (p : ℤ) = (m : ℤ) := by
          exact_mod_cast Nat.div_mul_cancel hpm
        apply mul_left_cancel₀ hp0
        rw [h1, ← h2]; ring
      obtain ⟨α', β, rfl, hα', hβ⟩ := ih (m / p) hlt n hcop γ' hγ'
      refine ⟨δ * α', β, by ring, ?_, hβ⟩
      rw [norm_mul, hδp, hα']
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) (Nat.mul_div_cancel' hpm)
    ·
      have hsq : p ^ 2 ∣ m := by
        have h1 : ((p ^ 2 : ℕ) : ℤ) ∣ ((m * n : ℕ) : ℤ) := by
          push_cast
          rw [← hδp]
          calc δ.norm ∣ (δ * γ').norm := norm_dvd_norm (dvd_mul_right δ γ')
            _ = (m : ℤ) * (n : ℤ) := hγ
        have h2 : p ^ 2 ∣ m * n := by exact_mod_cast h1
        exact ((Nat.Coprime.coprime_dvd_left hpm hmn).pow_left 2).dvd_of_dvd_mul_right h2
      have hp2 : 1 < p ^ 2 := by nlinarith [hp.one_lt]
      have hlt : m / p ^ 2 < m := Nat.div_lt_self (by omega) hp2
      have hdvd' : m / p ^ 2 ∣ m := ⟨p ^ 2, (Nat.div_mul_cancel hsq).symm⟩
      have hcop : Nat.Coprime (m / p ^ 2) n := Nat.Coprime.coprime_dvd_left hdvd' hmn
      have hp0 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.pos.ne')
      have hγ' : γ'.norm = ((m / p ^ 2 : ℕ) : ℤ) * (n : ℤ) := by
        have h1 : (p : ℤ) ^ 2 * γ'.norm = (m : ℤ) * (n : ℤ) := by
          rw [← hδp, ← norm_mul]; exact hγ
        have h2 : ((m / p ^ 2 : ℕ) : ℤ) * ((p : ℤ)) ^ 2 = (m : ℤ) := by
          exact_mod_cast Nat.div_mul_cancel hsq
        apply mul_left_cancel₀ hp0
        rw [h1, ← h2]; ring
      obtain ⟨α', β, rfl, hα', hβ⟩ := ih (m / p ^ 2) hlt n hcop γ' hγ'
      refine ⟨δ * α', β, by ring, ?_, hβ⟩
      rw [norm_mul, hδp, hα']
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) (Nat.mul_div_cancel' hsq)

private theorem dvd_of_mul_eq_mul {α β α' β' : HexInt} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hα : α.norm = (m : ℤ)) (hβ' : β'.norm = (n : ℤ))
    (heq : α * β = α' * β') : α ∣ α' := by
  classical

  have hcop : IsCoprime α β' := by
    rw [← EuclideanDomain.gcd_isUnit_iff]
    set d := EuclideanDomain.gcd α β' with hd
    have hd1 : d.norm ∣ (m : ℤ) := hα ▸ norm_dvd_norm (EuclideanDomain.gcd_dvd_left α β')
    have hd2 : d.norm ∣ (n : ℤ) := hβ' ▸ norm_dvd_norm (EuclideanDomain.gcd_dvd_right α β')
    have hdnat1 : d.norm.natAbs ∣ m := by
      have := Int.natAbs_dvd_natAbs.mpr hd1
      simpa using this
    have hdnat2 : d.norm.natAbs ∣ n := by
      have := Int.natAbs_dvd_natAbs.mpr hd2
      simpa using this
    have hd1' : d.norm.natAbs = 1 := Nat.eq_one_of_dvd_one (hmn ▸ Nat.dvd_gcd hdnat1 hdnat2)
    refine isUnit_iff_norm_eq_one.mpr ?_
    have := norm_nonneg d
    omega

  exact hcop.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right α β)

private theorem eq_unit_mul_of_mul_eq_mul {α β α' β' : HexInt} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : m ≠ 0)
    (hα : α.norm = (m : ℤ)) (_hβ : β.norm = (n : ℤ))
    (hα' : α'.norm = (m : ℤ)) (hβ' : β'.norm = (n : ℤ))
    (heq : α' * β' = α * β) :
    ∃ u ∈ unitFinset, α' = u * α ∧ β' = u.conj * β := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  have hα0 : α ≠ 0 := fun h => hm' (by rw [← hα, h, norm_zero])

  obtain ⟨u, hu⟩ := dvd_of_mul_eq_mul hmn hα hβ' heq.symm

  have hunorm : u.norm = 1 := by
    have h3 : (m : ℤ) * u.norm = (m : ℤ) * 1 := by
      rw [mul_one]
      conv_rhs => rw [← hα', hu]
      rw [norm_mul, hα]
    exact mul_left_cancel₀ hm' h3
  have hu0 : u ≠ 0 := fun h => by simp [h] at hunorm
  have huα : α' = u * α := by rw [hu, mul_comm]
  refine ⟨u, norm_eq_one_iff_mem.mp hunorm, huα, ?_⟩

  have hcancel : (u * α) * β' = (u * α) * (u.conj * β) := by
    have h4 : (u * α) * β' = α * β := by rw [← huα]; exact heq
    rw [h4]
    calc α * β = (u * u.conj) * (α * β) := by
          rw [mul_conj, hunorm, Int.cast_one, one_mul]
      _ = (u * α) * (u.conj * β) := by ring
  exact mul_left_cancel₀ (mul_ne_zero hu0 hα0) hcancel

private def toPair (z : HexInt) : ℤ × ℤ := (z.re, z.im)

private def ofPair (p : ℤ × ℤ) : HexInt := ⟨p.1, p.2⟩

@[simp] private theorem toPair_ofPair (p : ℤ × ℤ) : toPair (ofPair p) = p := rfl

@[simp] private theorem ofPair_toPair (z : HexInt) : ofPair (toPair z) = z := rfl

private theorem toPair_injective : Function.Injective toPair := fun z w h => by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact HexInt.ext h1 h2

@[simp] private theorem norm_ofPair (p : ℤ × ℤ) : (ofPair p).norm = hexForm p.1 p.2 := rfl

private theorem mem_reprSols_iff_norm {p : ℤ × ℤ} {n : ℕ} :
    p ∈ reprSols n ↔ (ofPair p).norm = (n : ℤ) := mem_reprSols_iff

private theorem mul_mem_reprSols {m n : ℕ} {pq : (ℤ × ℤ) × (ℤ × ℤ)}
    (h : pq ∈ reprSols m ×ˢ reprSols n) :
    toPair (ofPair pq.1 * ofPair pq.2) ∈ reprSols (m * n) := by
  rw [Finset.mem_product] at h
  rw [mem_reprSols_iff_norm, ofPair_toPair, norm_mul,
    mem_reprSols_iff_norm.mp h.1, mem_reprSols_iff_norm.mp h.2]
  push_cast
  ring

private theorem card_fiber {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (_hn : n ≠ 0)
    {γp : ℤ × ℤ} (hγp : γp ∈ reprSols (m * n)) :
    ((reprSols m ×ˢ reprSols n).filter
      fun pq => toPair (ofPair pq.1 * ofPair pq.2) = γp).card = 6 := by
  classical

  have hγnorm : (ofPair γp).norm = (m : ℤ) * (n : ℤ) := by
    rw [mem_reprSols_iff_norm.mp hγp]; push_cast; ring
  obtain ⟨α₀, β₀, hγeq, hα₀, hβ₀⟩ := exists_factorization m n hmn (ofPair γp) hγnorm
  have hα₀0 : α₀ ≠ 0 := fun h => hm (by
    rw [h, norm_zero] at hα₀
    exact_mod_cast hα₀.symm)
  have hγp_pair : γp = toPair (α₀ * β₀) := by rw [← hγeq, toPair_ofPair]

  have himage : ((reprSols m ×ˢ reprSols n).filter
      fun pq => toPair (ofPair pq.1 * ofPair pq.2) = γp)
      = unitFinset.image fun u => (toPair (u * α₀), toPair (u.conj * β₀)) := by
    ext ⟨P, Q⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨hP, hQ⟩, heq⟩
      have heq' : ofPair P * ofPair Q = α₀ * β₀ := by
        rw [← hγeq]
        exact toPair_injective (by rw [heq]; rfl)
      obtain ⟨u, humem, huP, huQ⟩ :=
        eq_unit_mul_of_mul_eq_mul hmn hm
          hα₀ hβ₀ (mem_reprSols_iff_norm.mp hP) (mem_reprSols_iff_norm.mp hQ) heq'
      exact ⟨u, humem, by rw [← huP, ← huQ, toPair_ofPair, toPair_ofPair]⟩
    · rintro ⟨u, humem, heq⟩
      have hunorm : u.norm = 1 := norm_eq_one_iff_mem.mpr humem
      have hP : P = toPair (u * α₀) := (congrArg Prod.fst heq).symm
      have hQ : Q = toPair (u.conj * β₀) := (congrArg Prod.snd heq).symm
      have hconjnorm : u.conj.norm = 1 := by rw [norm_conj]; exact hunorm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hP, mem_reprSols_iff_norm, ofPair_toPair, norm_mul, hunorm, one_mul, hα₀]
      · rw [hQ, mem_reprSols_iff_norm, ofPair_toPair, norm_mul, hconjnorm, one_mul, hβ₀]
      · rw [hP, hQ, ofPair_toPair, ofPair_toPair, hγp_pair]
        congr 1
        calc u * α₀ * (u.conj * β₀) = (u * u.conj) * (α₀ * β₀) := by ring
          _ = α₀ * β₀ := by rw [mul_conj, hunorm, Int.cast_one, one_mul]

  rw [himage]
  rw [Finset.card_image_of_injOn, card_unitFinset]
  intro u _ u' _ h
  have h1 : toPair (u * α₀) = toPair (u' * α₀) := congrArg Prod.fst h
  exact mul_right_cancel₀ hα₀0 (toPair_injective h1)

theorem orbitCountMultiplicative_holds : OrbitCountMultiplicative := by
  classical
  intro m n hmn

  rcases eq_or_ne m 0 with rfl | hm
  · have hn1 : n = 1 := by simpa using hmn
    subst hn1
    simp [reprCount_zero, reprCount_one]
  rcases eq_or_ne n 0 with rfl | hn
  · have hm1 : m = 1 := by simpa using hmn
    subst hm1
    simp [reprCount_zero, reprCount_one]

  have hcount : (reprSols m ×ˢ reprSols n).card
      = ∑ γp ∈ reprSols (m * n), ((reprSols m ×ˢ reprSols n).filter
          fun pq => toPair (ofPair pq.1 * ofPair pq.2) = γp).card :=
    Finset.card_eq_sum_card_fiberwise fun pq hpq => mul_mem_reprSols hpq
  have hfibers : ∀ γp ∈ reprSols (m * n),
      ((reprSols m ×ˢ reprSols n).filter
        fun pq => toPair (ofPair pq.1 * ofPair pq.2) = γp).card = 6 :=
    fun γp hγp => card_fiber hmn hm hn hγp
  rw [Finset.sum_congr rfl hfibers, Finset.sum_const, smul_eq_mul] at hcount
  rw [Finset.card_product] at hcount
  unfold reprCount
  omega

end HexInt

end FLT.AnalyticCore

end File_FLT_AnalyticCore_OrbitCountMultiplicative

section File_FLT_AnalyticCore_CountIdentification

namespace FLT
namespace AnalyticCore

open FLT.EisensteinWeightOne

private theorem latticeSum_hexForm_eq (v : ℤ × ℤ) : LatticeSum.hexForm v = hexForm v.1 v.2 := by
  simp only [LatticeSum.hexForm, hexForm]
  ring

private theorem preimage_hexFormNat_eq_coe_reprSols (n : ℕ) :
    LatticeSum.hexFormNat ⁻¹' {n} = ↑(reprSols n) := by
  ext v
  simp only [Set.mem_preimage, Set.mem_singleton_iff, LatticeSum.hexFormNat_eq_iff,
    Finset.mem_coe, mem_reprSols_iff, latticeSum_hexForm_eq]

theorem repCount_eq_reprCount (n : ℕ) : LatticeSum.repCount n = reprCount n := by
  rw [LatticeSum.repCount, preimage_hexFormNat_eq_coe_reprSols, Set.ncard_coe_finset]
  rfl

private theorem representationCountAgrees_iff_reprCountEqCoeffE1Chi3 :
    LatticeSum.RepresentationCountAgrees ↔ ReprCountEqCoeffE1Chi3 := by
  constructor
  · intro h n
    rw [← repCount_eq_reprCount]
    exact h n
  · intro h n
    rw [repCount_eq_reprCount]
    exact h n

theorem representationCountAgrees_of_reprCountEqCoeffE1Chi3
    (h : ReprCountEqCoeffE1Chi3) : LatticeSum.RepresentationCountAgrees :=
  representationCountAgrees_iff_reprCountEqCoeffE1Chi3.mpr h

end FLT.AnalyticCore

end File_FLT_AnalyticCore_CountIdentification

section File_FLT_AnalyticCore_SplitPrimePowCount

namespace FLT
namespace AnalyticCore

open Finset

private def emul (z w : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1 + z.2 * w.2)

private theorem hexForm_emul_mk (a b : ℤ) (w : ℤ × ℤ) :
    hexForm (emul (a, b) w).1 (emul (a, b) w).2 = hexForm a b * hexForm w.1 w.2 :=
  (hexForm_mul a b w.1 w.2).symm

private theorem hexForm_conj (a b : ℤ) : hexForm (a + b) (-b) = hexForm a b := by
  simp only [hexForm]; ring

private theorem emul_assoc (z w v : ℤ × ℤ) : emul (emul z w) v = emul z (emul w v) := by
  simp only [emul, Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

private theorem emul_conj_self (a b : ℤ) : emul (a, b) (a + b, -b) = (hexForm a b, 0) := by
  simp only [emul, hexForm, Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

private theorem emul_conj_self' (a b : ℤ) : emul (a + b, -b) (a, b) = (hexForm a b, 0) := by
  simp only [emul, hexForm, Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

private theorem emul_intCast (n : ℤ) (z : ℤ × ℤ) : emul (n, 0) z = (n * z.1, n * z.2) := by
  simp only [emul, Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

private theorem ne_zero_of_hexForm_eq_prime {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hπ : hexForm a b = (p : ℤ)) : ¬(a = 0 ∧ b = 0) := by
  rintro ⟨rfl, rfl⟩
  have h0 : hexForm (0 : ℤ) 0 = 0 := by simp [hexForm]
  rw [h0] at hπ
  exact hp.ne_zero (by exact_mod_cast hπ.symm)

private theorem emul_left_cancel {a b : ℤ} (hz : ¬(a = 0 ∧ b = 0)) {w v : ℤ × ℤ}
    (h : emul (a, b) w = emul (a, b) v) : w = v := by
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  simp only [emul, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hQ : hexForm a b ≠ 0 := fun h0 => hz (hexForm_eq_zero_iff.mp h0)
  have hc : hexForm a b * (c - e) = 0 := by
    simp only [hexForm]; linear_combination (a + b) * h1 + b * h2
  have hd : hexForm a b * (d - f) = 0 := by
    simp only [hexForm]; linear_combination a * h2 - b * h1
  have hce : c = e := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h hQ
    · linarith
  have hdf : d = f := by
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd h hQ
    · linarith
  exact Prod.ext hce hdf

private theorem emul_injOn {a b : ℤ} (hz : ¬(a = 0 ∧ b = 0)) (s : Finset (ℤ × ℤ)) :
    Set.InjOn (emul (a, b)) ↑s := fun _ _ _ _ h => emul_left_cancel hz h

private theorem thue_lemma (p : ℕ) (hp : p.Prime) (t : ZMod p) :
    ∃ x y : ℤ, ¬(x = 0 ∧ y = 0) ∧ x.natAbs ≤ p.sqrt ∧ y.natAbs ≤ p.sqrt ∧
      (x : ZMod p) = t * (y : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlt : (Finset.univ : Finset (ZMod p)).card <
      (Finset.range (p.sqrt + 1) ×ˢ Finset.range (p.sqrt + 1)).card := by
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, ZMod.card]
    exact Nat.lt_succ_sqrt p
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := fun q : ℕ × ℕ => (q.1 : ZMod p) - t * (q.2 : ZMod p))
      (fun q _ => Finset.mem_univ _)
  simp only [Finset.mem_product, Finset.mem_range] at ha hb
  refine ⟨(a.1 : ℤ) - (b.1 : ℤ), (a.2 : ℤ) - (b.2 : ℤ), ?_, by omega, by omega, ?_⟩
  · rintro ⟨h1, h2⟩
    refine hab (Prod.ext ?_ ?_) <;> omega
  · have hkey : (a.1 : ZMod p) - t * (a.2 : ZMod p)
        = (b.1 : ZMod p) - t * (b.2 : ZMod p) := hfab
    push_cast
    linear_combination hkey

private theorem sqrt_mul_self_lt_of_prime {p : ℕ} (hp : p.Prime) : p.sqrt * p.sqrt < p := by
  rcases lt_or_eq_of_le (Nat.sqrt_le p) with h | h
  · exact h
  · exfalso
    rcases hp.eq_one_or_self_of_dvd p.sqrt ⟨p.sqrt, h.symm⟩ with h1 | h1
    · rw [h1, one_mul] at h
      exact hp.one_lt.ne h
    · rw [h1] at h
      have h2 := hp.two_le
      nlinarith

private theorem exists_hexForm_eq_prime {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ x y : ℤ, hexForm x y = (p : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by omega
  obtain ⟨t, ht3⟩ := ModularCurve.exists_orderOf_eq_three hp h1
  have htroot : t ^ 2 + t + 1 = 0 :=
    (ModularCurve.sq_add_self_add_one_eq_zero_iff_orderOf_eq_three hp hp3 t).mpr ht3
  obtain ⟨x, y, hxy0, hxabs, hyabs, hcong⟩ := thue_lemma p hp t

  have hdvd : (p : ℤ) ∣ hexForm x y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [hexForm]
    linear_combination ((x : ZMod p) + t * (y : ZMod p) + (y : ZMod p)) * hcong +
      (y : ZMod p) ^ 2 * htroot

  have hpos : 0 < hexForm x y := by
    rcases (hexForm_nonneg x y).lt_or_eq with h | h
    · exact h
    · exact absurd (hexForm_eq_zero_iff.mp h.symm) hxy0

  have hsq : (p.sqrt : ℤ) * (p.sqrt : ℤ) < (p : ℤ) := by
    exact_mod_cast sqrt_mul_self_lt_of_prime hp
  have hb1 : (0 : ℤ) ≤ ((p.sqrt : ℤ) - x) * ((p.sqrt : ℤ) + x) :=
    mul_nonneg (by omega) (by omega)
  have hb2 : (0 : ℤ) ≤ ((p.sqrt : ℤ) - y) * ((p.sqrt : ℤ) + y) :=
    mul_nonneg (by omega) (by omega)
  have hb3 : (0 : ℤ) ≤ ((p.sqrt : ℤ) - x) * ((p.sqrt : ℤ) + y) :=
    mul_nonneg (by omega) (by omega)
  have hb4 : (0 : ℤ) ≤ ((p.sqrt : ℤ) + x) * ((p.sqrt : ℤ) - y) :=
    mul_nonneg (by omega) (by omega)
  have hlt : hexForm x y < 3 * (p : ℤ) := by
    simp only [hexForm]
    nlinarith

  obtain ⟨m, hm⟩ := hdvd
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hm1 : 0 < m := by
    rcases lt_trichotomy m 0 with h | h | h
    · nlinarith [mul_neg_of_pos_of_neg hppos h]
    · subst h
      rw [mul_zero] at hm
      omega
    · exact h
  have hm2 : m < 3 := by
    have hmm : (p : ℤ) * m < (p : ℤ) * 3 := by linarith
    exact lt_of_mul_lt_mul_left hmm (le_of_lt hppos)
  interval_cases m
  · exact ⟨x, y, by linarith⟩
  ·

    exfalso
    have h2d : ((2 : ℕ) : ℤ) ∣ hexForm x y := ⟨(p : ℤ), by push_cast; linarith⟩
    obtain ⟨hx2, hy2⟩ := inert_dvd_of_dvd_hexForm Nat.prime_two (by norm_num) h2d
    obtain ⟨x', rfl⟩ := hx2
    obtain ⟨y', rfl⟩ := hy2
    rw [hexForm_smul] at hm
    have h2p : ((2 : ℕ) : ℤ) ∣ (p : ℤ) := by
      refine ⟨hexForm x' y', ?_⟩
      push_cast at hm ⊢
      nlinarith [hm]
    have hpeq : p = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (by exact_mod_cast h2p)).symm
    omega

private theorem dvd_fst_of_dvd_snd_of_sq_dvd_hexForm {p : ℕ} (hp : p.Prime) {S T : ℤ}
    (hN : ((p : ℤ)) ^ 2 ∣ hexForm S T) (hT : (p : ℤ) ∣ T) : (p : ℤ) ∣ S := by
  have h1 : (p : ℤ) ∣ S * S := by
    have hrw : S * S = hexForm S T - S * T - T * T := by simp only [hexForm]; ring
    rw [hrw]
    exact dvd_sub (dvd_sub ((dvd_pow_self _ two_ne_zero).trans hN) (hT.mul_left S))
      (hT.mul_left T)
  rcases Int.Prime.dvd_mul' hp h1 with h | h <;> exact h

private theorem exists_eq_emul_conj_of_dvd {p : ℕ} (hp : p.Prime) {a b : ℤ} {z : ℤ × ℤ}
    (hπ : hexForm a b = (p : ℤ))
    (hS : (p : ℤ) ∣ (emul (a, b) z).1) (hT : (p : ℤ) ∣ (emul (a, b) z).2) :
    ∃ v : ℤ × ℤ, z = emul (a + b, -b) v ∧
      (p : ℤ) * hexForm v.1 v.2 = hexForm z.1 z.2 := by
  obtain ⟨c, hc⟩ := hS
  obtain ⟨d, hd⟩ := hT
  have hw0 : ¬(a = 0 ∧ b = 0) := ne_zero_of_hexForm_eq_prime hp hπ
  have hkey : emul (a, b) (emul (a + b, -b) (c, d)) = emul (a, b) z := by
    rw [← emul_assoc, emul_conj_self, hπ, emul_intCast]
    exact (Prod.ext hc hd).symm
  have hz : z = emul (a + b, -b) (c, d) := (emul_left_cancel hw0 hkey).symm
  refine ⟨(c, d), hz, ?_⟩
  rw [hz, hexForm_emul_mk, hexForm_conj, hπ]

private theorem exists_emul_of_dvd_hexForm {p : ℕ} (hp : p.Prime) {a b x y : ℤ}
    (hπ : hexForm a b = (p : ℤ)) (hz : (p : ℤ) ∣ hexForm x y) :
    (∃ v : ℤ × ℤ, (x, y) = emul (a, b) v ∧
        (p : ℤ) * hexForm v.1 v.2 = hexForm x y) ∨
    (∃ v : ℤ × ℤ, (x, y) = emul (a + b, -b) v ∧
        (p : ℤ) * hexForm v.1 v.2 = hexForm x y) := by
  have hπ' : hexForm (a + b) (-b) = (p : ℤ) := (hexForm_conj a b).trans hπ
  obtain ⟨m, hm⟩ := hz

  have htt : (p : ℤ) ∣ (emul (a + b, -b) (x, y)).2 * (emul (a, b) (x, y)).2 := by
    refine ⟨y ^ 2 - b ^ 2 * m, ?_⟩
    have hrw : (emul (a + b, -b) (x, y)).2 * (emul (a, b) (x, y)).2
        = y ^ 2 * hexForm a b - b ^ 2 * hexForm x y := by
      simp only [emul, hexForm]; ring
    rw [hrw, hπ, hm]
    ring

  have hN1 : ((p : ℤ)) ^ 2 ∣
      hexForm (emul (a + b, -b) (x, y)).1 (emul (a + b, -b) (x, y)).2 := by
    rw [hexForm_emul_mk]
    refine ⟨m, ?_⟩
    have hxy : hexForm ((x : ℤ), (y : ℤ)).1 ((x : ℤ), (y : ℤ)).2 = hexForm x y := rfl
    rw [hxy, hπ', hm]
    ring
  have hN2 : ((p : ℤ)) ^ 2 ∣ hexForm (emul (a, b) (x, y)).1 (emul (a, b) (x, y)).2 := by
    rw [hexForm_emul_mk]
    refine ⟨m, ?_⟩
    have hxy : hexForm ((x : ℤ), (y : ℤ)).1 ((x : ℤ), (y : ℤ)).2 = hexForm x y := rfl
    rw [hxy, hπ, hm]
    ring
  rcases Int.Prime.dvd_mul' hp htt with hT | hT
  ·
    left
    have hS := dvd_fst_of_dvd_snd_of_sq_dvd_hexForm hp hN1 hT
    obtain ⟨v, hv, hnorm⟩ := exists_eq_emul_conj_of_dvd hp hπ' hS hT
    have hconv : ((a + b) + -b, -(-b)) = ((a : ℤ), (b : ℤ)) := by
      simp only [Prod.mk.injEq]
      exact ⟨by ring, by ring⟩
    rw [hconv] at hv
    exact ⟨v, hv, hnorm⟩
  ·
    right
    have hS := dvd_fst_of_dvd_snd_of_sq_dvd_hexForm hp hN2 hT
    obtain ⟨v, hv, hnorm⟩ := exists_eq_emul_conj_of_dvd hp hπ hS hT
    exact ⟨v, hv, hnorm⟩

private theorem dvd_of_dvd_lin {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) {a b x y : ℤ}
    (hπ : hexForm a b = (p : ℤ))
    (hT : (p : ℤ) ∣ a * y - b * x) (hT' : (p : ℤ) ∣ a * y + b * x + b * y) :
    (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hp4 : 4 ≤ p := by
    have h2 := hp.two_le
    omega
  have hp4' : (4 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp4

  have hpb : ¬ (p : ℤ) ∣ b := by
    intro hb
    have ha2 : (p : ℤ) ∣ a * a := by
      have hrw : a * a = hexForm a b - b * (a + b) := by simp only [hexForm]; ring
      rw [hrw, hπ]
      exact dvd_sub (dvd_refl _) (hb.mul_right _)
    have ha : (p : ℤ) ∣ a := by
      rcases Int.Prime.dvd_mul' hp ha2 with h | h <;> exact h
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [hexForm_smul] at hπ

    have hppos : (0 : ℤ) < (p : ℤ) := by linarith
    have hcancel : (p : ℤ) * ((p : ℤ) * hexForm a' b') = (p : ℤ) * 1 := by
      linear_combination hπ
    have hone : (p : ℤ) * hexForm a' b' = 1 :=
      mul_left_cancel₀ hppos.ne' hcancel
    have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨hexForm a' b', hone.symm⟩
    linarith

  have h2xy : (p : ℤ) ∣ b * (2 * x + y) := by
    have hrw : b * (2 * x + y) = (a * y + b * x + b * y) - (a * y - b * x) := by ring
    rw [hrw]
    exact dvd_sub hT' hT
  have hy2ab : (p : ℤ) ∣ y * (2 * a + b) := by
    have hrw : y * (2 * a + b) = (a * y + b * x + b * y) + (a * y - b * x) := by ring
    rw [hrw]
    exact dvd_add hT' hT

  have h2x : (p : ℤ) ∣ 2 * x + y := by
    rcases Int.Prime.dvd_mul' hp h2xy with h | h
    · exact absurd h hpb
    · exact h

  have hy : (p : ℤ) ∣ y := by
    rcases Int.Prime.dvd_mul' hp hy2ab with h | h
    · exact h
    · exfalso
      have h4 : (2 * a + b) ^ 2 + 3 * b ^ 2 = 4 * (p : ℤ) := by
        rw [← four_mul_hexForm, hπ]
      have h3b : (p : ℤ) ∣ 3 * (b * b) := by
        have hrw : 3 * (b * b) = 4 * (p : ℤ) - (2 * a + b) * (2 * a + b) := by
          linear_combination h4
        rw [hrw]
        exact dvd_sub ((dvd_refl _).mul_left 4) (h.mul_left _)
      rcases Int.Prime.dvd_mul' hp h3b with h3 | hbb
      · have hle : (p : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) h3
        linarith
      · rcases Int.Prime.dvd_mul' hp hbb with h | h <;> exact hpb h

  refine ⟨?_, hy⟩
  have h2x' : (p : ℤ) ∣ 2 * x := by
    have hrw : 2 * x = (2 * x + y) - y := by ring
    rw [hrw]
    exact dvd_sub h2x hy
  rcases Int.Prime.dvd_mul' hp h2x' with h | h
  · exfalso
    have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
    linarith
  · exact h

private theorem dvd_of_emul_eq_of_emul_eq {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) {a b x y : ℤ}
    (hπ : hexForm a b = (p : ℤ)) {w1 w2 : ℤ × ℤ}
    (he1 : emul (a, b) w1 = (x, y)) (he2 : emul (a + b, -b) w2 = (x, y)) :
    (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  apply dvd_of_dvd_lin hp h1 hπ
  ·
    have hchain : emul (a + b, -b) ((x : ℤ), (y : ℤ))
        = ((p : ℤ) * w1.1, (p : ℤ) * w1.2) := by
      rw [← he1, ← emul_assoc, emul_conj_self', hπ, emul_intCast]
    have h2 : (emul (a + b, -b) ((x : ℤ), (y : ℤ))).2 = (p : ℤ) * w1.2 := by
      rw [hchain]
    refine ⟨w1.2, ?_⟩
    have h2' : (a + b) * y + -b * x + -b * y = (p : ℤ) * w1.2 := h2
    linear_combination h2'
  ·
    have hchain : emul (a, b) ((x : ℤ), (y : ℤ)) = ((p : ℤ) * w2.1, (p : ℤ) * w2.2) := by
      rw [← he2, ← emul_assoc, emul_conj_self, hπ, emul_intCast]
    have h2 : (emul (a, b) ((x : ℤ), (y : ℤ))).2 = (p : ℤ) * w2.2 := by
      rw [hchain]
    refine ⟨w2.2, ?_⟩
    have h2' : a * y + b * x + b * y = (p : ℤ) * w2.2 := h2
    linear_combination h2'

private theorem emul_mem_reprSols {p : ℕ} {a b : ℤ} (hπ : hexForm a b = (p : ℤ)) {n : ℕ}
    {w : ℤ × ℤ} (hw : w ∈ reprSols n) : emul (a, b) w ∈ reprSols (p * n) := by
  rw [mem_reprSols_iff, hexForm_emul_mk, hπ, mem_reprSols_iff.mp hw, Nat.cast_mul]

private theorem reprSols_mul_eq_union {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hπ : hexForm a b = (p : ℤ)) (n : ℕ) :
    reprSols (p * n) =
      (reprSols n).image (emul (a, b)) ∪ (reprSols n).image (emul (a + b, -b)) := by
  have hπ' : hexForm (a + b) (-b) = (p : ℤ) := (hexForm_conj a b).trans hπ
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  ext q
  constructor
  · intro hq
    obtain ⟨x, y⟩ := q
    have hQ : hexForm x y = ((p * n : ℕ) : ℤ) := mem_reprSols_iff.mp hq
    have hdvd : (p : ℤ) ∣ hexForm x y := by
      rw [hQ, Nat.cast_mul]
      exact dvd_mul_right _ _
    rcases exists_emul_of_dvd_hexForm hp hπ hdvd with ⟨v, hv, hnorm⟩ | ⟨v, hv, hnorm⟩
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, ?_, hv.symm⟩)
      rw [mem_reprSols_iff]
      apply mul_left_cancel₀ hp0
      rw [hnorm, hQ, Nat.cast_mul]
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, ?_, hv.symm⟩)
      rw [mem_reprSols_iff]
      apply mul_left_cancel₀ hp0
      rw [hnorm, hQ, Nat.cast_mul]
  · intro hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      exact emul_mem_reprSols hπ hw
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      exact emul_mem_reprSols hπ' hw

private theorem inter_image_one_eq_empty {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) {a b : ℤ}
    (hπ : hexForm a b = (p : ℤ)) :
    (reprSols 1).image (emul (a, b)) ∩ (reprSols 1).image (emul (a + b, -b)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨x, y⟩ hq
  rw [Finset.mem_inter] at hq
  obtain ⟨w1, hw1, he1⟩ := Finset.mem_image.mp hq.1
  obtain ⟨w2, hw2, he2⟩ := Finset.mem_image.mp hq.2
  obtain ⟨hx, hy⟩ := dvd_of_emul_eq_of_emul_eq hp h1 hπ he1 he2

  have hmem : ((x : ℤ), (y : ℤ)) ∈ reprSols (p * 1) := by
    rw [← he1]
    exact emul_mem_reprSols hπ hw1
  have hQ : hexForm x y = ((p * 1 : ℕ) : ℤ) := mem_reprSols_iff.mp hmem
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  rw [hexForm_smul] at hQ

  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hcancel : (p : ℤ) * ((p : ℤ) * hexForm x' y') = (p : ℤ) * 1 := by
    rw [Nat.mul_one] at hQ
    linear_combination hQ
  have hone : (p : ℤ) * hexForm x' y' = 1 := mul_left_cancel₀ hppos.ne' hcancel
  have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨hexForm x' y', hone.symm⟩
  have hgt := hp.one_lt
  have hgt' : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hgt
  linarith

private theorem inter_image_eq_dilate {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) {a b : ℤ}
    (hπ : hexForm a b = (p : ℤ)) (m : ℕ) :
    (reprSols (p * m)).image (emul (a, b)) ∩
        (reprSols (p * m)).image (emul (a + b, -b))
      = (reprSols m).image (fun w : ℤ × ℤ => ((p : ℤ) * w.1, (p : ℤ) * w.2)) := by
  have hπ' : hexForm (a + b) (-b) = (p : ℤ) := (hexForm_conj a b).trans hπ
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  ext q
  simp only [Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w1, hw1, he1⟩, ⟨w2, hw2, he2⟩⟩
    obtain ⟨x, y⟩ := q
    obtain ⟨hx, hy⟩ := dvd_of_emul_eq_of_emul_eq hp h1 hπ he1 he2
    have hmem : ((x : ℤ), (y : ℤ)) ∈ reprSols (p * (p * m)) := by
      rw [← he1]
      exact emul_mem_reprSols hπ hw1
    have hQ : hexForm x y = ((p * (p * m) : ℕ) : ℤ) := mem_reprSols_iff.mp hmem
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    refine ⟨(x', y'), ?_, rfl⟩
    rw [mem_reprSols_iff]
    rw [hexForm_smul] at hQ
    have hcancel : (p : ℤ) ^ 2 * hexForm x' y' = (p : ℤ) ^ 2 * (m : ℤ) := by
      push_cast at hQ
      linear_combination hQ
    exact mul_left_cancel₀ (pow_ne_zero 2 hp0) hcancel
  · rintro ⟨w, hw, heq⟩
    obtain ⟨c, d⟩ := w
    refine ⟨⟨emul (a + b, -b) (c, d), emul_mem_reprSols hπ' hw, ?_⟩,
      ⟨emul (a, b) (c, d), emul_mem_reprSols hπ hw, ?_⟩⟩
    · rw [← emul_assoc, emul_conj_self, hπ, emul_intCast]
      exact heq
    · rw [← emul_assoc, emul_conj_self', hπ, emul_intCast]
      exact heq

private theorem card_image_emul {p : ℕ} (hp : p.Prime) {a b : ℤ} (hπ : hexForm a b = (p : ℤ))
    (s : Finset (ℤ × ℤ)) : (s.image (emul (a, b))).card = s.card :=
  Finset.card_image_of_injOn (emul_injOn (ne_zero_of_hexForm_eq_prime hp hπ) s)

private theorem card_image_dilate {p : ℕ} (hp : p.Prime) (s : Finset (ℤ × ℤ)) :
    (s.image (fun w : ℤ × ℤ => ((p : ℤ) * w.1, (p : ℤ) * w.2))).card = s.card := by
  apply Finset.card_image_of_injOn
  intro w1 _ w2 _ h
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (mul_left_cancel₀ hp0 h.1) (mul_left_cancel₀ hp0 h.2)

private theorem reprCount_eq_twelve_of_split {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    reprCount p = 12 := by
  obtain ⟨a, b, hπ⟩ := exists_hexForm_eq_prime hp h1
  have hπ' : hexForm (a + b) (-b) = (p : ℤ) := (hexForm_conj a b).trans hπ
  have hcui := Finset.card_union_add_card_inter ((reprSols 1).image (emul (a, b)))
    ((reprSols 1).image (emul (a + b, -b)))
  rw [inter_image_one_eq_empty hp h1 hπ, Finset.card_empty, card_image_emul hp hπ,
    card_image_emul hp hπ'] at hcui
  have hone : (reprSols 1).card = 6 := reprCount_one
  have hgoal : reprCount (p * 1) = 12 := by
    show (reprSols (p * 1)).card = 12
    rw [reprSols_mul_eq_union hp hπ 1]
    omega
  simpa using hgoal

private theorem reprCount_mul_mul {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) {a b : ℤ}
    (hπ : hexForm a b = (p : ℤ)) (m : ℕ) :
    reprCount (p * (p * m)) + reprCount m = 2 * reprCount (p * m) := by
  have hπ' : hexForm (a + b) (-b) = (p : ℤ) := (hexForm_conj a b).trans hπ
  have hcui := Finset.card_union_add_card_inter
    ((reprSols (p * m)).image (emul (a, b)))
    ((reprSols (p * m)).image (emul (a + b, -b)))
  rw [inter_image_eq_dilate hp h1 hπ m, card_image_dilate hp, card_image_emul hp hπ,
    card_image_emul hp hπ'] at hcui
  show (reprSols (p * (p * m))).card + (reprSols m).card = 2 * (reprSols (p * m)).card
  rw [reprSols_mul_eq_union hp hπ (p * m)]
  omega

private theorem splitPrimePowCount : SplitPrimePowCount := by
  intro p k hp h1
  obtain ⟨a, b, hπ⟩ := exists_hexForm_eq_prime hp h1
  suffices h : ∀ j : ℕ, reprCount (p ^ j) = 6 * (j + 1) ∧
      reprCount (p ^ (j + 1)) = 6 * (j + 1 + 1) from (h k).1
  intro j
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa using reprCount_one
    · simpa using reprCount_eq_twelve_of_split hp h1
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have hrec := reprCount_mul_mul hp h1 hπ (p ^ j)
    rw [show p * (p * p ^ j) = p ^ (j + 1 + 1) by ring,
      show p * p ^ j = p ^ (j + 1) by ring] at hrec
    omega

private theorem reprCountEqCoeffE1Chi3 : ReprCountEqCoeffE1Chi3 :=
  reprCountEqCoeffE1Chi3_of_residuals HexInt.orbitCountMultiplicative_holds
    splitPrimePowCount

end FLT.AnalyticCore

end File_FLT_AnalyticCore_SplitPrimePowCount

section File_FLT_AnalyticCore_E1Chi3Modular

open Complex Real CongruenceSubgroup
open FLT.AnalyticCore.LatticeSum FLT.EisensteinWeightOne
open scoped UpperHalfPlane

namespace FLT
namespace AnalyticCore

noncomputable section

theorem representationCountAgrees : RepresentationCountAgrees :=
  representationCountAgrees_of_reprCountEqCoeffE1Chi3 reprCountEqCoeffE1Chi3

theorem e1Chi3IsModular : E1Chi3IsModular :=
  e1Chi3IsModular_of_repCount representationCountAgrees

/-! ### The theta form on `Γ₁(3)` and its Fricke involution

The residual of the pinned `S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean`.
Everything else in that `S_` file is the theta/lattice-sum development already here (or in
`Analysis/Theta/HexagonalLattice.lean`), so only these declarations are new. -/

open Matrix Subgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

private def thetaForm : ModularForm (Gamma1 3) 1 :=
  { slashInvariantForm_of_T_U hexThetaH hexThetaH_slash_T hexThetaH_slash_U with
    holo' := mdifferentiable_hexThetaH
    bdd_at_cusps' := fun {c} hc => hexThetaH_isBoundedAt_cusp c hc }

@[simp] private lemma coe_thetaForm : (⇑thetaForm : ℍ → ℂ) = hexThetaH := rfl

private lemma one_mem_strictPeriods_Gamma1_three :
    (1 : ℝ) ∈ ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

private lemma qExpansion_coeff_thetaForm (n : ℕ) :
    (qExpansion 1 (⇑thetaForm : ℍ → ℂ)).coeff n = (repCount n : ℂ) := by
  symm
  refine ModularFormClass.qExpansion_coeff_unique (c := fun n => (repCount n : ℂ)) one_pos
    one_mem_strictPeriods_Gamma1_three (f := thetaForm) (fun τ => ?_) n
  have hτ : 0 < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ.im_pos
  have h := hasSum_repCount_qpow hτ
  rw [coe_thetaForm, hexThetaH_apply]
  convert h using 1
  funext m
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring_nf

private lemma thetaForm_slash_fricke (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 3, 0]) :
    (⇑thetaForm : ℍ → ℂ) ∣[(1 : ℤ)] W = (-Complex.I / (Real.sqrt 3 : ℂ)) • (⇑thetaForm : ℍ → ℂ) := by
  funext τ
  have hdet : (W.det : ℝ) = 3 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hW, Matrix.det_fin_two_of]
    norm_num
  have hdetpos : 0 < (W.det : ℝ) := by rw [hdet]; norm_num
  have hτ : 0 < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ.im_pos
  have hτ0 : (τ : ℂ) ≠ 0 := ne_zero_of_im_pos hτ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hσ : σ W = ContinuousAlgEquiv.refl ℝ ℂ := by rw [σ, ite_eq_left hdetpos]
  have hsm : ((W • τ : ℍ) : ℂ) = -1 / (3 * (τ : ℂ)) := by
    rw [coe_smul_of_det_pos hdetpos]
    simp [num, denom, hW]
  have hden : denom W τ = 3 * (τ : ℂ) := by simp [denom, hW]
  rw [hσ, ContinuousAlgEquiv.refl_apply, hdet, coe_thetaForm, hexThetaH_eq_hexTheta,
    hexThetaH_eq_hexTheta, hsm, hexTheta_fricke hτ, hden]
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := sqrt_three_ne_zero
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    rfl
  rw [sub_self, zpow_zero, mul_one, _root_.zpow_neg, zpow_one]
  field_simp
  linear_combination (-hexTheta (τ : ℂ)) * hs3

end

end FLT.AnalyticCore

end File_FLT_AnalyticCore_E1Chi3Modular

/-- **SET-6 order 2.** The weight-one `χ₋₃` Eisenstein series `e1Chi3` is the
`q`-expansion of a modular form on `Γ₁(3)`. -/
theorem EisensteinWeightOne.e1Chi3IsModular : EisensteinWeightOne.E1Chi3IsModular :=
  FLT.AnalyticCore.e1Chi3IsModular

/-- **The `q`-series of `e1Chi3` is the `A₂` theta series.** Stated verbatim from
`Theorems/Thm_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.lean`.

No `S_` text is transcribed for this headline. `latticeSum` is already both the `e1Chi3`
`q`-series (`latticeSum_eq_e1Chi3_qSeries`, applied at the half-plane point `⟨σ, hσ⟩`) and the
hexagonal theta series (`latticeSum_eq_hexTheta`); the identity is those two halves composed. -/
theorem EisensteinWeightOne.tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal (σ : ℂ) (hσ : 0 < σ.im) :
    (∑' n : ℕ, ((PowerSeries.coeff n EisensteinWeightOne.e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * σ)) =
      ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) := by
  rw [← FLT.AnalyticCore.LatticeSum.latticeSum_eq_e1Chi3_qSeries
        FLT.AnalyticCore.representationCountAgrees ⟨σ, hσ⟩,
      FLT.AnalyticCore.latticeSum_eq_hexTheta]
  rfl

open scoped MatrixGroups ModularForm

/-- **A weight-one form on `Γ₁(3)` with the Fricke involution.** Stated verbatim from
`Theorems/Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean`; the
theta/lattice-sum development of that `S_` file is already in this module, so only this
packaging is added. -/
theorem ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)) 1,
      (∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 g).coeff n = (r : ℂ)) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ W : GL (Fin 2) ℝ, (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 3, 0] →
        (⇑g : UpperHalfPlane → ℂ) ∣[(1 : ℤ)] W =
          (-Complex.I / (Real.sqrt 3 : ℂ)) • (⇑g : UpperHalfPlane → ℂ) := by
  refine ⟨FLT.AnalyticCore.thetaForm,
    fun n => ⟨(FLT.AnalyticCore.LatticeSum.repCount n : ℚ), ?_⟩, ?_,
    fun W hW => FLT.AnalyticCore.thetaForm_slash_fricke W hW⟩
  · rw [FLT.AnalyticCore.qExpansion_coeff_thetaForm]
    push_cast
    rfl
  · rw [FLT.AnalyticCore.qExpansion_coeff_thetaForm,
      FLT.AnalyticCore.LatticeSum.repCount_zero]
    push_cast
    rfl
