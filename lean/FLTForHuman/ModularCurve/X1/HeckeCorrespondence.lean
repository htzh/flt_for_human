/-
MC-7c — the β/α Hecke correspondence at `ℓ ∤ M`.

`coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd`: the
correspondence `traceAlong β ∘ pullbackAlong α` on `Ω[x1FunctionFieldBar M / Qb]` acts
on `q`-coefficients by

    coeff n  ↦  coeff (n * ℓ)  +  ℓ · (if ℓ ∣ n then twisted coeff (n / ℓ) else 0),

where the second term is the diamond twist `diamondAutBar M ℓ` read through the
Atkin–Lehner exchange `W`. The computation is the trace over the `ℓ` embeddings of the
β-extension (`emb`), and the coefficient identity is the root-of-unity sum over them
(`rootSum`, `sum_zpow_pow`).

Proof transcribed from FLT's `S_` file at the pin `aa2d8b3`; the statement is the
`Theorems/` wrapper's, its binder block verbatim. The pin's `namespace R1G1H1` is a
search label and is not transcribed; its `set_option synthInstance.maxHeartbeats 1600000`
and `set_option maxHeartbeats 3200000` are not transcribed either, and no declaration
here carries `set_option maxHeartbeats`.

Already in the port and imported rather than restated (the checker diffs statements, and
these have the port's binder shapes): the pin's `twistFun` is `ModularCurve.qTwistFun`
(`Defs/Twist.lean`); `P4`/`P6`/`xq`/`xq_mem`/`constantCoeff_P4`/`_P6`/`coeff_one_P4`/
`_P6`/`intSeriesC_ne_zero_of_constantCoeff` are `ModularCurve.RelrankSol`'s
(`XH/Relrank.lean`); `coeffEmb_intSeriesC` is `ModularCurve`'s
(`JqIntegralRatios.lean`); `A12`/`B12`/`isIntegralQExp_A12`/`_B12` are
`JOneES.JOneESRat`'s (`X1/FunctionField.lean`) and are needed only inside the imported
`xq_mem`. The pin's `AutTrace` block is proved twice, once per `S_` file; the port proves
it once, in `AlgebraicCurve/Differential/AutTrace.lean`, which this module imports (no
copy is kept here). `emb_injective` is kept in this module's own namespace, where it does
not collide with `AutomorphicForm.IwasawaWeyl.emb_injective`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.lean

spec-pin: Theorems/Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.lean
spec-pin: P2M/Sol/S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.lean
-/
import FLTForHuman.ModularCurve.X1.HeckeDegree
import FLTForHuman.ModularCurve.X1.AtkinLehnerExchange
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.Defs.HeckeDifferential
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.Differential.AutTrace
import FLTForHuman.AlgebraicCurve.Differential.TraceDiff
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.ModularCurve.XH.Relrank

set_option autoImplicit false

noncomputable section

open ModularCurve HahnSeries KaehlerDifferential AlgebraicCurve AlgebraicCurve.Differential

open ModularCurve.RelrankSol (P4 P6 constantCoeff_P4 constantCoeff_P6 coeff_one_P4
  coeff_one_P6 intSeriesC_ne_zero_of_constantCoeff xq xq_mem)

namespace ModularCurve.X1HeckeCorrespondence

section Twist

variable {R : Type*} [Field R]

/-- The coefficient twist `q ↦ c q` packaged as an `R`-algebra endomorphism of Laurent
series. The pin's `twistFun` is the port's `ModularCurve.qTwistFun`, so the underlying
function is the ported one. -/
def twist (c : Rˣ) : LaurentSeries R →ₐ[R] LaurentSeries R :=
  { qTwist c with
    commutes' := by
      intro r
      rw [algebraMap_laurentSeries_eq_single]
      show qTwist c (single 0 r) = single 0 r
      rw [qTwist_single]; simp }

@[scoped simp] theorem twist_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twist c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem twist_qExpand_of_pow_eq_one (c : Rˣ) (m : ℕ) [NeZero m] (hc : c ^ m = 1)
    (z : LaurentSeries R) : twist c (qExpand R m z) = qExpand R m z := by
  ext n
  rw [twist_coeff]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [zpow_mul, zpow_natCast, hc, one_zpow, Units.val_one, one_mul]
  · rw [qExpand_coeff_of_not_dvd m _ h, mul_zero]

end Twist

section Euler

variable {R : Type*} [CommRing R]

theorem qEuler_qExpand (m : ℕ) [NeZero m] (x : LaurentSeries R) :
    qEuler R (qExpand R m x) = C (m : R) * qExpand R m (qEuler R x) := by
  ext n
  rw [qEuler_coeff, C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, qEuler_coeff]
    push_cast
    ring
  · rw [qExpand_coeff_of_not_dvd m _ h, qExpand_coeff_of_not_dvd m _ h, mul_zero, mul_zero]

end Euler

section Pull

variable {L : Type*} [Field L]

theorem diffQExp_pullbackAlong (F₁ F₂ : IntermediateField L (LaurentSeries L))
    (φ : F₁ →ₐ[L] F₂) (ρ : LaurentSeries L →+* LaurentSeries L) (c : L)
    (hφ : ∀ x : F₁, ((φ x : F₂) : LaurentSeries L) = ρ x)
    (hρ : ∀ y, qEuler L (ρ y) = C c * ρ (qEuler L y)) (η : Ω[F₁⁄L]) :
    diffQExp F₂ (pullbackAlong φ η) = C c * ρ (diffQExp F₁ η) := by
  have key : ∀ η : Ω[F₁⁄L], η ∈ Submodule.span F₁ (Set.range (D L F₁)) → ∀ f : F₁,
      diffQExp F₂ (pullbackAlong φ (f • η)) = C c * ρ (diffQExp F₁ (f • η)) := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem η h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      rw [pullbackAlong_smul, pullbackAlong_D, diffQExp_smul_D, diffQExp_smul_D, hφ, hφ, hρ,
        map_mul, mul_left_comm]
    | zero => intro f; simp
    | add x y _ _ hx hy =>
      intro f
      rw [smul_add, map_add, map_add, hx, hy, map_add, map_add, mul_add]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key η (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

-- `pullbackAlong_pullbackAlong` is not re-declared here: the port already has it, in
-- `AlgebraicCurve/Differential/PushPull.lean` (`TraceAtPoints.pullbackAlong_pullbackAlong`,
-- the same statement modulo binder order). The proofs below use that one directly, under its
-- qualified name.

theorem diffQExp_smul (F : IntermediateField L (LaurentSeries L)) (u : F) (ξ : Ω[F⁄L]) :
    diffQExp F (u • ξ) = (u : LaurentSeries L) * diffQExp F ξ := by
  rw [map_smul]; rfl

end Pull

/-! The pin's `AutTrace` block — `pullbackAlong_id`, `separableAlong_algEquiv`,
`trace_one_along_algEquiv`, `traceAlong_algEquiv`, `correspondence_algEquiv_id` — is *shared*
with the 934 row (the pin proves it twice, once per `S_` file). The port proves it once, in
`AlgebraicCurve/Differential/AutTrace.lean` (namespace `AlgebraicCurve.Differential`), which
this module imports; nothing of it is copied here. -/

section RootSum

variable {R : Type*} [Field R]

theorem twist_C (c : Rˣ) (r : R) : twist c (C r) = C r := by
  show qTwist c (single 0 r) = single 0 r
  rw [qTwist_single]; simp

def rootSum (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) : LaurentSeries R :=
  ∑ j ∈ Finset.range ℓ, twist (u ^ j) x

theorem rootSum_apply (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) :
    rootSum u ℓ x = ∑ j ∈ Finset.range ℓ, twist (u ^ j) x := rfl

theorem rootSum_add (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R) :
    rootSum u ℓ (x + y) = rootSum u ℓ x + rootSum u ℓ y := by
  simp only [rootSum, map_add, Finset.sum_add_distrib]

theorem rootSum_zero (u : Rˣ) (ℓ : ℕ) : rootSum u ℓ (0 : LaurentSeries R) = 0 := by
  simp only [rootSum, map_zero, Finset.sum_const_zero]

theorem rootSum_C_mul (u : Rˣ) (ℓ : ℕ) (r : R) (x : LaurentSeries R) :
    rootSum u ℓ (C r * x) = C r * rootSum u ℓ x := by
  simp only [rootSum, map_mul, twist_C, Finset.mul_sum]

theorem rootSum_mul_of_fixed (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R)
    (hy : ∀ j : ℕ, twist (u ^ j) y = y) : rootSum u ℓ (x * y) = rootSum u ℓ x * y := by
  rw [rootSum_apply, rootSum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hy]

theorem sum_zpow_pow {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (n : ℤ) :
    ∑ j ∈ Finset.range ℓ, (ζ ^ n) ^ j = if (ℓ : ℤ) ∣ n then (ℓ : R) else 0 := by
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd n).mpr h]
    simp
  · have hne : ζ ^ n ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd n).mp h')
    rw [geom_sum_eq hne]
    have : (ζ ^ n) ^ ℓ = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

theorem rootSum_coeff {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (hz : ζ ≠ 0)
    (x : LaurentSeries R) (n : ℤ) :
    (rootSum (Units.mk0 ζ hz) ℓ x).coeff n = if (ℓ : ℤ) ∣ n then (ℓ : R) * x.coeff n else 0 := by
  rw [rootSum_apply, HahnSeries.coeff_sum]
  simp only [twist_coeff]
  rw [← Finset.sum_mul]
  have h : ∀ j ∈ Finset.range ℓ, (((Units.mk0 ζ hz ^ j) ^ n : Rˣ) : R) = (ζ ^ n) ^ j := by
    intro j _
    rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [Finset.sum_congr rfl h, sum_zpow_pow hζ n]
  split_ifs <;> simp

end RootSum

section TwistPS

local notation "Qb" => AlgebraicClosure ℚ

theorem intSeriesC_coeff_of_neg (K : Type*) [Field K] (p : PowerSeries ℤ) {n : ℤ} (hn : n < 0) :
    (intSeriesC K p).coeff n = 0 := by
  rw [intSeriesC, PowerSeries.coeff_coe]
  simp [hn]

theorem intSeriesC_coeff_natCast (K : Type*) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    (intSeriesC K p).coeff (n : ℤ) = ((PowerSeries.coeff n p : ℤ) : K) := by
  rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]

theorem twist_intSeriesC (c : Qbˣ) (p : PowerSeries ℤ) :
    twist c (intSeriesC Qb p) =
      HahnSeries.ofPowerSeries ℤ Qb (PowerSeries.rescale (c : Qb) (p.map (Int.castRingHom Qb))) := by
  ext n
  rw [twist_coeff, PowerSeries.coeff_coe]
  split_ifs with hn
  · rw [intSeriesC_coeff_of_neg Qb p hn, mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hn)
    rw [intSeriesC_coeff_natCast, Int.natAbs_natCast, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
      eq_intCast, zpow_natCast, Units.val_pow_eq_pow_val]

def numB : LaurentSeries Qb := intSeriesC Qb (P6 ^ 2)

def denA : LaurentSeries Qb := intSeriesC Qb (P4 ^ 3)

theorem denA_ne_zero : denA ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff (by rw [map_pow, constantCoeff_P4, one_pow])

theorem twist_injective (c : Qbˣ) : Function.Injective (twist c) := by
  intro a b hab
  ext n
  have := congrArg (fun s : LaurentSeries Qb => s.coeff n) hab
  simp only [twist_coeff] at this
  exact (mul_right_inj' (Units.ne_zero _)).mp this

theorem twist_ne_zero (c : Qbˣ) {x : LaurentSeries Qb} (hx : x ≠ 0) : twist c x ≠ 0 :=
  fun h => hx (twist_injective c (by rw [h, map_zero]))

def PBs (a : Qb) : PowerSeries Qb := PowerSeries.rescale a ((P6 ^ 2).map (Int.castRingHom Qb))

def PAs (a : Qb) : PowerSeries Qb := PowerSeries.rescale a ((P4 ^ 3).map (Int.castRingHom Qb))

theorem coeff_zero_PBs (a : Qb) : PowerSeries.coeff 0 (PBs a) = 1 := by
  rw [PBs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, constantCoeff_P6]
  simp

theorem coeff_zero_PAs (a : Qb) : PowerSeries.coeff 0 (PAs a) = 1 := by
  rw [PAs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, constantCoeff_P4]
  simp

theorem coeff_one_PBs (a : Qb) : PowerSeries.coeff 1 (PBs a) = a * (-1008) := by
  rw [PBs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P6,
    constantCoeff_P6, eq_intCast]
  push_cast
  ring

theorem coeff_one_PAs (a : Qb) : PowerSeries.coeff 1 (PAs a) = a * 720 := by
  rw [PAs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P4,
    constantCoeff_P4, eq_intCast]
  push_cast
  ring

theorem coeff_one_mul' (φ ψ : PowerSeries Qb) :
    PowerSeries.coeff 1 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 1 ψ + PowerSeries.coeff 1 φ * PowerSeries.coeff 0 ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.Nat.antidiagonal_zero]
  simp

theorem twist_sep {a b : Qbˣ} (h : twist a (numB / denA) = twist b (numB / denA)) : (a : Qb) = b := by
  rw [map_div₀, map_div₀, div_eq_div_iff (twist_ne_zero a denA_ne_zero) (twist_ne_zero b denA_ne_zero)]
    at h
  rw [numB, denA, twist_intSeriesC, twist_intSeriesC, twist_intSeriesC, twist_intSeriesC, ← map_mul,
    ← map_mul] at h
  have h' := HahnSeries.ofPowerSeries_injective h
  have h1 := congrArg (PowerSeries.coeff 1) h'
  change PowerSeries.coeff 1 (PBs a * PAs b) = PowerSeries.coeff 1 (PBs b * PAs a) at h1
  rw [coeff_one_mul', coeff_one_mul', coeff_zero_PBs, coeff_zero_PAs, coeff_one_PBs, coeff_one_PAs,
    coeff_zero_PBs, coeff_zero_PAs, coeff_one_PBs, coeff_one_PAs] at h1
  have h2 : (1728 : Qb) * (b - a) = 0 := by linear_combination h1
  have h1728 : (1728 : Qb) ≠ 0 := by norm_num
  have := (mul_eq_zero.mp h2).resolve_left h1728
  exact (sub_eq_zero.mp this).symm

theorem twist_twist (a b : Qbˣ) (x : LaurentSeries Qb) : twist a (twist b x) = twist (a * b) x := by
  ext n
  rw [twist_coeff, twist_coeff, twist_coeff, mul_zpow, Units.val_mul, mul_assoc]

end TwistPS

section Trace

local notation "Qb" => AlgebraicClosure ℚ

def EE (_ℓ : ℕ) : Type := AlgebraicClosure (LaurentSeries Qb)

variable (ℓ : ℕ) in
scoped instance : Field (EE ℓ) := inferInstanceAs (Field (AlgebraicClosure (LaurentSeries Qb)))

variable (ℓ : ℕ) in
scoped instance : IsAlgClosed (EE ℓ) := inferInstanceAs (IsAlgClosed (AlgebraicClosure (LaurentSeries Qb)))

/-- The coefficient embedding `LaurentSeries Qb → EE` into the algebraic closure in which
the `ℓ` embeddings of the β-extension take their values. -/
def ιE (ℓ : ℕ) : LaurentSeries Qb →+* EE ℓ :=
  algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))

theorem ιE_injective (ℓ : ℕ) : Function.Injective (ιE ℓ) :=
  (algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))).injective

variable (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime]

abbrev FXt : Type := ↥(x1FunctionFieldBar M)

abbrev FUf : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (x1x0FunctionFieldC ℚ M (M * ℓ))

abbrev FUt : Type := ↥(FUf M ℓ)

abbrev bβ : FXt M →ₐ[Qb] FUt M ℓ := heckeBetaOneBar Qb M ℓ

abbrev bα : FXt M →ₐ[Qb] FUt M ℓ := heckeAlphaOneBar Qb M ℓ

@[reducible] def algAlongBeta : Algebra (FXt M) (FUt M ℓ) :=
  algebraAlong (bβ M ℓ)

@[reducible] def algBetaE : Algebra (FXt M) (EE ℓ) :=
  (((ιE ℓ).comp (algebraMap (FUt M ℓ) (LaurentSeries Qb))).comp (bβ M ℓ).toRingHom).toAlgebra

attribute [local instance] algAlongBeta algBetaE

omit [NeZero M] in
theorem isScalarTower_beta : IsScalarTower Qb (FXt M) (FUt M ℓ) :=
  isScalarTower_along (bβ M ℓ)

attribute [local instance] isScalarTower_beta

/-- The degree of the β-row: `ℓ + 1` at `ℓ ∤ M`. -/
theorem finrank_beta (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ¬ ℓ ∣ M) :
    Module.finrank (FXt M) (FUt M ℓ) = ℓ + 1 := by
  have h := ModularCurve.finrankAlong_heckeBetaOneBar Qb M ℓ hβ
  rw [show (if ℓ ∣ M then ℓ else ℓ + 1) = ℓ + 1 by simp [hℓM]] at h
  exact h

theorem finiteDimensional_beta (hβ : HeckeBetaOneDefined M ℓ) :
    FiniteDimensional (FXt M) (FUt M ℓ) := by
  refine Module.finite_of_finrank_pos ?_
  have h := ModularCurve.finrankAlong_heckeBetaOneBar Qb M ℓ hβ
  change Module.finrank (FXt M) (FUt M ℓ) = _ at h
  rw [h]
  split_ifs
  · exact (Fact.out : ℓ.Prime).pos
  · exact Nat.succ_pos ℓ

/-- The β-extension is separable (the base is a `ℚ`-algebra and the degree is finite). -/
theorem separableAlong_beta (hβ : HeckeBetaOneDefined M ℓ) : SeparableAlong Qb (bβ M ℓ) := by
  have := finiteDimensional_beta M ℓ hβ
  show Algebra.IsSeparable (FXt M) (FUt M ℓ)
  infer_instance

variable {M ℓ}

/-- The embedding of the β-extension cut out by the coefficient twist `q ↦ c q`: it fixes
`FXt` because `c ^ ℓ = 1` and `β` substitutes `q ↦ q ^ ℓ`. -/
def sigmaTwist (hβ : HeckeBetaOneDefined M ℓ) (c : Qbˣ) (hc : c ^ ℓ = 1) :
    FUt M ℓ →ₐ[FXt M] EE ℓ where
  toRingHom := (ιE ℓ).comp ((twist c).toRingHom.comp (algebraMap (FUt M ℓ) (LaurentSeries Qb)))
  commutes' f := by
    show ιE ℓ (twist c ((bβ M ℓ f : FUt M ℓ) : LaurentSeries Qb)) =
      ιE ℓ ((bβ M ℓ f : FUt M ℓ) : LaurentSeries Qb)
    rw [coe_heckeBetaOneBar M ℓ hβ, twist_qExpand_of_pow_eq_one c ℓ hc]

omit [NeZero M] in
theorem sigmaTwist_apply (hβ : HeckeBetaOneDefined M ℓ) (c : Qbˣ) (hc : c ^ ℓ = 1) (v : FUt M ℓ) :
    sigmaTwist hβ c hc v = ιE ℓ (twist c (v : LaurentSeries Qb)) := rfl

/-- The Atkin–Lehner data: an automorphism `W` of the β-field sending `β` to `α` and `α`
back to `β` composed with the diamond automorphism. -/
structure ALData (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) : Prop where
  wβ : ∀ x : FXt M, W (bβ M ℓ x) = bα M ℓ x
  wα : ∀ x : FXt M, W (bα M ℓ x) = bβ M ℓ ((diamondAutBar M ℓ).symm x)

/-- The last embedding: `W`, then the `ℓ`-substitution, then `ιE`. It fixes `FXt` by
`ALData.wβ`. -/
def sigmaLast (hβ : HeckeBetaOneDefined M ℓ) (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) (hW : ALData W) :
    FUt M ℓ →ₐ[FXt M] EE ℓ where
  toRingHom := (ιE ℓ).comp ((qExpand Qb ℓ).comp
    ((algebraMap (FUt M ℓ) (LaurentSeries Qb)).comp W.toAlgHom.toRingHom))
  commutes' f := by
    show ιE ℓ (qExpand Qb ℓ ((W (bβ M ℓ f) : FUt M ℓ) : LaurentSeries Qb)) =
      ιE ℓ ((bβ M ℓ f : FUt M ℓ) : LaurentSeries Qb)
    rw [hW.wβ, coe_heckeAlphaOneBar, coe_heckeBetaOneBar M ℓ hβ]

omit [NeZero M] in
theorem sigmaLast_apply (hβ : HeckeBetaOneDefined M ℓ) (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) (hW : ALData W)
    (v : FUt M ℓ) :
    sigmaLast hβ W hW v = ιE ℓ (qExpand Qb ℓ ((W v : FUt M ℓ) : LaurentSeries Qb)) := rfl

/-- The primitive `ℓ`-th root of unity `ζ` as a unit. -/
def zu {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Qbˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem zu_pow {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (zu hζ ^ j) ^ ℓ = 1 := by
  ext
  rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu,
    Units.val_mk0, hζ.pow_eq_one, one_pow, Units.val_one]

/-- The `ℓ + 1` embeddings of the β-field: the `ℓ` twists by the powers of `ζ`, and the
Atkin–Lehner one. -/
def emb (hβ : HeckeBetaOneDefined M ℓ) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) (hW : ALData W) :
    Option (Fin ℓ) → (FUt M ℓ →ₐ[FXt M] EE ℓ)
  | none => sigmaLast hβ W hW
  | some j => sigmaTwist hβ (zu hζ ^ (j : ℕ)) (zu_pow hζ j)

variable (M) in
/-- The image in `FXt M` of the `q`-expansion generator `xq = E₆²/E₄³`. -/
def xBar : FXt M :=
  ⟨coeffEmb Qb xq, coeffEmb_mem_laurentBaseChange Qb (xq_mem (CongruenceSubgroup.Gamma1 M))⟩

omit [NeZero M] in
theorem coe_xBar : ((xBar M : FXt M) : LaurentSeries Qb) = numB / denA := by
  show coeffEmb Qb xq = _
  rw [xq, map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  rfl

omit [NeZero M] in
theorem emb_injective (hβ : HeckeBetaOneDefined M ℓ) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) (hW : ALData W) :
    Function.Injective (emb hβ hζ W hW) := by
  have hprime : ℓ.Prime := Fact.out

  have vsome : ∀ j : Fin ℓ, emb hβ hζ W hW (some j) (bα M ℓ (xBar M)) =
      ιE ℓ (twist (zu hζ ^ (j : ℕ)) (numB / denA)) := by
    intro j
    show sigmaTwist hβ (zu hζ ^ (j : ℕ)) (zu_pow hζ j) (bα M ℓ (xBar M)) = _
    rw [sigmaTwist_apply, coe_heckeAlphaOneBar, coe_xBar]
  have vnone : emb hβ hζ W hW none (bα M ℓ (xBar M)) =
      ιE ℓ (qExpand Qb ℓ (qExpand Qb ℓ (((diamondAutBar M ℓ).symm (xBar M) : FXt M) :
        LaurentSeries Qb))) := by
    show sigmaLast hβ W hW (bα M ℓ (xBar M)) = _
    rw [sigmaLast_apply, hW.wα, coe_heckeBetaOneBar M ℓ hβ]

  have hsome : ∀ i j : Fin ℓ, twist (zu hζ ^ (i : ℕ)) (numB / denA) =
      twist (zu hζ ^ (j : ℕ)) (numB / denA) → i = j := by
    intro i j h
    have h1 := twist_sep h
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu, Units.val_mk0] at h1
    exact Fin.ext (hζ.pow_inj i.2 j.2 h1)
  intro o₁ o₂ h
  have h' := congrArg (fun σ : FUt M ℓ →ₐ[FXt M] EE ℓ => σ (bα M ℓ (xBar M))) h
  rcases o₁ with _ | j₁ <;> rcases o₂ with _ | j₂
  · rfl
  ·
    exfalso
    rw [vnone, vsome] at h'
    have h2 := ιE_injective ℓ h'
    have h3 : twist (zu hζ) (twist (zu hζ ^ (j₂ : ℕ)) (numB / denA)) =
        twist (zu hζ ^ (j₂ : ℕ)) (numB / denA) := by
      rw [← h2, twist_qExpand_of_pow_eq_one _ ℓ (by simpa using zu_pow hζ 1)]
    rw [twist_twist, ← pow_succ'] at h3
    have h4 := twist_sep h3
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu, Units.val_mk0, pow_succ'] at h4
    have h5 : ζ = 1 := by
      have hz : ζ ^ (j₂ : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne ℓ))
      exact mul_left_eq_self₀.mp h4 |>.resolve_right hz
    exact hζ.ne_one hprime.one_lt h5
  · exfalso
    rw [vnone, vsome] at h'
    have h2 := ιE_injective ℓ h'
    have h3 : twist (zu hζ) (twist (zu hζ ^ (j₁ : ℕ)) (numB / denA)) =
        twist (zu hζ ^ (j₁ : ℕ)) (numB / denA) := by
      rw [h2, twist_qExpand_of_pow_eq_one _ ℓ (by simpa using zu_pow hζ 1)]
    rw [twist_twist, ← pow_succ'] at h3
    have h4 := twist_sep h3
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu, Units.val_mk0, pow_succ'] at h4
    have h5 : ζ = 1 := by
      have hz : ζ ^ (j₁ : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne ℓ))
      exact mul_left_eq_self₀.mp h4 |>.resolve_right hz
    exact hζ.ne_one hprime.one_lt h5
  · rw [vsome, vsome] at h'
    exact congrArg some (hsome j₁ j₂ (ιE_injective ℓ h'))

/-- The embeddings are exactly the `ℓ + 1` of them: the β-degree is `ℓ + 1`. -/
theorem emb_bijective (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ¬ ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) (hW : ALData W) :
    Function.Bijective (emb hβ hζ W hW) := by
  have := finiteDimensional_beta M ℓ hβ
  have : Algebra.IsSeparable (FXt M) (FUt M ℓ) := separableAlong_beta M ℓ hβ
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective hβ hζ W hW, ?_⟩
  rw [Fintype.card_option, Fintype.card_fin, AlgHom.card (FXt M) (FUt M ℓ) (EE ℓ),
    finrank_beta M ℓ hβ hℓM]

/-- **The trace over the β-extension through the `q`-expansion.** The trace of `v` down to
`FXt` expands as the root-of-unity sum of the twisted coefficients plus the last
(Atkin–Lehner) embedding. -/
theorem qExpand_trace (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ¬ ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) (hW : ALData W) (v : FUt M ℓ) :
    qExpand Qb ℓ ((Algebra.trace (FXt M) (FUt M ℓ) v : FXt M) : LaurentSeries Qb)
      = rootSum (zu hζ) ℓ (v : LaurentSeries Qb)
        + qExpand Qb ℓ ((W v : FUt M ℓ) : LaurentSeries Qb) := by
  have := finiteDimensional_beta M ℓ hβ
  have : Algebra.IsSeparable (FXt M) (FUt M ℓ) := separableAlong_beta M ℓ hβ
  apply ιE_injective ℓ
  have h1 := trace_eq_sum_embeddings (EE ℓ) (K := FXt M) (L := FUt M ℓ) (x := v)
  have h2 : algebraMap (FXt M) (EE ℓ) (Algebra.trace (FXt M) (FUt M ℓ) v)
      = ιE ℓ (qExpand Qb ℓ ((Algebra.trace (FXt M) (FUt M ℓ) v : FXt M) : LaurentSeries Qb)) := by
    show ιE ℓ ((bβ M ℓ _ : FUt M ℓ) : LaurentSeries Qb) = _
    rw [coe_heckeBetaOneBar M ℓ hβ]
  rw [← h2, h1, ← (emb_bijective hβ hℓM hζ W hW).sum_comp (fun σ => σ v), Fintype.sum_option,
    map_add, rootSum_apply, map_sum, Finset.sum_range, add_comm]
  rfl

end Trace

section Assembly

local notation "Qb" => AlgebraicClosure ℚ

theorem coeff_C_mul {R : Type*} [CommRing R] (r : R) (x : LaurentSeries R) (n : ℤ) :
    (C r * x).coeff n = r * x.coeff n := by
  rw [C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

variable {M ℓ : ℕ} [NeZero M] [Fact ℓ.Prime]

attribute [local instance] algAlongBeta algBetaE isScalarTower_beta

local notation "FN" => x1FunctionFieldBar M
local notation "FNl" => FUf M ℓ
local notation "β" => heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ
local notation "α" => heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ
local notation "σℓ" => diamondAutBar M ℓ

omit [NeZero M] in

theorem diffQExp_pullback_beta (hβ : HeckeBetaOneDefined M ℓ) (η : Ω[↥FN⁄Qb]) :
    diffQExp FNl (pullbackAlong β η) = C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN η) :=
  diffQExp_pullbackAlong FN FNl β (qExpand Qb ℓ) ℓ (fun x => coe_heckeBetaOneBar M ℓ hβ x)
    (fun y => qEuler_qExpand ℓ y) η

omit [NeZero M] in

theorem diffQExp_pullback_w_beta {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ} (hW : ALData W) (η : Ω[↥FN⁄Qb]) :
    diffQExp FNl (pullbackAlong (W.toAlgHom.comp β) η) = diffQExp FN η := by
  rw [diffQExp_pullbackAlong FN FNl (W.toAlgHom.comp β) (RingHom.id _) 1 ?_ ?_ η, C_one, one_mul,
    RingHom.id_apply]
  · intro x
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hW.wβ, coe_heckeAlphaOneBar, RingHom.id_apply]
  · intro y
    rw [C_one, one_mul]
    rfl

omit [NeZero M] in

theorem diffQExp_pullback_w_alpha (hβ : HeckeBetaOneDefined M ℓ) {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ}
    (hW : ALData W) (η : Ω[↥FN⁄Qb]) :
    diffQExp FNl (pullbackAlong (W.toAlgHom.comp α) η) =
      C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (pullbackAlong ((σℓ).symm : ↥FN →ₐ[Qb] ↥FN) η)) := by
  have hcomp : W.toAlgHom.comp α = (β).comp ((σℓ).symm : ↥FN →ₐ[Qb] ↥FN) := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hW.wα]
    rfl
  rw [hcomp, ← TraceAtPoints.pullbackAlong_pullbackAlong, diffQExp_pullback_beta hβ]

theorem twist_fix {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) (z : LaurentSeries Qb) :
    twist (zu hζ ^ j) (C (ℓ : Qb) * qExpand Qb ℓ z) = C (ℓ : Qb) * qExpand Qb ℓ z := by
  rw [map_mul, twist_C, twist_qExpand_of_pow_eq_one _ ℓ (zu_pow hζ j)]

/-- The coefficient identity, at one fixed primitive `ℓ`-th root `ζ` and one fixed
Atkin–Lehner `W`, stated over a `Qb`-basis of `Ω[FNl⁄Qb]` — the induction invariant of
`MC_all`. -/
def MC {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ) (ξ : Ω[↥FNl⁄Qb]) : Prop :=
  ∀ v : ↥FNl, C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (traceAlong β (v • ξ)))
    = rootSum (zu hζ) ℓ ((v : LaurentSeries Qb) * diffQExp FNl ξ)
      + C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FNl (pullbackAlong W.toAlgHom (v • ξ)))

theorem MC_base (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ¬ ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ} (hW : ALData W) (η : Ω[↥FN⁄Qb]) : MC hζ W (pullbackAlong β η) := by
  intro v
  rw [traceAlong_smul_pullbackAlong β (separableAlong_beta M ℓ hβ) v η, diffQExp_smul, map_mul,
    qExpand_trace hβ hℓM hζ W hW v, diffQExp_pullback_beta hβ,
    rootSum_mul_of_fixed _ _ _ _ (fun j => twist_fix hζ j _), pullbackAlong_smul,
    TraceAtPoints.pullbackAlong_pullbackAlong, diffQExp_smul, diffQExp_pullback_w_beta hW, map_mul,
    AlgEquiv.coe_toAlgHom]
  ring

omit [NeZero M] in
theorem MC_smul {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ}
    (ξ : Ω[↥FNl⁄Qb]) (h : MC hζ W ξ) (u' : ↥FNl) : MC hζ W (u' • ξ) := by
  intro v
  have e1 : v • (u' • ξ) = (v * u') • ξ := smul_smul v u' ξ
  have e2 : (v : LaurentSeries Qb) * diffQExp FNl (u' • ξ)
      = ((v * u' : ↥FNl) : LaurentSeries Qb) * diffQExp FNl ξ := by
    rw [diffQExp_smul, ← mul_assoc]; rfl
  rw [e1, e2]
  exact h (v * u')

omit [NeZero M] in
theorem MC_add {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ}
    (ξ₁ ξ₂ : Ω[↥FNl⁄Qb]) (h₁ : MC hζ W ξ₁) (h₂ : MC hζ W ξ₂) : MC hζ W (ξ₁ + ξ₂) := by
  intro v
  simp only [smul_add, map_add, mul_add, rootSum_add]
  rw [h₁ v, h₂ v]
  ring

omit [NeZero M] in
theorem MC_zero {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ} : MC hζ W 0 := by
  intro v
  simp only [smul_zero, map_zero, mul_zero, rootSum_zero, add_zero]

theorem MC_all (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ¬ ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ} (hW : ALData W) (ξ : Ω[↥FNl⁄Qb]) : MC hζ W ξ := by
  have := finiteDimensional_beta M ℓ hβ
  have : Algebra.IsSeparable (FXt M) (FUt M ℓ) := separableAlong_beta M ℓ hβ
  have : Algebra.FormallyEtale (FXt M) (FUt M ℓ) := Algebra.FormallyEtale.of_isSeparable _ _
  obtain ⟨t, rfl⟩ :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Qb (FXt M) (FUt M ℓ)).surjective ξ
  induction t using TensorProduct.inductionOn with
  | tmul u' η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    change MC hζ W (u' • pullbackAlong β η)
    exact MC_smul hζ _ (MC_base hβ hℓM hζ hW η) u'
  | add x y hx hy => rw [map_add]; exact MC_add hζ _ _ hx hy

theorem key_identity (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ¬ ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ} (hW : ALData W) (ω : Ω[↥FN⁄Qb]) :
    C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (Differential.correspondence β α ω))
      = rootSum (zu hζ) ℓ (diffQExp FN ω)
        + C (ℓ : Qb) * (C (ℓ : Qb) * qExpand Qb ℓ (qExpand Qb ℓ
            (diffQExp FN (pullbackAlong ((σℓ).symm : ↥FN →ₐ[Qb] ↥FN) ω)))) := by
  have key : ∀ ω : Ω[↥FN⁄Qb], ω ∈ Submodule.span (↥FN) (Set.range (D Qb ↥FN)) → ∀ f : ↥FN,
      C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (Differential.correspondence β α (f • ω)))
        = rootSum (zu hζ) ℓ (diffQExp FN (f • ω))
          + C (ℓ : Qb) * (C (ℓ : Qb) * qExpand Qb ℓ (qExpand Qb ℓ
              (diffQExp FN (pullbackAlong ((σℓ).symm : ↥FN →ₐ[Qb] ↥FN) (f • ω))))) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem ω h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      have hM := MC_all hβ hℓM hζ hW (D Qb ↥FNl (α g)) (α f)

      have hW2 : diffQExp FNl (pullbackAlong W.toAlgHom ((α f) • D Qb ↥FNl (α g))) =
          C (ℓ : Qb) * qExpand Qb ℓ
            (diffQExp FN (pullbackAlong ((σℓ).symm : ↥FN →ₐ[Qb] ↥FN) (f • D Qb ↥FN g))) := by
        have e1 : (α f) • D Qb ↥FNl (α g) = pullbackAlong α (f • D Qb ↥FN g) := by
          rw [pullbackAlong_smul, pullbackAlong_D]
        rw [e1, TraceAtPoints.pullbackAlong_pullbackAlong, diffQExp_pullback_w_alpha hβ hW]
      rw [correspondence_apply, pullbackAlong_smul, pullbackAlong_D, hM, hW2, diffQExp_D,
        coe_heckeAlphaOneBar, coe_heckeAlphaOneBar, diffQExp_smul_D, map_mul, qExpand_C]
    | zero => intro f; simp [rootSum_zero]
    | add x y _ _ hx hy =>
      intro f
      simp only [smul_add, map_add, mul_add, rootSum_add]
      rw [hx f, hy f]
      ring
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem coeff_identity (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ¬ ℓ ∣ M)
    (hAL : ∃ W : FUt M ℓ ≃ₐ[Qb] FUt M ℓ, ALData W) (ω : Ω[↥FN⁄Qb]) (n : ℤ) :
    (diffQExp FN (Differential.correspondence β α ω)).coeff n
      = (diffQExp FN ω).coeff (n * ℓ)
        + (ℓ : Qb) * (if (ℓ : ℤ) ∣ n then
            (diffQExp FN (pullbackAlong ((σℓ).symm : ↥FN →ₐ[Qb] ↥FN) ω)).coeff (n / ℓ) else 0) := by
  have : NeZero ((ℓ : ℕ) : Qb) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb ℓ
  obtain ⟨W, hW⟩ := hAL
  have h := congrArg (fun s : LaurentSeries Qb => s.coeff ((ℓ : ℤ) * n)) (key_identity hβ hℓM hζ hW ω)
  rw [coeff_C_mul, qExpand_coeff_mul, HahnSeries.coeff_add, coeff_C_mul, coeff_C_mul,
    qExpand_coeff_mul, zu, rootSum_coeff hζ, ite_eq_left (dvd_mul_right _ _), ← mul_add] at h
  have hℓ0 : ((ℓ : ℕ) : Qb) ≠ 0 := NeZero.ne _
  have h' := mul_left_cancel₀ hℓ0 h
  rw [h', mul_comm (ℓ : ℤ) n]
  congr 2
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [qExpand_coeff_mul, Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne ℓ))]
  · exact qExpand_coeff_of_not_dvd ℓ _ hd

end Assembly

theorem charZero_FX (M : ℕ) : CharZero ↥(ModularCurve.x1FunctionFieldBar M) :=
  charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective

/-- **The `β`/`α` Hecke correspondence at `ℓ ∤ M`.** The `q`-coefficient of the
correspondence `traceAlong β ∘ pullbackAlong α` at `n` is the coefficient of `ω` at
`n * ℓ`, plus `ℓ` times the diamond-twisted coefficient at `n / ℓ` when `ℓ ∣ n`. -/
theorem coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hβ : ModularCurve.HeckeBetaOneDefined M ℓ)
    (hσ : ∃ σ : ↥(ModularCurve.x1FunctionField M) ≃ₐ[ℚ] ↥(ModularCurve.x1FunctionField M),
      ModularCurve.IsDiamondAut M ℓ σ)
    (hσ' : ∃ σ' : ↥(ModularCurve.x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.x1FunctionFieldBar M),
      ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M ℓ) σ')
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
        (AlgebraicCurve.Differential.correspondence
          (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
          (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) ω)).coeff n =
      (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω).coeff (n * ℓ) +
        (ℓ : AlgebraicClosure ℚ) *
          (if (ℓ : ℤ) ∣ n then
            (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
              (AlgebraicCurve.Differential.correspondence
                (ModularCurve.diamondAutBar M ℓ).toAlgHom
                (AlgHom.id (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)) ω)).coeff
              (n / ℓ)
           else 0) := by
  have := charZero_FX M
  obtain ⟨W, hW1, hW2⟩ :=
    ModularCurve.exists_algEquiv_x1x0FunctionFieldC_atkinLehner M ℓ hℓM hβ hσ hσ'
  rw [correspondence_algEquiv_id]
  exact coeff_identity hβ hℓM ⟨W, ⟨hW1, hW2⟩⟩ ω n

end ModularCurve.X1HeckeCorrespondence

end
