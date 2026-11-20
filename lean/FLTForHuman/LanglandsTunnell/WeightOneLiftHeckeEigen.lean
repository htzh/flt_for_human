/-
  The weight-one lift is a Hecke-coset eigenfunction.

  For a weight-one form `f` on `Γ₁(n)` that is an eigenform for the Hecke operators away from a
  finite set `S`, with eigensystem `Φ`, the adelic lift is an eigenfunction of the local Hecke
  coset operators `(productionPinsCompact ℚ).gen v` with the same eigenvalues.

  Transcribed from `P2M/Sol/S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift.lean`
  (pinned `aa2d8b3`, 1,753 lines / 163 declarations: 34 in the shared prelude, 129 in the row's
  own `P2GProbe.C3` blocks, i.e. 128 private declarations plus `solution`). The port carries
  those 128 declarations — 127 `private` ones plus the row — at the pin's visibility, names and
  statements (`C3.foo` is plain `foo` in `namespace LanglandsTunnell`); the row is the pin's
  `solution` (`:1718`). The shared prelude is imported from `WeightOneLiftAdelic`.

  spec-pin: P2M/Sol/S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift.lean

  ## Port deltas

  - One `set_option` line added at file scope, `linter.style.haveILetI false`: the pin's bodies
    carry nine `have`/`letI` whose goal is a proposition, and the port's linter (absent from the
    pin) flags them. No proof is changed.
  - `omit hp in` (`one_notMem_asIdeal`) and `omit [Fintype ι] in` (`crossIndex_injective`) are the
    pin's own (`:926`, `:754`). The scaffold dropped them and the port's
    `linter.unusedSectionVars` reports both; restored, statement-neutral.
  - `Matrix.SpecialLinearGroup` is a `def` at mathlib v4.34, not an `abbrev` (FR-0245), so the
    pin's `simp`-based `mapGL_coe_matrix`/`map_apply_coe` rewrites through the coercion do not
    replay. In `ratHeckeRep_some_eq` those two lemmas are `rw`n before `fin_cases`; in
    `ratRep_none_mul_twistQ` a local `have` (proved by `Matrix.GeneralLinearGroup.ext` and
    `sl2ToQ_apply`) first turns `twistQ` into a `mapGL`. Both are body-only changes.
  - `ofReal_inv`/`ofReal_natCast`/`ofReal_div`/`ofReal_neg`/`ofReal_intCast` are gone at v4.34;
    `num_heckeArchFin` uses `push_cast` instead.
  - `mul_apply` is qualified `Matrix.mul_apply` in the three `ratHeckeRep_inv_mul_apply_*`
    proofs: the port's preamble has `open HeckePair`, which brings `HeckePair.mul_apply` into
    scope (the pin opens only `HeckeIntegralSeam`).
  - `if_neg` → `ite_eq_right` in `sum_f_heckeArchFin_smul` (deprecation).
  - The pin's `P2.Artin.absNorm_coprime_of_not_dvd` has no port; its proof is inlined, as a
    `have`, in `exists_twist_data` (`:1100`), statement-neutral.
  - No import added, no statement re-spelled, no declaration renamed or dropped; all 113 pin
    bodies are filled.

  ## Heartbeat probe (measured, never installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/LanglandsTunnell/WeightOneLiftHeckeEigen.lean`
  is silent at `N = 8000` and fails at `N = 6000` and at `N = 4000` (deterministic timeouts, at
  `:911`/`isDefEq` and at `ratRep_none_mul_twistQ`/`whnf` respectively); it is also silent at the
  playbook's `200000`. The project cap is 4,000,000, so the module is nowhere near it and no
  `set_option maxHeartbeats` is installed.
-/


import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
import FLTForHuman.LanglandsTunnell.DihedralWeightOneLift
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.LanglandsTunnell.HeckeCosetSystem
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsTail
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SmoothRealization
import FLTForHuman.NumberTheory.AdelicHaar.Adele

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix
open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open Matrix Matrix.GeneralLinearGroup
open CongruenceSubgroup ModularGroup
open AdelicDock
open NumberField.AdelicHaar
open HeckeIntegralSeam HeckePair
open AutomorphicForm.SmoothCusp IsDedekindDomain.HeightOneSpectrum
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne
local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ


namespace LanglandsTunnell

open RatArch DetIntegral ArchLift



private def heckeArchFin (p : ℕ) [NeZero p] (j : ℤ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![((p : ℝ))⁻¹, -(j : ℝ) / p; 0, 1] (by
    rw [Matrix.det_fin_two_of]; simp [NeZero.ne p])

private def heckeArchInf (p : ℕ) [NeZero p] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, ((p : ℝ))⁻¹] (by
    rw [Matrix.det_fin_two_of]; simp [NeZero.ne p])

private theorem det_heckeArchFin (p : ℕ) [NeZero p] (j : ℤ) : (heckeArchFin p j).det.val = ((p : ℝ))⁻¹ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det !![((p : ℝ))⁻¹, -(j : ℝ) / p; 0, 1] = _
  rw [Matrix.det_fin_two_of]; ring

private theorem det_heckeArchInf (p : ℕ) [NeZero p] : (heckeArchInf p).det.val = ((p : ℝ))⁻¹ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det !![(1 : ℝ), 0; 0, ((p : ℝ))⁻¹] = _
  rw [Matrix.det_fin_two_of]; ring

section

variable (p : ℕ) [hp : Fact p.Prime]

private theorem heckeArchFin_apply (j : ℤ) (i l : Fin 2) :
    ((heckeArchFin p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i l = !![((p : ℝ))⁻¹, -(j : ℝ) / p; 0, 1] i l :=
  rfl

private theorem heckeArchInf_apply (i l : Fin 2) :
    ((heckeArchInf p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i l = !![(1 : ℝ), 0; 0, ((p : ℝ))⁻¹] i l :=
  rfl

private theorem cast_p_ne_zero {K : Type*} [DivisionRing K] [CharZero K] : (p : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr hp.out.ne_zero

private noncomputable def ratHeckeRep : Option (ZMod p) → GL (Fin 2) ℚ
  | some c => mkOfDetNeZero !![(p : ℚ), ((ZMod.val c : ℕ) : ℚ); 0, 1]
      (by rw [Matrix.det_fin_two_of]; simp [cast_p_ne_zero p])
  | none => mkOfDetNeZero !![1, 0; 0, (p : ℚ)]
      (by rw [Matrix.det_fin_two_of]; simp [cast_p_ne_zero p])

private theorem ratHeckeRep_some_apply (c : ZMod p) (i l : Fin 2) :
    ((ratHeckeRep p (some c) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i l
      = !![(p : ℚ), ((ZMod.val c : ℕ) : ℚ); 0, 1] i l := rfl

private theorem ratHeckeRep_none_apply (i l : Fin 2) :
    ((ratHeckeRep p none : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i l
      = !![1, 0; 0, (p : ℚ)] i l := rfl

private theorem heckeArchFin_mul_mapGL_ratHeckeRep_some (c : ZMod p) :
    heckeArchFin p (ZMod.val c : ℤ)
      * GeneralLinearGroup.map (algebraMap ℚ ℝ) (ratHeckeRep p (some c)) = 1 := by
  have hP : (p : ℝ) ≠ 0 := cast_p_ne_zero p
  refine Matrix.GeneralLinearGroup.ext fun i l => ?_
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [heckeArchFin_apply, Matrix.GeneralLinearGroup.map_apply, ratHeckeRep_some_apply]
  fin_cases i <;> fin_cases l <;> push_cast <;> simp [-ZMod.natCast_val]
  field_simp
  ring

private theorem heckeArchInf_mul_mapGL_ratHeckeRep_none :
    heckeArchInf p * GeneralLinearGroup.map (algebraMap ℚ ℝ) (ratHeckeRep p none) = 1 := by
  have hP : (p : ℝ) ≠ 0 := cast_p_ne_zero p
  refine Matrix.GeneralLinearGroup.ext fun i l => ?_
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [heckeArchInf_apply, Matrix.GeneralLinearGroup.map_apply, ratHeckeRep_none_apply]
  fin_cases i <;> fin_cases l <;> simp [hP]

private theorem mapGL_ratHeckeRep_some_inv (c : ZMod p) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (ratHeckeRep p (some c))⁻¹
      = heckeArchFin p (ZMod.val c : ℤ) := by
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_left (heckeArchFin_mul_mapGL_ratHeckeRep_some p c)

private theorem mapGL_ratHeckeRep_none_inv :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (ratHeckeRep p none)⁻¹ = heckeArchInf p := by
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_left (heckeArchInf_mul_mapGL_ratHeckeRep_none p)

end

section

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))

private noncomputable def adelicHeckeRep [Fact (Ideal.absNorm v.asIdeal).Prime]
    (i : Option (ZMod (Ideal.absNorm v.asIdeal))) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (ratHeckeRep (Ideal.absNorm v.asIdeal) i)))

end

section

variable (p : ℕ) [hp : Fact p.Prime]

private theorem natCast_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos

private theorem det_pos_heckeArchFin (j : ℤ) : 0 < (heckeArchFin p j).det.val := by
  rw [det_heckeArchFin]; exact inv_pos.mpr (natCast_pos p)

private theorem det_pos_heckeArchInf : 0 < (heckeArchInf p).det.val := by
  rw [det_heckeArchInf]; exact inv_pos.mpr (natCast_pos p)

private theorem denom_heckeArchFin (j : ℤ) (z : ℍ) : denom (heckeArchFin p j) z = 1 := by
  simp [denom, heckeArchFin_apply]

private theorem denom_heckeArchInf (z : ℍ) : denom (heckeArchInf p) z = ((p : ℂ))⁻¹ := by
  simp [denom, heckeArchInf_apply]

private theorem num_heckeArchFin (j : ℤ) (z : ℍ) : num (heckeArchFin p j) z = ((z : ℂ) - j) / p := by
  have hP : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [num, heckeArchFin_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  push_cast
  field_simp
  ring

private theorem num_heckeArchInf (z : ℍ) : num (heckeArchInf p) z = z := by
  simp [num, heckeArchInf_apply]

private theorem coe_heckeArchFin_smul (j : ℤ) (z : ℍ) : (((heckeArchFin p j) • z : ℍ) : ℂ) = ((z : ℂ) - j) / p := by
  rw [coe_smul_of_det_pos (det_pos_heckeArchFin p j), num_heckeArchFin, denom_heckeArchFin, div_one]

private theorem coe_heckeArchInf_smul (z : ℍ) : (((heckeArchInf p) • z : ℍ) : ℂ) = p * z := by
  have hP : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [coe_smul_of_det_pos (det_pos_heckeArchInf p), num_heckeArchInf, denom_heckeArchInf, div_inv_eq_mul, mul_comm]

private theorem σ_heckeArchFin (j : ℤ) (w : ℂ) : σ (heckeArchFin p j) w = w := by
  have h' : 0 < ((heckeArchFin p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact det_pos_heckeArchFin p j
  simp [σ, h']

private theorem σ_heckeArchInf (w : ℂ) : σ (heckeArchInf p) w = w := by
  have h' : 0 < ((heckeArchInf p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact det_pos_heckeArchInf p
  simp [σ, h']

end

section

variable {G : Type*} [Group G] {U : Subgroup G} {g : G}
  {ι : Type*} [Fintype ι] {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps)

include hsys

private noncomputable def leftPermIndex (u₀ : G) (hu₀ : u₀ ∈ U) (i : ι) : ι :=
  (hsys.covers (u₀ * reps i) (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu₀)).choose

omit [Fintype ι] in

private theorem mk_leftPermIndex (u₀ : G) (hu₀ : u₀ ∈ U) (i : ι) :
    (QuotientGroup.mk (u₀ * reps i) : G ⧸ U)
      = QuotientGroup.mk (reps ((leftPermIndex hsys) u₀ hu₀ i)) :=
  (hsys.covers (u₀ * reps i) (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu₀)).choose_spec

private theorem leftPermIndex_bijective (u₀ : G) (hu₀ : u₀ ∈ U) :
    Function.Bijective ((leftPermIndex hsys) u₀ hu₀) := by
  refine (Finite.injective_iff_bijective).mp fun i₁ i₂ hi => ?_
  have h₁ := (mk_leftPermIndex hsys) u₀ hu₀ i₁
  have h₂ := (mk_leftPermIndex hsys) u₀ hu₀ i₂
  rw [hi] at h₁
  have heq : (QuotientGroup.mk (u₀ * reps i₁) : G ⧸ U) = QuotientGroup.mk (u₀ * reps i₂) :=
    h₁.trans h₂.symm
  have hrep : (QuotientGroup.mk (reps i₁) : G ⧸ U) = QuotientGroup.mk (reps i₂) := by
    rw [QuotientGroup.eq] at heq ⊢
    simpa [mul_assoc] using heq
  exact hsys.mk_injective hrep

private theorem sum_mul_left_eq {M : Type*} [AddCommMonoid M]
    (φ : G → M) (hφ : ∀ x, ∀ u ∈ U, φ (x * u) = φ x)
    (h u₀ : G) (hu₀ : u₀ ∈ U) :
    ∑ i, φ (h * (u₀ * reps i)) = ∑ i, φ (h * reps i) := by
  refine Fintype.sum_bijective ((leftPermIndex hsys) u₀ hu₀)
    ((leftPermIndex_bijective hsys) u₀ hu₀) _ _ fun i => ?_
  have hu' : (reps ((leftPermIndex hsys) u₀ hu₀ i))⁻¹ * (u₀ * reps i) ∈ U :=
    QuotientGroup.eq.mp ((mk_leftPermIndex hsys) u₀ hu₀ i).symm
  have hueq : h * (u₀ * reps i)
      = h * reps ((leftPermIndex hsys) u₀ hu₀ i)
        * ((reps ((leftPermIndex hsys) u₀ hu₀ i))⁻¹ * (u₀ * reps i)) := by
    rw [mul_assoc h, ← mul_assoc (reps _), mul_inv_cancel, one_mul]
  rw [hueq, hφ _ _ hu']

end

section

variable {G : Type*} [Group G] {U : Subgroup G} {g : G}
  {n : ℕ} {reps : Fin n → G} (hsys : IsHeckeCosetSystem U g reps)
variable {ι : Type*} [Fintype ι] {reps' : ι → G}
  (hmem : ∀ i, reps' i ∈ HeckePair.doubleCoset U g)
  (hinj : Function.Injective fun i => (QuotientGroup.mk (reps' i) : G ⧸ U))

include hsys

private noncomputable def crossIndex (i : ι) : Fin n :=
  (hsys.covers (reps' i) (hmem i)).choose

omit [Fintype ι] in
include hmem in

include hmem in

private theorem mk_crossIndex (i : ι) :
    (QuotientGroup.mk (reps' i) : G ⧸ U) = QuotientGroup.mk (reps ((crossIndex hsys) hmem i)) :=
  (hsys.covers (reps' i) (hmem i)).choose_spec

omit [Fintype ι] in
include hmem hinj in

private theorem crossIndex_injective : Function.Injective ((crossIndex hsys) hmem) := fun i₁ i₂ hi => by
  have h₁ := (mk_crossIndex hsys) hmem i₁
  have h₂ := (mk_crossIndex hsys) hmem i₂
  rw [hi] at h₁
  exact hinj (h₁.trans h₂.symm)

include hmem hinj in

private theorem sum_cross_eq {M : Type*} [AddCommMonoid M]
    (hcard : Fintype.card ι = n)
    (φ : G → M) (hφ : ∀ x, ∀ u ∈ U, φ (x * u) = φ x) (h : G) :
    ∑ i, φ (h * reps' i) = ∑ j, φ (h * reps j) := by
  have hbij : Function.Bijective ((crossIndex hsys) hmem) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(crossIndex_injective hsys) hmem hinj, hcard.trans (Fintype.card_fin n).symm⟩
  refine Fintype.sum_bijective ((crossIndex hsys) hmem) hbij _ _ fun i => ?_
  have hu' : (reps ((crossIndex hsys) hmem i))⁻¹ * reps' i ∈ U :=
    QuotientGroup.eq.mp ((mk_crossIndex hsys) hmem i).symm
  have hueq : h * reps' i
      = h * reps ((crossIndex hsys) hmem i) * ((reps ((crossIndex hsys) hmem i))⁻¹ * reps' i) := by
    rw [mul_assoc h, ← mul_assoc (reps _), mul_inv_cancel, one_mul]
  rw [hueq, hφ _ _ hu']

end

section

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
  [hp : Fact (Ideal.absNorm v.asIdeal).Prime]

local notation "Nv" => Ideal.absNorm v.asIdeal

private theorem absNorm_cast_ne_zero : ((Nv : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr hp.out.ne_zero

private theorem prime_absNorm_cast : Prime ((Nv : ℕ) : 𝓞 ℚ) := by
  have hcast : ((Nv : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((Nv : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Nv : ℕ)).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

private theorem isMaximal_span_absNorm : (Ideal.span {((Nv : ℕ) : 𝓞 ℚ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (absNorm_cast_ne_zero v)).mpr (prime_absNorm_cast v)).isMaximal
    ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (absNorm_cast_ne_zero v))

private theorem asIdeal_eq_span_absNorm : v.asIdeal = Ideal.span {((Nv : ℕ) : 𝓞 ℚ)} :=
  ((isMaximal_span_absNorm v).eq_of_le v.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.absNorm_mem v.asIdeal))).symm

private theorem valued_absNorm_self :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ ((Nv : ℕ) : 𝓞 ℚ)))
      = WithZero.exp (-1 : ℤ) := by
  rw [valued_algebraMap,
    intValuation_singleton v (absNorm_cast_ne_zero v) (asIdeal_eq_span_absNorm v)]

private theorem absNorm_notMem_asIdeal_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((Nv : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun hmem => hw <| HeightOneSpectrum.ext <|
  ((isMaximal_span_absNorm v).eq_of_le w.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hmem)) ▸ (asIdeal_eq_span_absNorm v).symm

private theorem intValuation_absNorm_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    w.intValuation ((Nv : ℕ) : 𝓞 ℚ) = 1 :=
  intValuation_eq_one_iff.mpr (absNorm_notMem_asIdeal_of_ne v hw)

private theorem valued_algebraMap_absNorm_self :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((Nv : ℕ) : ℚ)) = WithZero.exp (-1 : ℤ) := by
  rw [show ((Nv : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((Nv : ℕ) : 𝓞 ℚ) from
    (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm]
  exact valued_absNorm_self v

private theorem valued_algebraMap_absNorm_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) ((Nv : ℕ) : ℚ)) = 1 := by
  rw [show ((Nv : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((Nv : ℕ) : 𝓞 ℚ) from
    (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm, valued_algebraMap]
  exact intValuation_absNorm_of_ne v hw

private theorem glArch_diagOne_finIncl (b : (𝔸f)ˣ) :
    glArch (𝓞 ℚ) ℚ (diagOne (Units.map (finIncl (𝓞 ℚ) ℚ : 𝔸f →* AdeleRing (𝓞 ℚ) ℚ) b)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, diagOne_coe_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> rfl

private theorem glArch_heckeGenAt (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    glArch (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ v t) = 1 :=
  glArch_diagOne_finIncl _

end

section

variable (p : ℕ) [hp : Fact p.Prime]

private def diagNat : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1] (by
    rw [Matrix.det_fin_two_of]; simp [hp.out.ne_zero])

private theorem diagNat_apply (i j : Fin 2) :
    ((diagNat p : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = !![(p : ℚ), 0; 0, 1] i j := rfl

private def unipZ (m : ℤ) : SL(2, ℤ) := ⟨!![1, m; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem ratHeckeRep_some_eq (c : ZMod p) :
    ratHeckeRep p (some c) = Matrix.SpecialLinearGroup.mapGL ℚ (unipZ (c.val : ℤ)) * diagNat p := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, ratHeckeRep_some_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagNat_apply, unipZ, RingHom.mapMatrix_apply, Matrix.map_apply]

private def natIdele : (𝔸f)ˣ :=
  Units.map (algebraMap ℚ 𝔸f : ℚ →* 𝔸f) (Units.mk0 (p : ℚ) (by exact_mod_cast hp.out.ne_zero))

private theorem finiteAdele_mul_apply (x y : 𝔸f) (w : HeightOneSpectrum (𝓞 ℚ)) : (x * y) w = x w * y w := rfl

private theorem natIdele_apply (w : HeightOneSpectrum (𝓞 ℚ)) :
    (natIdele p : 𝔸f) w = algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ) := rfl

private theorem natIdele_inv_apply (w : HeightOneSpectrum (𝓞 ℚ)) :
    (((natIdele p)⁻¹ : (𝔸f)ˣ) : 𝔸f) w = algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ)⁻¹ := by
  rw [natIdele, ← map_inv, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
  rfl

private theorem finPart_globalPoints_diagNat :
    finPart (globalPoints (𝓞 ℚ) ℚ (diagNat p))
      = diagOne (Units.map (finIncl (𝓞 ℚ) ℚ : 𝔸f →* AdeleRing (𝓞 ℚ) ℚ) (natIdele p)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · fin_cases i <;> fin_cases j <;> rfl
  · show algebraMap ℚ 𝔸f (((diagNat p : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
    fin_cases i <;> fin_cases j
    · rfl
    · exact map_zero _
    · exact map_zero _
    · exact map_one _

end

section

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
  [hp : Fact (Ideal.absNorm v.asIdeal).Prime]
omit hp in
private theorem one_notMem_asIdeal : (1 : 𝓞 ℚ) ∉ v.asIdeal := fun h =>
  v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

local notation "Nv" => Ideal.absNorm v.asIdeal

private theorem not_mem_integralFiniteAdeles_intCast_div_absNorm {q : ℤ} (hq : (q : 𝓞 ℚ) ∉ v.asIdeal) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚ) / (Nv : ℚ))
      ∉ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro hmem
  have hNvne : ((Nv : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hle : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((q : ℚ) / (Nv : ℚ))) ≤ 1 :=
    (mem_adicCompletionIntegers _ _ _).mp (hmem v)
  rw [map_div₀, map_div₀, valued_algebraMap_absNorm_self v,
    show ((q : ℤ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((q : ℤ) : 𝓞 ℚ) from
      (map_intCast (algebraMap (𝓞 ℚ) ℚ) q).symm,
    valued_algebraMap, intValuation_eq_one_iff.mpr hq, one_div, ← WithZero.exp_neg,
    neg_neg] at hle
  have e0 : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) := by simp [WithZero.exp]
  rw [e0] at hle
  exact absurd (WithZero.exp_le_exp.mp hle) (by omega)

private theorem coe_ratHeckeRep_some (c : ZMod Nv) :
    ((ratHeckeRep Nv (some c) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = !![(Nv : ℚ), (ZMod.val c : ℚ); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratHeckeRep_some_apply]

private theorem coe_ratHeckeRep_none :
    ((ratHeckeRep Nv none : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = !![1, 0; 0, (Nv : ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ratHeckeRep_none_apply]

private theorem ratHeckeRep_inv_mul_apply_01 (c c' : ZMod Nv) :
    (((ratHeckeRep Nv (some c'))⁻¹ * ratHeckeRep Nv (some c) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) 0 1 = ((ZMod.val c : ℤ) - (ZMod.val c' : ℤ) : ℚ) / (Nv : ℚ) := by
  have hNvne : ((Nv : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, coe_ratHeckeRep_some,
    Matrix.inv_def, adjugate_fin_two_of, det_fin_two_of, Ring.inverse_eq_inv',
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, of_apply, cons_val_zero,
    cons_val_one]
  push_cast
  ring_nf

private theorem ratHeckeRep_inv_mul_apply_00_some_none (c : ZMod Nv) :
    (((ratHeckeRep Nv (some c))⁻¹ * ratHeckeRep Nv none : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) 0 0 = ((1 : ℤ) : ℚ) / (Nv : ℚ) := by
  have hNvne : ((Nv : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, coe_ratHeckeRep_some,
    coe_ratHeckeRep_none, Matrix.inv_def, adjugate_fin_two_of, det_fin_two_of,
    Ring.inverse_eq_inv', Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
    of_apply, cons_val_zero, cons_val_one]
  push_cast
  ring_nf

private theorem ratHeckeRep_inv_mul_apply_11_none_some (c : ZMod Nv) :
    (((ratHeckeRep Nv none)⁻¹ * ratHeckeRep Nv (some c) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) 1 1 = ((1 : ℤ) : ℚ) / (Nv : ℚ) := by
  have hNvne : ((Nv : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, coe_ratHeckeRep_some,
    coe_ratHeckeRep_none, Matrix.inv_def, adjugate_fin_two_of, det_fin_two_of,
    Ring.inverse_eq_inv', Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
    of_apply, cons_val_zero, cons_val_one]
  push_cast
  ring_nf

private theorem sub_val_notMem_asIdeal {c c' : ZMod Nv} (hcc' : c ≠ c') :
    (((ZMod.val c : ℤ) - (ZMod.val c' : ℤ) : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := by
  have : NeZero Nv := ⟨hp.out.ne_zero⟩
  intro hmem
  have hdvd : ((Nv : ℕ) : 𝓞 ℚ) ∣ (((ZMod.val c : ℤ) - (ZMod.val c' : ℤ) : ℤ) : 𝓞 ℚ) :=
    Ideal.mem_span_singleton.mp ((asIdeal_eq_span_absNorm v) ▸ hmem)
  have hdvdℤ : ((Nv : ℕ) : ℤ) ∣ ((ZMod.val c : ℤ) - (ZMod.val c' : ℤ)) := by
    have h' := map_dvd (Rat.ringOfIntegersEquiv : (𝓞 ℚ) →+* ℤ) hdvd
    rwa [map_natCast, map_intCast] at h'
  have h1 := ZMod.val_lt c; have h2 := ZMod.val_lt c'
  have hlt : |((ZMod.val c : ℤ) - (ZMod.val c' : ℤ))| < (Nv : ℤ) := by
    rw [abs_sub_lt_iff]; omega
  have heq := Int.eq_zero_of_abs_lt_dvd hdvdℤ hlt
  exact hcc' (ZMod.val_injective _ (by omega))

private theorem mk_adelicHeckeRep_injective :
    Function.Injective (fun i => (QuotientGroup.mk (adelicHeckeRep v i) :
      𝔾 ⧸ (productionPinsCompact ℚ).U ⊤)) := by
  intro i j hij
  by_contra hne
  have hmem : (adelicHeckeRep v j)⁻¹ * adelicHeckeRep v i ∈ (productionPinsCompact ℚ).U ⊤ :=
    QuotientGroup.eq.mp hij.symm

  have hmemfin : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      ((ratHeckeRep Nv j)⁻¹ * ratHeckeRep Nv i)) ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤ := by
    have hmem' := ((mem_U_top_iff _).mp hmem).1
    unfold adelicHeckeRep at hmem'
    rw [← map_inv, ← map_mul, glFin_finEmbed, ← map_inv, ← map_mul, ← map_inv, ← map_mul] at hmem'
    exact hmem'

  have hint := hmemfin.1.1.integral

  rcases j with _ | c' <;> rcases i with _ | c
  · exact hne rfl
  · refine not_mem_integralFiniteAdeles_intCast_div_absNorm v (q := 1)
      (by exact_mod_cast one_notMem_asIdeal v) ?_
    have := hint 1 1
    rwa [glFin_globalPoints_apply, ratHeckeRep_inv_mul_apply_11_none_some] at this
  · refine not_mem_integralFiniteAdeles_intCast_div_absNorm v (q := 1)
      (by exact_mod_cast one_notMem_asIdeal v) ?_
    have := hint 0 0
    rwa [glFin_globalPoints_apply, ratHeckeRep_inv_mul_apply_00_some_none] at this
  · refine not_mem_integralFiniteAdeles_intCast_div_absNorm v
      (q := (ZMod.val c : ℤ) - (ZMod.val c' : ℤ))
      (sub_val_notMem_asIdeal v (fun h => hne (h ▸ rfl))) ?_
    have := hint 0 1
    rw [glFin_globalPoints_apply, ratHeckeRep_inv_mul_apply_01] at this
    convert this using 2; push_cast; ring

private theorem card_option_zmod_absNorm :
    Fintype.card (Option (ZMod Nv)) = Nv + 1 := by
  have : NeZero Nv := ⟨hp.out.ne_zero⟩
  rw [Fintype.card_option, ZMod.card]

private theorem c3_absNorm_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
      Rat.ringOfIntegersEquiv.symm.surjective
  set π := Submodule.IsPrincipal.generator v.asIdeal with hπdef
  have hspan := (Submodule.IsPrincipal.span_singleton_generator v.asIdeal).symm
  have hπprime : Prime π :=
    Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot
  have hπℤ : Prime (Rat.ringOfIntegersEquiv π) :=
    (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.toMulEquiv).mpr hπprime
  have hrank : Module.finrank ℤ (𝓞 ℚ) = 1 :=
    (RingOfIntegers.rank ℚ).trans (Module.finrank_self (R := ℚ))
  have hπeq : algebraMap ℤ (𝓞 ℚ) (Rat.ringOfIntegersEquiv π) = π := by
    rw [algebraMap_int_eq, eq_intCast,
      show ((Rat.ringOfIntegersEquiv π : ℤ) : 𝓞 ℚ)
        = Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv π) from
        (map_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm,
      RingEquiv.symm_apply_apply]
  rw [hspan, Ideal.absNorm_span_singleton, ← hπdef, ← hπeq, Algebra.norm_algebraMap, hrank,
    pow_one]
  exact Int.prime_iff_natAbs_prime.mp hπℤ

private theorem c3_exists_decomp {n : ℕ} (hn : n ≠ 0) (g : 𝔾) :
    ∃ (γ : GL (Fin 2) ℚ) (h u : 𝔾), u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}) ∧
      glFin (𝓞 ℚ) ℚ h = 1 ∧ LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧
      g = globalPoints (𝓞 ℚ) ℚ γ * h * u := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  exact hasWeightOneDecomp_of_ne_bot hN g

private theorem c3_lift_mul_of_mem_U {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : 𝔾) {u₀ : 𝔾} (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (g * u₀) = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g :=
  weightOneLift_mul_of_mem_U hn f hf g hu₀

private theorem c3_lift_globalPoints_mul {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (γ₀ : GL (Fin 2) ℚ) (g : 𝔾) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ₀ * g)
      = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g :=
  weightOneLift_globalPoints_mul hn f hf γ₀ g

private theorem exists_twist_data {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ∃ b d : ℤ, ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) * d - b * (n : ℤ) = 1 := by
  have hcop : Nat.Coprime (Ideal.absNorm v.asIdeal) n := by
    classical
    have hmax : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
    let : Field (𝓞 ℚ ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : Fintype (𝓞 ℚ ⧸ v.asIdeal) := Fintype.ofFinite _
    obtain ⟨m, hprime, hcard⟩ :=
      FiniteField.card (𝓞 ℚ ⧸ v.asIdeal) (ringChar (𝓞 ℚ ⧸ v.asIdeal))
    have habs : Ideal.absNorm v.asIdeal = ringChar (𝓞 ℚ ⧸ v.asIdeal) ^ (m : ℕ) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← hcard]
    rw [habs]
    refine Nat.Coprime.pow_left _ ?_
    by_contra hnc
    have hpq : ringChar (𝓞 ℚ ⧸ v.asIdeal) ∣ n := by
      by_contra hdvd
      exact hnc ((Nat.Prime.coprime_iff_not_dvd hprime).mpr hdvd)
    apply hv
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    have hpmem : ((ringChar (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [map_natCast (Ideal.Quotient.mk v.asIdeal), CharP.cast_eq_zero]
    obtain ⟨t, ht⟩ := hpq
    have hqt : ((n : ℕ) : 𝓞 ℚ)
        = ((ringChar (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : 𝓞 ℚ) * ((t : ℕ) : 𝓞 ℚ) := by
      rw [← Nat.cast_mul, ← ht]
    rw [SetLike.mem_coe, hqt]
    exact Ideal.mul_mem_right _ _ hpmem
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.mpr hcop)
  exact ⟨-w, u, by linear_combination huw⟩

private noncomputable def twistZ {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) : SL(2, ℤ) :=
  ⟨!![((Ideal.absNorm v.asIdeal : ℕ) : ℤ), Classical.choose (exists_twist_data v hv);
      (n : ℤ), Classical.choose (Classical.choose_spec (exists_twist_data v hv))],
    by
      rw [Matrix.det_fin_two_of]
      exact Classical.choose_spec (Classical.choose_spec (exists_twist_data v hv))⟩

private theorem twistZ_mem_Gamma0 {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) : twistZ v hv ∈ CongruenceSubgroup.Gamma0 n := by
  rw [CongruenceSubgroup.Gamma0_mem]
  show (((n : ℤ) : ZMod n)) = 0
  exact_mod_cast ZMod.natCast_self n

private noncomputable def sl2ToQ (ε : SL(2, ℤ)) : GL (Fin 2) ℚ :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) ε)

private theorem sl2ToQ_apply (ε : SL(2, ℤ)) (i j : Fin 2) :
    ((sl2ToQ ε : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = ((ε i j : ℤ) : ℚ) := rfl

private theorem sl2ToQ_inv (ε : SL(2, ℤ)) : (sl2ToQ ε)⁻¹ = sl2ToQ ε⁻¹ := by
  unfold sl2ToQ; rw [map_inv, map_inv]

private noncomputable def twistQ {n : ℕ} (_hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) : GL (Fin 2) ℚ :=
  sl2ToQ (twistZ v hv)

private theorem c3_intCast_mem_integralFiniteAdeles (m : ℤ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((m : ℤ) : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro w
  have h := NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers (K := ℚ) w ((m : ℤ) : 𝓞 ℚ)
  rw [map_intCast] at h
  exact h

private theorem mem_idealBall_top_of_mem_integral {x : FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) : x ∈ idealBall (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)) := by
  intro w
  rw [NumberField.AdelicLevel.idealBound_top]
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ w).mp (hx w)

private theorem isLevelOneMatrix_top_of_integral {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hm : ∀ i j, m i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)) m :=
  { integral := hm
    lowerLeft := mem_idealBall_top_of_mem_integral (hm 1 0)
    lowerRight := mem_idealBall_top_of_mem_integral
      (sub_mem_integralFiniteAdeles (hm 1 1) one_mem_integralFiniteAdeles) }

private theorem glFin_globalPoints_sl2ToQ_apply (ε : SL(2, ℤ)) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (sl2ToQ ε)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((ε i j : ℤ) : ℚ) := rfl

private theorem isLevelOneMatrix_top_sl2 (ε : SL(2, ℤ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ))
      (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (sl2ToQ ε)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  isLevelOneMatrix_top_of_integral fun i j => by
    rw [glFin_globalPoints_sl2ToQ_apply]; exact c3_intCast_mem_integralFiniteAdeles _

private theorem glFin_globalPoints_sl2ToQ_mem_finiteLevelOne_top (ε : SL(2, ℤ)) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (sl2ToQ ε)) ∈ finiteLevelOne (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)) := by
  refine ⟨isLevelOneMatrix_top_sl2 ε, ?_⟩
  rw [← map_inv, ← map_inv, sl2ToQ_inv]
  exact isLevelOneMatrix_top_sl2 ε⁻¹

private theorem idealBall_le_top (N : Ideal (𝓞 ℚ)) :
    idealBall (𝓞 ℚ) ℚ N ⊆ idealBall (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)) := fun _ hx w => by
  rw [NumberField.AdelicLevel.idealBound_top]
  exact (hx w).trans (NumberField.AdelicLevel.idealBound_le_one N w)

private theorem isLevelOneMatrix_top_of_isLevelOneMatrix {N : Ideal (𝓞 ℚ)}
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hm : IsLevelOneMatrix (𝓞 ℚ) ℚ N m) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)) m :=
  { integral := hm.integral
    lowerLeft := idealBall_le_top N hm.lowerLeft
    lowerRight := idealBall_le_top N hm.lowerRight }

private theorem finiteLevelOne_le_top (N : Ideal (𝓞 ℚ)) :
    finiteLevelOne (𝓞 ℚ) ℚ N ≤ finiteLevelOne (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)) := fun _ hg =>
  ⟨isLevelOneMatrix_top_of_isLevelOneMatrix hg.1, isLevelOneMatrix_top_of_isLevelOneMatrix hg.2⟩

private theorem U_le_U_top (N : Ideal (𝓞 ℚ)) :
    (productionPinsCompact ℚ).U N ≤ (productionPinsCompact ℚ).U ⊤ := fun _ hu =>
  ⟨finiteLevelOne_le_top N hu.1, hu.2⟩

private theorem twist_mem_U_top {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (twistQ hn v hv)))
      ∈ (productionPinsCompact ℚ).U ⊤ :=
  finPart_mem_U_top (glFin_globalPoints_sl2ToQ_mem_finiteLevelOne_top _)

private noncomputable def c3RatRep {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    Option (ZMod (Ideal.absNorm v.asIdeal)) → GL (Fin 2) ℚ
  | some c => ratHeckeRep (Ideal.absNorm v.asIdeal) (some c)
  | none => ratHeckeRep (Ideal.absNorm v.asIdeal) none * twistQ hn v hv

private noncomputable def c3Rep {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) (i : Option (ZMod (Ideal.absNorm v.asIdeal))) : 𝔾 :=
  finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (c3RatRep hn v hv i)))

private theorem c3Rep_some {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) (c : ZMod (Ideal.absNorm v.asIdeal)) :
    c3Rep hn v hv (some c) = adelicHeckeRep v (some c) := rfl

private theorem c3Rep_none {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    c3Rep hn v hv none = adelicHeckeRep v none
      * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (twistQ hn v hv))) := by
  unfold c3Rep adelicHeckeRep c3RatRep
  rw [map_mul, map_mul, map_mul]

private noncomputable def x0Z {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) : SL(2, ℤ) :=
  ⟨!![1, Classical.choose (exists_twist_data v hv);
      (n : ℤ), ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) * Classical.choose (Classical.choose_spec (exists_twist_data v hv))],
    by
      rw [Matrix.det_fin_two_of]
      have h := Classical.choose_spec (Classical.choose_spec (exists_twist_data v hv))
      linear_combination h⟩

private theorem x0Z_mem_Gamma1 {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) : x0Z v hv ∈ CongruenceSubgroup.Gamma1 n := by
  rw [CongruenceSubgroup.Gamma1_mem]
  have h := Classical.choose_spec (Classical.choose_spec (exists_twist_data v hv))
  refine ⟨?_, ?_, ?_⟩
  · show (((1 : ℤ)) : ZMod n) = 1
    exact Int.cast_one
  · show ((((Ideal.absNorm v.asIdeal : ℕ) : ℤ) * Classical.choose (Classical.choose_spec (exists_twist_data v hv)) : ℤ)
        : ZMod n) = 1
    rw [show ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) * Classical.choose (Classical.choose_spec (exists_twist_data v hv))
        = 1 + Classical.choose (exists_twist_data v hv) * (n : ℤ) by linear_combination h]
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero]
  · show (((n : ℤ)) : ZMod n) = 0
    exact_mod_cast ZMod.natCast_self n

private theorem ratRep_none_mul_twistQ {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Ideal.absNorm v.asIdeal).Prime] (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ratHeckeRep (Ideal.absNorm v.asIdeal) none * twistQ hn v hv
      = Matrix.SpecialLinearGroup.mapGL ℚ (x0Z v hv) * diagNat (Ideal.absNorm v.asIdeal) := by
  have htw : twistQ hn v hv = Matrix.SpecialLinearGroup.mapGL ℚ (twistZ v hv) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [twistQ, sl2ToQ_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    rfl
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [htw, Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagNat_apply, ratHeckeRep_none_apply, twistZ,
      x0Z, RingHom.mapMatrix_apply, Matrix.map_apply]
  all_goals ring

private theorem span_natCast_ne_bot {n : ℕ} (hn : n ≠ 0) : Ideal.span {(n : 𝓞 ℚ)} ≠ (⊥ : Ideal (𝓞 ℚ)) := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hn

private theorem algebraMap_mem_idealBall_of_mem {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) {r : 𝓞 ℚ} (hr : r ∈ N) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r) ∈ idealBall (𝓞 ℚ) ℚ N := by
  classical
  rw [← Ideal.iInf_maxPowDividing_eq hN, Ideal.mem_iInf] at hr
  intro w
  rw [show (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)) w
      = algebraMap ℚ (w.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ r) from rfl,
    NumberField.AdelicLevel.valued_algebraMap, NumberField.AdelicLevel.idealBound_of_ne_bot hN,
    IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
  exact hr w

private theorem intCast_mem_idealBall_span_of_dvd {n : ℕ} (hn : n ≠ 0) {k : ℤ} (hk : (n : ℤ) ∣ k) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (k : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  have hmem : (k : 𝓞 ℚ) ∈ Ideal.span {(n : 𝓞 ℚ)} := by
    rw [Ideal.mem_span_singleton]
    obtain ⟨m, hm⟩ := hk
    rw [hm]
    push_cast
    exact dvd_mul_right _ _
  have h := algebraMap_mem_idealBall_of_mem (span_natCast_ne_bot hn) hmem
  rwa [map_intCast] at h

private theorem glFin_globalPoints_mapGL_apply' (ε : SL(2, ℤ)) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((ε i j : ℤ) : ℚ) := rfl

private theorem isLevelOneMatrix_span_mapGL_of_mem_Gamma1 {n : ℕ} (hn : n ≠ 0) {ε : SL(2, ℤ)}
    (hε : ε ∈ CongruenceSubgroup.Gamma1 n) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  obtain ⟨-, hd, hc⟩ := (CongruenceSubgroup.Gamma1_mem n ε).mp hε
  have hc' : (n : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hc
  have hd' : (n : ℤ) ∣ ε 1 1 - 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp ?_
    rw [Int.cast_sub, Int.cast_one, hd, sub_self]
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · rw [glFin_globalPoints_mapGL_apply']
    exact intCast_mem_integralFiniteAdeles _
  · rw [glFin_globalPoints_mapGL_apply']
    exact intCast_mem_idealBall_span_of_dvd hn hc'
  · rw [glFin_globalPoints_mapGL_apply']
    have h := intCast_mem_idealBall_span_of_dvd hn hd'
    rwa [Int.cast_sub, Int.cast_one, map_sub, map_one] at h

private theorem glFin_globalPoints_mapGL_mem_finiteLevelOne_span {n : ℕ} (hn : n ≠ 0) {ε : SL(2, ℤ)}
    (hε : ε ∈ CongruenceSubgroup.Gamma1 n) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  rw [mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_span_mapGL_of_mem_Gamma1 hn hε, ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv]
  exact isLevelOneMatrix_span_mapGL_of_mem_Gamma1 hn (Subgroup.inv_mem _ hε)

private theorem mem_U_iff' (N : Ideal (𝓞 ℚ)) (u : 𝔾) :
    u ∈ (productionPinsCompact ℚ).U N ↔
      glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glArch (𝓞 ℚ) ℚ u = 1 :=
  Iff.rfl

private theorem finPart_globalPoints_mapGL_mem_U_span {n : ℕ} (hn : n ≠ 0) {ε : SL(2, ℤ)}
    (hε : ε ∈ CongruenceSubgroup.Gamma1 n) :
    finPart (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε))
      ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}) :=
  finPart_mem_U (glFin_globalPoints_mapGL_mem_finiteLevelOne_span hn hε)

private theorem unipZ_mem_Gamma1 (n : ℕ) (m : ℤ) : unipZ m ∈ CongruenceSubgroup.Gamma1 n := by
  refine (CongruenceSubgroup.Gamma1_mem n _).mpr ⟨?_, ?_, ?_⟩ <;> simp [unipZ]

private theorem isLevelOneMatrix_glFin_diagOne_finIncl' (N : Ideal (𝓞 ℚ)) {b : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ N
      (glFin (𝓞 ℚ) ℚ (diagOne (Units.map
          (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) b)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j
    · exact hb
    · exact zero_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
    · exact one_mem_integralFiniteAdeles
  · exact zero_mem_idealBall N
  · show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ idealBall (𝓞 ℚ) ℚ N
    rw [sub_self]; exact zero_mem_idealBall N

private theorem diagOne_finIncl_mem_U (N : Ideal (𝓞 ℚ)) {b : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hb' : ((b⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    diagOne (Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) b)
      ∈ (productionPinsCompact ℚ).U N := by
  refine (mem_U_iff' N _).mpr ⟨?_, glArch_diagOne_finIncl b⟩
  rw [mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_glFin_diagOne_finIncl' N hb, ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv]
  exact isLevelOneMatrix_glFin_diagOne_finIncl' N hb'

private theorem heckeGenAt_mem_heckeGen_mul' (N : Ideal (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    ∃ u ∈ (productionPinsCompact ℚ).U N, heckeGenAt (𝓞 ℚ) ℚ v t = heckeGen (𝓞 ℚ) ℚ v * u := by
  refine ⟨(heckeGen (𝓞 ℚ) ℚ v)⁻¹ * heckeGenAt (𝓞 ℚ) ℚ v t, ?_, by group⟩
  refine (mem_U_iff' N _).mpr ⟨heckeGen_inv_mul_heckeGenAt_mem_levelOne t ht N, ?_⟩
  rw [map_mul, map_inv, heckeGen, glArch_heckeGenAt,
    glArch_heckeGenAt, inv_one, one_mul]

private theorem finPart_diagNat_eq_mul_heckeGen_mul (N : Ideal (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ)
    [Fact p.Prime]
    (hv : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) = WithZero.exp (-1 : ℤ))
    (hw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ)) = 1) :
    ∃ E ∈ (productionPinsCompact ℚ).U N, ∃ u₀ ∈ (productionPinsCompact ℚ).U N,
      finPart (globalPoints (𝓞 ℚ) ℚ (diagNat p))
        = E * heckeGen (𝓞 ℚ) ℚ v * u₀ := by
  classical
  have h0 : algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) ≠ 0 := fun h => by
    rw [h, map_zero] at hv; exact WithZero.coe_ne_zero hv.symm
  set t : (v.adicCompletion ℚ)ˣ := Units.mk0 _ h0 with ht
  have htv : Valued.v (t : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := hv
  set b : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := natIdele p * (localUnit (𝓞 ℚ) ℚ v t)⁻¹ with hbdef
  have hb : (b : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro w
    rw [hbdef, Units.val_mul, ← map_inv, finiteAdele_mul_apply,
      natIdele_apply]
    by_cases hwv : w = v
    · subst hwv
      rw [localUnit_apply_self, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ h0]
      exact one_mem _
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hwv, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers, hw w hwv]
  have hb' : ((b⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro w
    rw [hbdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, finiteAdele_mul_apply,
      natIdele_inv_apply]
    by_cases hwv : w = v
    · subst hwv
      rw [localUnit_apply_self, Units.val_mk0, map_inv₀, mul_inv_cancel₀ h0]
      exact one_mem _
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hwv, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
        map_inv₀, hw w hwv, inv_one]
  set E : 𝔾 := diagOne (Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) b) with hE
  have hEU : E ∈ (productionPinsCompact ℚ).U N :=
    diagOne_finIncl_mem_U N hb hb'
  have hD : finPart (globalPoints (𝓞 ℚ) ℚ (diagNat p))
      = E * heckeGenAt (𝓞 ℚ) ℚ v t := by
    rw [finPart_globalPoints_diagNat, hE, heckeGenAt, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ← map_mul, ← map_mul, hbdef, inv_mul_cancel_right]
  obtain ⟨u₀, hu₀, hgen⟩ := heckeGenAt_mem_heckeGen_mul' N v t htv
  exact ⟨E, hEU, u₀, hu₀, by rw [hD, hgen, mul_assoc]⟩

private theorem c3RatRep_eq_mapGL_mul_diagNat {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Ideal.absNorm v.asIdeal).Prime] (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (i : Option (ZMod (Ideal.absNorm v.asIdeal))) :
    ∃ γ ∈ CongruenceSubgroup.Gamma1 n, c3RatRep hn v hv i
      = Matrix.SpecialLinearGroup.mapGL ℚ γ * diagNat (Ideal.absNorm v.asIdeal) := by
  cases i with
  | some c =>
      exact ⟨_, unipZ_mem_Gamma1 n _, ratHeckeRep_some_eq (Ideal.absNorm v.asIdeal) c⟩
  | none =>
      exact ⟨_, x0Z_mem_Gamma1 v hv, ratRep_none_mul_twistQ hn v hv⟩

private theorem c3Rep_mem_doubleCoset {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) (i : Option (ZMod (Ideal.absNorm v.asIdeal))) :
    c3Rep hn v hv i ∈ HeckePair.doubleCoset ((productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}))
      ((productionPinsCompact ℚ).gen v) := by
  obtain ⟨γ, hγ, hfac⟩ := c3RatRep_eq_mapGL_mul_diagNat hn v hv i
  have hrep : c3Rep hn v hv i
      = finPart (globalPoints (𝓞 ℚ) ℚ (c3RatRep hn v hv i)) := rfl
  have hmul : ∀ x y : GL (Fin 2) ℚ, finPart (globalPoints (𝓞 ℚ) ℚ (x * y))
      = finPart (globalPoints (𝓞 ℚ) ℚ x)
        * finPart (globalPoints (𝓞 ℚ) ℚ y) := by
    intro x y
    simp only [finPart, map_mul]
  obtain ⟨E, hE, u₀, hu₀, hD⟩ := finPart_diagNat_eq_mul_heckeGen_mul (Ideal.span {(n : 𝓞 ℚ)}) v
    (Ideal.absNorm v.asIdeal) (valued_algebraMap_absNorm_self v)
    (fun _ hw => valued_algebraMap_absNorm_of_ne v hw)
  rw [hrep, hfac, hmul, hD, HeckePair.mem_doubleCoset_iff, productionPinsCompact_gen]
  exact ⟨finPart (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) * E,
    Subgroup.mul_mem _ (finPart_globalPoints_mapGL_mem_U_span hn hγ) hE, u₀, hu₀, by group⟩

private theorem mk_c3Rep_injective {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    Function.Injective (fun i => (QuotientGroup.mk (c3Rep hn v hv i) :
      𝔾 ⧸ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}))) := by
  intro i j hij
  apply mk_adelicHeckeRep_injective v

  have key : ∀ k, ∃ t ∈ (productionPinsCompact ℚ).U ⊤,
      c3Rep hn v hv k = adelicHeckeRep v k * t := by
    intro k
    rcases k with _ | c
    · exact ⟨_, twist_mem_U_top hn v hv, c3Rep_none hn v hv⟩
    · exact ⟨1, one_mem _, by rw [c3Rep_some, mul_one]⟩
  obtain ⟨ti, hti, hi⟩ := key i
  obtain ⟨tj, htj, hj⟩ := key j
  have hmem : (c3Rep hn v hv i)⁻¹ * c3Rep hn v hv j ∈ (productionPinsCompact ℚ).U ⊤ :=
    U_le_U_top _ (QuotientGroup.eq.mp hij)
  rw [hi, hj, _root_.mul_inv_rev] at hmem

  have h2 : ti * (ti⁻¹ * (adelicHeckeRep v i)⁻¹
      * (adelicHeckeRep v j * tj)) * tj⁻¹ ∈ (productionPinsCompact ℚ).U ⊤ :=
    mul_mem (mul_mem hti hmem) (inv_mem htj)
  have h3 : ti * (ti⁻¹ * (adelicHeckeRep v i)⁻¹
      * (adelicHeckeRep v j * tj)) * tj⁻¹
      = (adelicHeckeRep v i)⁻¹ * adelicHeckeRep v j := by
    group
  rw [h3] at h2
  exact QuotientGroup.eq.mpr h2

private theorem c3_lift_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : 𝔾) (γ : GL (Fin 2) ℚ) (h u : 𝔾)
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hfin : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) :=
  weightOneLift_eq hn f hf g γ h u hu hfin hpos hg

private theorem ratArchGL2_eq_ratArch' (g : 𝔾) : LanglandsTunnell.ratArchGL2 g = ratArch g := rfl

private theorem sl2ToQ_eq_mapGL (ε : SL(2, ℤ)) : sl2ToQ ε = Matrix.SpecialLinearGroup.mapGL ℚ ε := rfl

private theorem sigma_apply_of_det_pos (x : GL (Fin 2) ℝ) (hx : 0 < x.det.val) (c : ℂ) : σ x c = c := by
  have hx' : 0 < (x : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  simp [σ, hx']

private theorem weightOneArchLift_mul_of_det (p : ℕ) (f : ℍ → ℂ) (m x : GL (Fin 2) ℝ)
    (hm : m.det.val = ((p : ℝ))⁻¹) :
    weightOneArchLift f (m * x)
      = ((f ∣[(1 : ℤ)] m) ∣[(1 : ℤ)] x) UpperHalfPlane.I * ((((p : ℝ))⁻¹ * x.det.val : ℝ) : ℂ) := by
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, map_mul, Units.val_mul, hm, zpow_one]

private theorem c3_lift_mul_c3Rep_of_inv {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Ideal.absNorm v.asIdeal).Prime] (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {h : 𝔾} (hfin : glFin (𝓞 ℚ) ℚ h = 1) (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (i : Option (ZMod (Ideal.absNorm v.asIdeal))) {m : GL (Fin 2) ℝ}
    (hm : (ratArch (globalPoints (𝓞 ℚ) ℚ (c3RatRep hn v hv i)))⁻¹ = m)
    (hmdet : m.det.val = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (h * c3Rep hn v hv i)
      = ((f ∣[(1 : ℤ)] m) ∣[(1 : ℤ)] ratArch h) UpperHalfPlane.I
          * (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ * (ratArch h).det.val : ℝ) : ℂ) := by
  have hApos : 0 < (ratArch h).det.val := (Matrix.mem_glpos _).mp hpos
  have hmpos : 0 < m.det.val := by
    rw [hmdet]
    exact inv_pos.mpr (Nat.cast_pos.mpr (Fact.out : (Ideal.absNorm v.asIdeal).Prime).pos)
  set P := globalPoints (𝓞 ℚ) ℚ (c3RatRep hn v hv i) with hP
  have hrep1 : ratArch (c3Rep hn v hv i) = 1 :=
    ratArch_eq_one_of_glArch_eq_one (by unfold c3Rep; exact AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)
  have harch : ratArch (P⁻¹ * h * c3Rep hn v hv i) = m * ratArch h := by
    rw [ratArch_mul, ratArch_mul, ratArch_inv, hm, hrep1, mul_one]
  have hglfin : glFin (𝓞 ℚ) ℚ (P⁻¹ * h * c3Rep hn v hv i) = 1 := by
    rw [map_mul, map_mul, map_inv, hfin, mul_one]
    unfold c3Rep
    rw [AdelicDock.glFin_finEmbed (𝓞 ℚ) ℚ _, inv_mul_cancel]
  have hmid : LanglandsTunnell.ratArchGL2 (P⁻¹ * h * c3Rep hn v hv i) ∈ GLPos (Fin 2) ℝ := by
    rw [ratArchGL2_eq_ratArch', harch, Matrix.mem_glpos, map_mul, Units.val_mul]
    exact mul_pos hmpos hApos
  have hdec : h * c3Rep hn v hv i = P * (P⁻¹ * h * c3Rep hn v hv i) * 1 := by group
  rw [c3_lift_eq hn f hf _ _ _ 1 (Subgroup.one_mem _) hglfin hmid hdec, ratArchGL2_eq_ratArch', harch,
    weightOneArchLift_mul_of_det _ f _ _ hmdet]

private theorem c3_ratArch_some_inv {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Ideal.absNorm v.asIdeal).Prime] (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (c : ZMod (Ideal.absNorm v.asIdeal)) :
    (ratArch (globalPoints (𝓞 ℚ) ℚ (c3RatRep hn v hv (some c))))⁻¹
      = heckeArchFin (Ideal.absNorm v.asIdeal) (ZMod.val c : ℤ) := by
  show (ratArch (globalPoints (𝓞 ℚ) ℚ (ratHeckeRep (Ideal.absNorm v.asIdeal) (some c))))⁻¹ = _
  rw [ratArch_globalPoints]
  exact mapGL_ratHeckeRep_some_inv (Ideal.absNorm v.asIdeal) c

private theorem coe_sl2_inv (ε : SL(2, ℤ)) : ((ε⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (ε : GL (Fin 2) ℝ)⁻¹ := by
  simp

private theorem c3_ratArch_none_inv {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Ideal.absNorm v.asIdeal).Prime] (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    (ratArch (globalPoints (𝓞 ℚ) ℚ (c3RatRep hn v hv none)))⁻¹
      = (((twistZ v hv)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeArchInf (Ideal.absNorm v.asIdeal) := by
  have h₁ : (ratArch (globalPoints (𝓞 ℚ) ℚ (ratHeckeRep (Ideal.absNorm v.asIdeal) none)))⁻¹
      = heckeArchInf (Ideal.absNorm v.asIdeal) := by
    rw [ratArch_globalPoints]
    exact mapGL_ratHeckeRep_none_inv (Ideal.absNorm v.asIdeal)
  have h₂ : ratArch (globalPoints (𝓞 ℚ) ℚ (twistQ hn v hv)) = ((twistZ v hv : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    unfold twistQ
    rw [sl2ToQ_eq_mapGL, ratArch_globalPoints_mapGL]
  show (ratArch (globalPoints (𝓞 ℚ) ℚ (ratHeckeRep (Ideal.absNorm v.asIdeal) none * twistQ hn v hv)))⁻¹ = _
  rw [map_mul, ratArch_mul, _root_.mul_inv_rev, h₁, h₂, coe_sl2_inv]

private theorem det_twist_inv_mul_heckeArchInf {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Ideal.absNorm v.asIdeal).Prime] (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ((((twistZ v hv)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeArchInf (Ideal.absNorm v.asIdeal)).det.val
      = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
  rw [map_mul, Units.val_mul]
  have h1 : ((((twistZ v hv)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)).det.val = 1 := by simp
  rw [h1, one_mul, det_heckeArchInf]

private theorem twistZ_inv_apply_one_one {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ((twistZ v hv)⁻¹ : SL(2, ℤ)) 1 1 = ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

private theorem slash_heckeArchFin_apply (p : ℕ) [Fact p.Prime] (f : ℍ → ℂ) (j : ℤ) (z : ℍ) :
    (f ∣[(1 : ℤ)] heckeArchFin p j) z = f (heckeArchFin p j • z) := by
  rw [ModularForm.slash_apply, denom_heckeArchFin, σ_heckeArchFin]
  simp

private theorem slash_heckeArchInf_apply (p : ℕ) [Fact p.Prime] (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[(1 : ℤ)] heckeArchInf p) z = (p : ℂ) * f (heckeArchInf p • z) := by
  rw [ModularForm.slash_apply, denom_heckeArchInf, σ_heckeArchInf]
  simp [mul_comm]

private theorem c3_f_int_vadd {n : ℕ} (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (m : ℤ) (w : ℍ) : f ((m : ℝ) +ᵥ w) = f w := by
  have hT : ModularGroup.T ^ m ∈ CongruenceSubgroup.Gamma1 n := by
    rw [CongruenceSubgroup.Gamma1_mem, ModularGroup.coe_T_zpow]
    simp
  have h := congr_fun (hf _ hT) w
  have hden : denom (((ModularGroup.T ^ m : SL(2, ℤ)) : GL (Fin 2) ℝ)) w = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]
    simp
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, modular_T_zpow_smul, hden, _root_.one_zpow,
    mul_one] at h
  exact h

private theorem sum_f_heckeArchFin_smul {n : ℕ} (p : ℕ) [hp : Fact p.Prime] (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) (z : ℍ) :
    ∑ c : ZMod p, f (heckeArchFin p (ZMod.val c : ℤ) • z)
      = ∑ j ∈ Finset.range p, f (ModularForm.heckeMatrix p j • z) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hterm : ∀ c : ZMod p,
      f (heckeArchFin p (ZMod.val c : ℤ) • z) = f (ModularForm.heckeMatrix p (ZMod.val (-c)) • z) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      rw [← c3_f_int_vadd f hf 0 (ModularForm.heckeMatrix p (ZMod.val (-(0 : ZMod p))) • z)]
      congr 1
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_vadd, coe_heckeArchFin_smul, ModularForm.coe_heckeMatrix_smul hp.out.ne_zero]
      simp
    · rw [← c3_f_int_vadd f hf (-1) (ModularForm.heckeMatrix p (ZMod.val (-c)) • z)]
      congr 1
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_vadd, coe_heckeArchFin_smul, ModularForm.coe_heckeMatrix_smul hp.out.ne_zero,
        ZMod.neg_val, ite_eq_right hc, Nat.cast_sub (ZMod.val_lt c).le]
      push_cast
      field_simp
      ring
  simp_rw [hterm]

  rw [← Fin.sum_univ_eq_sum_range (fun j => f (ModularForm.heckeMatrix p j • z)) p]
  exact Fintype.sum_bijective (fun c : ZMod p => (⟨ZMod.val (-c), ZMod.val_lt (-c)⟩ : Fin p))
    ⟨fun c₁ c₂ hc => neg_injective (ZMod.val_injective _ (Fin.mk.inj hc)),
     fun j => ⟨-((j : ℕ) : ZMod p), Fin.ext (by simp [ZMod.val_natCast_of_lt j.isLt])⟩⟩ _ _ (fun c => rfl)

private theorem heckeArchInf_smul_eq_heckeDiagMatrix_smul (p : ℕ) [hp : Fact p.Prime] (z : ℍ) :
    heckeArchInf p • z = ModularForm.heckeDiagMatrix p • z := by
  apply UpperHalfPlane.ext
  rw [coe_heckeArchInf_smul, ModularForm.coe_heckeDiagMatrix_smul hp.out.ne_zero]

private theorem c3_heckeSlashSum_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) [hp : Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (a : ℂ)
    (hTv : ModularForm.heckeU 1 (Ideal.absNorm v.asIdeal) f
        + χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) •
            (f ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
      = a • f) :
    f ∣[(1 : ℤ)] ((((twistZ v hv)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeArchInf (Ideal.absNorm v.asIdeal))
        + ∑ c : ZMod (Ideal.absNorm v.asIdeal), f ∣[(1 : ℤ)] heckeArchFin (Ideal.absNorm v.asIdeal) (ZMod.val c : ℤ)
      = (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * a) • f := by
  have hp0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  have hκ : f ∣[(1 : ℤ)] ((((twistZ v hv)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeArchInf (Ideal.absNorm v.asIdeal))
      = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) • (f ∣[(1 : ℤ)] heckeArchInf (Ideal.absNorm v.asIdeal)) := by
    rw [SlashAction.slash_mul, hχ _ (Subgroup.inv_mem _ (twistZ_mem_Gamma0 v hv)), twistZ_inv_apply_one_one,
      Int.cast_natCast, ModularForm.smul_slash, σ_heckeArchInf]
  rw [hκ]
  funext z
  have hU := congr_fun hTv z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hU ⊢
  rw [ModularForm.heckeU_apply 1 hp.out.ne_zero, ModularForm.slash_heckeDiagMatrix_apply 1 hp.out.ne_zero,
    sub_self, zpow_zero, one_mul] at hU
  rw [slash_heckeArchInf_apply, heckeArchInf_smul_eq_heckeDiagMatrix_smul]
  simp_rw [slash_heckeArchFin_apply]
  rw [sum_f_heckeArchFin_smul (Ideal.absNorm v.asIdeal) f hf z, mul_assoc ((Ideal.absNorm v.asIdeal : ℕ) : ℂ),
    ← hU, mul_add, mul_inv_cancel_left₀ hp0, add_comm, mul_left_comm]

private theorem sum_weightOneLift_mul_c3Rep {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (Ideal.absNorm v.asIdeal).Prime]
    (hv : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (a : ℂ)
    (hTv : ModularForm.heckeU 1 (Ideal.absNorm v.asIdeal) f
        + χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) •
            (f ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
      = a • f)
    (h : 𝔾) (hfin : glFin (𝓞 ℚ) ℚ h = 1) (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ) :
    ∑ i : Option (ZMod (Ideal.absNorm v.asIdeal)),
        weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (h * c3Rep hn v hv i)
      = a * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f h := by
  have hp0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : (Ideal.absNorm v.asIdeal).Prime).ne_zero
  have hApos : 0 < (ratArch h).det.val := (Matrix.mem_glpos _).mp hpos

  have hLh : weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f h
      = weightOneArchLift f (ratArch h) :=
    c3_lift_eq hn f hf h 1 h 1 (Subgroup.one_mem _) hfin hpos (by rw [map_one, one_mul, mul_one])

  have hsome : ∀ c : ZMod (Ideal.absNorm v.asIdeal),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (h * c3Rep hn v hv (some c))
        = ((f ∣[(1 : ℤ)] heckeArchFin (Ideal.absNorm v.asIdeal) (ZMod.val c : ℤ))
              ∣[(1 : ℤ)] ratArch h) UpperHalfPlane.I
            * (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ * (ratArch h).det.val : ℝ) : ℂ) :=
    fun c => c3_lift_mul_c3Rep_of_inv hn v hv f hf hfin hpos (some c) (c3_ratArch_some_inv hn v hv c)
      (det_heckeArchFin _ _)
  have hnone : weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (h * c3Rep hn v hv none)
        = ((f ∣[(1 : ℤ)] ((((twistZ v hv)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)
                * heckeArchInf (Ideal.absNorm v.asIdeal)))
              ∣[(1 : ℤ)] ratArch h) UpperHalfPlane.I
            * (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ * (ratArch h).det.val : ℝ) : ℂ) :=
    c3_lift_mul_c3Rep_of_inv hn v hv f hf hfin hpos none (c3_ratArch_none_inv hn v hv)
      (det_twist_inv_mul_heckeArchInf v hv)
  rw [Fintype.sum_option, hnone]
  simp_rw [hsome]

  rw [← Finset.sum_mul, ← add_mul, ← Finset.sum_apply, ← Pi.add_apply, ← SlashAction.sum_slash,
    ← SlashAction.add_slash, c3_heckeSlashSum_eq v hv f hf χ hχ a hTv, ModularForm.smul_slash,
    sigma_apply_of_det_pos _ hApos, Pi.smul_apply, smul_eq_mul, hLh]
  unfold weightOneArchLift
  rw [zpow_one]
  push_cast
  field_simp

end

theorem isHeckeCosetEigenfunctionAt_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ) (hΦ : Φ.level = Ideal.span {(n : 𝓞 ℚ)})
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ModularForm.heckeU 1 (Ideal.absNorm v.asIdeal) f
          + χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) •
              (f ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = Φ.a v • f) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      IsHeckeCosetEigenfunctionAt ℚ ((productionPinsCompact ℚ).U Φ.level)
        ((productionPinsCompact ℚ).gen v) v (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) (Φ.a v) := by
  intro v hv
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨c3_absNorm_prime v⟩
  have hvn : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)} := hS v hv
  rw [hΦ]
  obtain ⟨reps, hsys⟩ :=
    LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd
      (Ideal.span {(n : 𝓞 ℚ)}) v hvn
  refine ⟨reps, hsys, fun g => ?_⟩
  unfold heckeCosetSum
  obtain ⟨γ, h, u, hu, hfin, hpos, heq⟩ := c3_exists_decomp hn g
  have hinv : ∀ x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ), ∀ u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (x * u₀) = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f x :=
    fun x _ hu₀ => c3_lift_mul_of_mem_U hn f hf x hu₀
  simp only [heq, mul_assoc, c3_lift_globalPoints_mul hn f hf]
  rw [(sum_mul_left_eq hsys) _ hinv h u hu,
    ← (sum_cross_eq hsys) (c3Rep_mem_doubleCoset hn v hvn) (mk_c3Rep_injective hn v hvn)
      (card_option_zmod_absNorm v) _ hinv h,
    sum_weightOneLift_mul_c3Rep hn v hvn f hf χ hχ (Φ.a v) (hT v hv) h hfin hpos,
    c3_lift_mul_of_mem_U hn f hf h hu]

end LanglandsTunnell

end
