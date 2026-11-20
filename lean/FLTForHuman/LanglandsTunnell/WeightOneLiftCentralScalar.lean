/-
  The central character of the weight-one lift.

  Along the centre `Z` the lift transforms by the idèle-class character attached to `(χ, ‖·‖)` — the
  Dirichlet character read on idèle classes (`DirichletCharacter.dirichletIdeleChar`, ported in
  `NumberTheory/RatIdele/UnitResidue.lean`) times the normalized absolute value.

  Transcribed from `P2M/Sol/S_LanglandsTunnell_weightOneLift_centralScalar_mul.lean` (pinned
  `aa2d8b3`, 1,135 lines / 100 declarations). The shared adelic prelude lives in
  `WeightOneLiftAdelic`; this module carries the row and the pin's row-local declarations at the
  pin's names and statements.

  spec-pin: P2M/Sol/S_LanglandsTunnell_weightOneLift_centralScalar_mul.lean

  ## Port deltas

  - Namespace flattening only. The pin states the engine `private` in its search-stage
    `P2GProbe.C1`; here it sits at `LanglandsTunnell`, so the pin's `R1.`/`R3.`/`R4a.`/`R7.`
    qualifiers on prelude references (`weightOneArchLift_def`,
    `weightOneArchLift_scalar_mul`, `hasWeightOneDecomp_of_ne_bot`, `weightOneLift_eq`,
    `weightOneLift_globalPoints_mul`, `mem_U_iff`, `weightOneLift_mul_eq`,
    `ratArchGL2_eq_ratArch`) are dropped: those declarations are `WeightOneLiftAdelic`'s, public
    there. `det_coe_SL` — the one declaration of the pin's `:589`–`:1116` block not repeated here
    — is that prelude's too (pin `:981`).
  - `centralScalar_comm` keeps the pin's statement and takes its body from the port's one home of
    the fact, `AutomorphicForm.centralScalar_mul_comm` (the pin re-proves it inline; the two
    propositions are the same).
  - Three body-level substitutions, all statement-neutral:
    * `if_pos`/`if_neg` are `ite_eq_left`/`ite_eq_right` at mathlib `v4.34.0` (FR-0238's rename
      class; the deprecated spellings would emit a warning and break the silence gate).
    * the pin's `simp [twistMat, Matrix.SpecialLinearGroup.SL2_inv_expl]` no longer reaches the
      coerced inverse at `v4.34.0` (the lemma's own proof carries
      `backward.isDefEq.respectTransparency false`); `rw [Matrix.SpecialLinearGroup.SL2_inv_expl]`
      then `rfl` yields the same two entries.
    * `haveI : Fact (P : ℕ).Prime := ⟨P.2⟩` is spelled `have` in
      `exists_unitAt_sub_residue_eq` (the style linter rejects `haveI` on a proposition goal; the
      local hypothesis still serves as the instance).

  ## Deferred pin surface

  None. `move_dead.py` reports 0 declarations / 0 lines, and each of the pin block's 56
  declarations is either transcribed here (55) or the shared prelude's (`det_coe_SL`).

  ## Gates

  - `check_port` — 1 ok, 0 mismatch, 0 missing, 0 own (the row at pin `:1116`; the 54 `private`
    engine declarations are off the wire). `scaffold_audit` **complete**, 55 port declarations.
  - Silent at the project cap and under `-DmaxHeartbeats=8000`.
  - `#print axioms` on all 55 — `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
  - `dedup --within` reports **one `shape` cluster (5 lines)**, and it stays: the pin's own pair
    `twistMat_inv_apply_10` (pin `:899`) / `twistMat_inv_apply_11` (`:903`), two distinct
    statements (the `(1,0)` and `(1,1)` entries of the twisted inverse), both with consumers in
    `glFin_twist_mem_finiteLevelOne`'s two `finiteLevelOne` halves. The duplication is the pin's,
    not the port's.
  - Heartbeat probe (never installed, FR-0225): silent at `-DmaxHeartbeats=8000`; first failure at
    `7000` (`deterministic timeout at whnf`, in `weightOneLift_centralScalar_mul_eq`), so the
    heaviest declaration costs ≈7–8 k. No `set_option maxHeartbeats` is carried.
-/


import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
import FLTForHuman.NumberTheory.RatIdele.UnitResidue
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsTail
import FLTForHuman.ModularForms.Analytic.NormSqPow
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Topology
import FLTForHuman.AutomorphicForm.Adelic.ConstantTermUnipotent

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
open CuspForm ModularFormClass ModularForm
open LanglandsTunnell.RatArch

open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne RatIdele Rat.HeightOneSpectrum
local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)
local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ


namespace LanglandsTunnell

open RatArch DetIntegral ArchLift



private def rhoUnit (x : (𝔸ℚ)ˣ) : ℚˣ := Units.mk0 (RatIdele.ρ x) (ρ_ne_zero x)

private theorem coe_rhoUnit (x : (𝔸ℚ)ˣ) : ((rhoUnit x : ℚˣ) : ℚ) = RatIdele.ρ x := rfl

private def principal (q : ℚˣ) : (𝔸ℚ)ˣ := Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q

private def unitPart (x : (𝔸ℚ)ˣ) : (𝔸ℚ)ˣ := (principal (rhoUnit x))⁻¹ * x

private theorem principal_mul_unitPart (x : (𝔸ℚ)ˣ) : principal (rhoUnit x) * unitPart x = x :=
  mul_inv_cancel_left _ _

private theorem rho_principal' (q : ℚˣ) : RatIdele.ρ (principal q) = (q : ℚ) := ρ_principal q

private theorem rho_inv_principal (q : ℚˣ) : RatIdele.ρ (principal q)⁻¹ = ((q : ℚ))⁻¹ := by
  have h := ρ_mul (principal q)⁻¹ (principal q)
  rw [inv_mul_cancel, ρ_one, rho_principal'] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private theorem rho_unitPart (x : (𝔸ℚ)ˣ) : RatIdele.ρ (unitPart x) = 1 := by
  unfold unitPart
  rw [ρ_mul, rho_inv_principal, coe_rhoUnit, inv_mul_cancel₀ (ρ_ne_zero x)]

private theorem principal_inv (q : ℚˣ) : (principal q)⁻¹ = principal q⁻¹ :=
  (map_inv (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ)) q).symm

private theorem unitResidue_unitPart (n : ℕ) [NeZero n] (x : (𝔸ℚ)ˣ) :
    unitResidue n (unitPart x) = unitResidue n x := by
  unfold unitPart
  rw [map_mul, principal_inv, principal, unitResidue_principal, one_mul]

private theorem archCoord_unitPart_pos (x : (𝔸ℚ)ˣ) : 0 < archCoord (unitPart x) := by
  have h := (ρ_spec (unitPart x)).2
  rwa [rho_unitPart, Rat.cast_one, mul_one] at h

private theorem snd_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((unitPart x : 𝔸ℚ)).2 v = unitAt v (unitPart x) := by
  unfold RatIdele.unitAt
  rw [rho_unitPart, map_one, inv_one, mul_one]

private theorem valued_snd_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((unitPart x : 𝔸ℚ)).2 v) = 1 := by
  rw [snd_unitPart]; exact valued_unitAt v (unitPart x)

private theorem valued_snd_inv_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v) = 1 := by
  have h := valued_snd_inv_mul (unitPart x) v
  rwa [valued_snd_unitPart, mul_one] at h

private theorem snd_unitPart_mem_integral (x : (𝔸ℚ)ˣ) :
    ((unitPart x : 𝔸ℚ)).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun v =>
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (valued_snd_unitPart x v).le

private theorem snd_inv_unitPart_mem_integral (x : (𝔸ℚ)ˣ) :
    (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun v =>
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (valued_snd_inv_unitPart x v).le

private theorem snd_unitPart_mul_snd_inv (x : (𝔸ℚ)ˣ) :
    ((unitPart x : 𝔸ℚ)).2 * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = 1 := by
  show ((unitPart x : 𝔸ℚ) * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ)).2 = (1 : 𝔸ℚ).2
  rw [Units.mul_inv]

private theorem distribHaarChar_eq_unitPart
    (hprin : ∀ q : ℚˣ,
      MeasureTheory.distribHaarChar 𝔸ℚ (Units.map (algebraMap ℚ 𝔸ℚ).toMonoidHom q) = 1)
    (x : (𝔸ℚ)ˣ) :
    MeasureTheory.distribHaarChar 𝔸ℚ x = MeasureTheory.distribHaarChar 𝔸ℚ (unitPart x) := by
  have h1 : MeasureTheory.distribHaarChar 𝔸ℚ (principal (rhoUnit x)) = 1 := hprin (rhoUnit x)
  conv_lhs => rw [← principal_mul_unitPart x]
  rw [map_mul, h1, one_mul]

private theorem norm_snd_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ‖((unitPart x : 𝔸ℚ)).2 v‖ = 1 := by
  rw [FinitePlace.norm_def, valued_snd_unitPart, map_one, NNReal.coe_one]

private theorem norm_fst_unitPart (x : (𝔸ℚ)ˣ) :
    ‖((unitPart x : 𝔸ℚ)).1 Rat.infinitePlace‖ = archCoord (unitPart x) := by
  have hiso := (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).isometry
  have h0 : InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
  rw [← hiso.norm_map_of_map_zero h0, Real.norm_eq_abs]
  exact abs_of_pos (archCoord_unitPart_pos x)

private theorem coe_distribHaarChar_unitPart
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (x : (𝔸ℚ)ˣ) :
    (MeasureTheory.distribHaarChar 𝔸ℚ (unitPart x) : ℝ) = archCoord (unitPart x) := by
  rw [hprod (unitPart x),
    finprod_eq_one_of_forall_eq_one (norm_snd_unitPart x), mul_one, Fintype.prod_unique,
    show (default : InfinitePlace ℚ) = Rat.infinitePlace from Subsingleton.elim _ _, norm_fst_unitPart]
  have hmult : (Rat.infinitePlace).mult = 1 := by
    simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
  rw [hmult, pow_one]

private theorem coe_distribHaarChar_eq_archCoord
    (hprin : ∀ q : ℚˣ,
      MeasureTheory.distribHaarChar 𝔸ℚ (Units.map (algebraMap ℚ 𝔸ℚ).toMonoidHom q) = 1)
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (x : (𝔸ℚ)ˣ) :
    (MeasureTheory.distribHaarChar 𝔸ℚ x : ℝ) = archCoord (unitPart x) := by
  rw [distribHaarChar_eq_unitPart hprin, coe_distribHaarChar_unitPart hprod]

private theorem valued_natCast_eq_idealBound {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = idealBound (𝓞 ℚ) (Ideal.span {(n : 𝓞 ℚ)}) v := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have hn' : (n : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hn
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg hn', idealBound_of_ne_bot hN]

private theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (d : ℕ) :
    Valued.v ((d : ℕ) : v.adicCompletion ℚ) ≤ 1 := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    show ((d : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (d : 𝓞 ℚ) from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one v _

private theorem natCast_level_eq (n : ℕ) (P : Nat.Primes) :
    ((n : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
      = (((P : ℕ) ^ n.factorization (P : ℕ) : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
        * ((n / (P : ℕ) ^ n.factorization (P : ℕ) : ℕ)
          : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) := by
  rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self n (P : ℕ)]

private theorem valued_ordCompl_eq_one {n : ℕ} (hn : n ≠ 0) (P : Nat.Primes) :
    Valued.v ((n / (P : ℕ) ^ n.factorization (P : ℕ) : ℕ)
      : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) = 1 := by
  rw [← map_natCast (algebraMap ℚ (((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)),
    valued_algebraMap_rat]
  exact valuation_natCast_of_not_dvd _
    (by rw [natGenerator_primesEquiv_symm]; exact Nat.not_dvd_ordCompl P.2 hn)

private theorem toZModPow_unitPadicAt (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ) (P : Nat.Primes)
    [Fact (P : ℕ).Prime] (hPmem : (P : ℕ) ∈ n.primeFactors) :
    PadicInt.toZModPow (n.factorization (P : ℕ)) (unitPadicAt (P : ℕ) y)
      = (((unitResidue n y).val : ℕ) : ZMod ((P : ℕ) ^ n.factorization (P : ℕ))) := by
  have h1 : ZMod.equivPi n (NeZero.ne n) ((((unitResidue n y).val : ℕ) : ZMod n))
      = unitResidues n y := by
    rw [ZMod.natCast_zmod_val, equivPi_unitResidue]
  rw [map_natCast] at h1
  have h2 := congrFun h1 ⟨(P : ℕ), hPmem⟩
  rw [Pi.natCast_apply] at h2
  exact h2.symm

private theorem exists_unitPadicAt_sub_eq (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ) (P : Nat.Primes)
    [Fact (P : ℕ).Prime] (hPmem : (P : ℕ) ∈ n.primeFactors) :
    ∃ c : ℤ_[(P : ℕ)], unitPadicAt (P : ℕ) y - (((unitResidue n y).val : ℕ) : ℤ_[(P : ℕ)])
      = (((P : ℕ) ^ n.factorization (P : ℕ) : ℕ) : ℤ_[(P : ℕ)]) * c := by
  have hker : unitPadicAt (P : ℕ) y - (((unitResidue n y).val : ℕ) : ℤ_[(P : ℕ)])
      ∈ RingHom.ker (PadicInt.toZModPow (p := (P : ℕ)) (n.factorization (P : ℕ))) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, toZModPow_unitPadicAt n y P hPmem, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨c, hc⟩ := hker
  exact ⟨c, by rw [Nat.cast_pow]; exact hc⟩

private noncomputable abbrev padicToCompletion (P : Nat.Primes) [Fact (P : ℕ).Prime] :
    ℤ_[(P : ℕ)] →+* ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ :=
  (((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletionIntegers ℚ).subtype.comp
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P).toAlgEquiv.toRingEquiv.toRingHom

private theorem padicToCompletion_unitPadicAt (y : (𝔸ℚ)ˣ) (P : Nat.Primes) :
    haveI : Fact (P : ℕ).Prime := ⟨P.2⟩
    padicToCompletion P (unitPadicAt (P : ℕ) y) = unitAt ((primesEquiv (R := 𝓞 ℚ)).symm P) y := by
  unfold unitPadicAt
  show (((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P)
      ((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P).symm
        (unitIntAt ((primesEquiv (R := 𝓞 ℚ)).symm P) y))
      : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletionIntegers ℚ)
      : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) = _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  exact coe_unitIntAt _ y

private theorem exists_unitAt_sub_residue_eq (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ) (P : Nat.Primes)
    (hPmem : (P : ℕ) ∈ n.primeFactors) :
    ∃ z : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletionIntegers ℚ,
      unitAt ((primesEquiv (R := 𝓞 ℚ)).symm P) y
          - (((unitResidue n y).val : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
        = (((P : ℕ) ^ n.factorization (P : ℕ) : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
            * (z : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) := by
  have hprime : Fact (P : ℕ).Prime := ⟨P.2⟩
  obtain ⟨c, hc⟩ := exists_unitPadicAt_sub_eq n y P hPmem
  refine ⟨PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P c, ?_⟩
  have h1 := congrArg (padicToCompletion P) hc
  rw [map_sub (padicToCompletion P), map_natCast (padicToCompletion P), map_mul (padicToCompletion P),
    map_natCast (padicToCompletion P), padicToCompletion_unitPadicAt y P] at h1
  exact h1

private theorem valued_unitAt_sub_residue_le (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (unitAt v y - (((unitResidue n y).val : ℕ) : v.adicCompletion ℚ))
      ≤ idealBound (𝓞 ℚ) (Ideal.span {(n : 𝓞 ℚ)}) v := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [← valued_natCast_eq_idealBound hn v]
  obtain ⟨P, rfl⟩ : ∃ P : Nat.Primes, (primesEquiv (R := 𝓞 ℚ)).symm P = v :=
    ⟨primesEquiv v, (primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v⟩
  by_cases hdvd : (P : ℕ) ∣ n
  · obtain ⟨z, hz⟩ := exists_unitAt_sub_residue_eq n y P (Nat.mem_primeFactors.mpr ⟨P.2, hdvd, hn⟩)
    have hz1 : Valued.v (z : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ _).mp z.2
    rw [hz, Valued.v.map_mul, natCast_level_eq n P, Valued.v.map_mul, valued_ordCompl_eq_one hn P,
      mul_one]
    exact mul_le_of_le_one_right' hz1
  · have h1 : Valued.v ((n : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) = 1 := by
      rw [← map_natCast (algebraMap ℚ (((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)),
        valued_algebraMap_rat]
      exact valuation_natCast_of_not_dvd _ (by rw [natGenerator_primesEquiv_symm]; exact hdvd)
    rw [h1]
    exact (Valuation.map_sub _ _ _).trans
      (max_le (valued_unitAt _ y).le (valued_natCast_le_one _ _))

private theorem snd_unitPart_sub_residue_mem_idealBall (n : ℕ) [NeZero n] (x : (𝔸ℚ)ˣ) :
    ((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (((unitResidue n x).val : ℕ) : ℚ)
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  intro v
  rw [coe_sub_apply, snd_unitPart,
    show (algebraMap ℚ 𝔸ℚf (((unitResidue n x).val : ℕ) : ℚ)) v
      = algebraMap ℚ (v.adicCompletion ℚ) (((unitResidue n x).val : ℕ) : ℚ) from rfl,
    map_natCast, ← unitResidue_unitPart n x]
  exact valued_unitAt_sub_residue_le n (unitPart x) v

private theorem algebraMap_natCast_mem_idealBall {n : ℕ} (hn : n ≠ 0) :
    algebraMap ℚ 𝔸ℚf ((n : ℕ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  intro v
  rw [show (algebraMap ℚ 𝔸ℚf ((n : ℕ) : ℚ)) v = algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ) from rfl,
    map_natCast, valued_natCast_eq_idealBound hn v]

private theorem neg_mem_idealBall {N : Ideal (𝓞 ℚ)} {z : 𝔸ℚf} (hz : z ∈ idealBall (𝓞 ℚ) ℚ N) :
    -z ∈ idealBall (𝓞 ℚ) ℚ N := fun v => by
  rw [coe_neg_apply, Valuation.map_neg]; exact hz v

private theorem centralScalar_comm (y : (𝔸ℚ)ˣ) (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    centralScalar (𝓞 ℚ) ℚ y * X = X * centralScalar (𝓞 ℚ) ℚ y :=
  centralScalar_mul_comm y X

private theorem centralScalar_principal (q : ℚˣ) :
    centralScalar (𝓞 ℚ) ℚ (principal q)
      = globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (algebraMap ℚ 𝔸ℚ (q : ℚ))
    = (Matrix.scalar (Fin 2) (q : ℚ)).map (algebraMap ℚ 𝔸ℚ)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

private theorem glFin_centralScalar_val (y : (𝔸ℚ)ˣ) :
    ((glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ y) : GL (Fin 2) 𝔸ℚf) : Matrix (Fin 2) (Fin 2) 𝔸ℚf)
      = Matrix.diagonal (fun _ => ((y : 𝔸ℚ)).2) := by
  ext i j
  rw [glFin_apply, centralScalar_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> rfl

private theorem glFin_mapGL_mul_centralScalar_apply (ε : SL(2, ℤ)) (y : (𝔸ℚ)ˣ) (i j : Fin 2) :
    ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * centralScalar (𝓞 ℚ) ℚ y)
        : GL (Fin 2) 𝔸ℚf) : Matrix (Fin 2) (Fin 2) 𝔸ℚf) i j
      = algebraMap ℚ 𝔸ℚf ((ε i j : ℤ) : ℚ) * ((y : 𝔸ℚ)).2 := by
  rw [map_mul, Units.val_mul, glFin_centralScalar_val, Matrix.mul_diagonal,
    glFin_globalPoints_apply]
  congr 1

private theorem isLevelOneMatrix_mapGL_mul_centralScalar {n : ℕ} (ε : SL(2, ℤ)) (y : (𝔸ℚ)ˣ)
    (hint : ((y : 𝔸ℚ)).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hc : algebraMap ℚ 𝔸ℚf ((ε 1 0 : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}))
    (hd : algebraMap ℚ 𝔸ℚf ((ε 1 1 : ℤ) : ℚ) * ((y : 𝔸ℚ)).2 - 1
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * centralScalar (𝓞 ℚ) ℚ y)
        : GL (Fin 2) 𝔸ℚf) : Matrix (Fin 2) (Fin 2) 𝔸ℚf) := by
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · rw [glFin_mapGL_mul_centralScalar_apply]
    exact mul_mem_integralFiniteAdeles (intCast_mem_integralFiniteAdeles _) hint
  · rw [glFin_mapGL_mul_centralScalar_apply]
    exact mul_mem_idealBall_right hc hint
  · rw [glFin_mapGL_mul_centralScalar_apply]
    exact hd

private def twistMat {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) : SL(2, ℤ) :=
  ⟨!![d, m; (n : ℤ), a], by rw [Matrix.det_fin_two_of]; exact hdet⟩

private theorem twistMat_apply_10 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    twistMat (n := n) d m a hdet 1 0 = (n : ℤ) := rfl

private theorem twistMat_apply_11 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    twistMat (n := n) d m a hdet 1 1 = a := rfl

private theorem twistMat_inv_apply_10 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    (twistMat (n := n) d m a hdet)⁻¹ 1 0 = -(n : ℤ) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

private theorem twistMat_inv_apply_11 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    (twistMat (n := n) d m a hdet)⁻¹ 1 1 = d := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

private theorem twistMat_mem_Gamma0 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    twistMat (n := n) d m a hdet ∈ Gamma0 n := by
  rw [Gamma0_mem, twistMat_apply_10, Int.cast_natCast, ZMod.natCast_self]

private theorem glFin_twist_mem_finiteLevelOne (n : ℕ) [NeZero n] (x : (𝔸ℚ)ˣ) (m a : ℤ)
    (hdet : ((unitResidue n x).val : ℤ) * a - m * n = 1) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (Matrix.SpecialLinearGroup.mapGL ℚ (twistMat (n := n) ((unitResidue n x).val : ℤ) m a hdet))
      * centralScalar (𝓞 ℚ) ℚ (unitPart x))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  have hn : n ≠ 0 := NeZero.ne n
  set d : ℤ := ((unitResidue n x).val : ℤ) with hd_def
  have hball : ((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (d : ℚ)
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [hd_def, Int.cast_natCast]
    exact snd_unitPart_sub_residue_mem_idealBall n x
  have hnball : algebraMap ℚ 𝔸ℚf (((n : ℕ) : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [Int.cast_natCast]; exact algebraMap_natCast_mem_idealBall hn
  rw [mem_finiteLevelOne_iff]
  refine ⟨?_, ?_⟩
  ·
    refine isLevelOneMatrix_mapGL_mul_centralScalar _ _ (snd_unitPart_mem_integral x) ?_ ?_
    · rw [twistMat_apply_10]; exact hnball
    · rw [twistMat_apply_11]

      have hkey : algebraMap ℚ 𝔸ℚf (a : ℚ) * ((unitPart x : 𝔸ℚ)).2 - 1
          = algebraMap ℚ 𝔸ℚf (a : ℚ) * (((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (d : ℚ))
            + algebraMap ℚ 𝔸ℚf (m : ℚ) * algebraMap ℚ 𝔸ℚf (((n : ℕ) : ℤ) : ℚ) := by
        have hmn : a * d - 1 = m * n := by linear_combination hdet
        have h2 : algebraMap ℚ 𝔸ℚf (m : ℚ) * algebraMap ℚ 𝔸ℚf (((n : ℕ) : ℤ) : ℚ)
            = algebraMap ℚ 𝔸ℚf (a : ℚ) * algebraMap ℚ 𝔸ℚf (d : ℚ) - 1 := by
          rw [← map_mul, ← map_mul, ← map_one (algebraMap ℚ 𝔸ℚf), ← map_sub, ← Int.cast_mul,
            ← Int.cast_mul, ← Int.cast_one, ← Int.cast_sub, hmn]
        rw [h2]; ring
      rw [hkey]
      exact add_mem_idealBall (mul_mem_idealBall_left (intCast_mem_integralFiniteAdeles _) hball)
        (mul_mem_idealBall_left (intCast_mem_integralFiniteAdeles _) hnball)
  ·
    rw [← map_inv, _root_.mul_inv_rev, ← map_inv, ← map_inv, ← map_inv, centralScalar_comm]
    refine isLevelOneMatrix_mapGL_mul_centralScalar _ _ (snd_inv_unitPart_mem_integral x) ?_ ?_
    · rw [twistMat_inv_apply_10, Int.cast_neg, map_neg]; exact neg_mem_idealBall hnball
    · rw [twistMat_inv_apply_11]

      have hkey : algebraMap ℚ 𝔸ℚf (d : ℚ) * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 - 1
          = -(((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (d : ℚ)) * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 := by
        rw [neg_sub, sub_mul, snd_unitPart_mul_snd_inv]
      rw [hkey]
      exact mul_mem_idealBall_right (neg_mem_idealBall hball) (snd_inv_unitPart_mem_integral x)

private theorem exists_twist (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (x : (𝔸ℚ)ˣ) :
    ∃ ε : SL(2, ℤ), ε ∈ Gamma0 n
      ∧ χ ((ε 1 1 : ℤ) : ZMod n) = (χ (unitResidue n x))⁻¹
      ∧ glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)
          * centralScalar (𝓞 ℚ) ℚ (unitPart x))
        ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  have hru : IsUnit (unitResidue n x) := (Group.isUnit x).map (unitResidue n)

  have hmul : (((unitResidue n x).val : ℕ) : ZMod n) * (((unitResidue n x)⁻¹.val : ℕ) : ZMod n) = 1 := by
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact ZMod.mul_inv_of_unit _ hru
  have hdvd : ((n : ℕ) : ℤ) ∣ ((unitResidue n x).val : ℤ) * ((unitResidue n x)⁻¹.val : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hmul, sub_self]
  obtain ⟨m, hm⟩ := hdvd
  have hdet : ((unitResidue n x).val : ℤ) * ((unitResidue n x)⁻¹.val : ℤ) - m * n = 1 := by
    linear_combination hm
  refine ⟨twistMat (n := n) _ m _ hdet, twistMat_mem_Gamma0 _ _ _ _, ?_,
    glFin_twist_mem_finiteLevelOne n x m _ hdet⟩
  rw [twistMat_apply_11, Int.cast_natCast, ZMod.natCast_zmod_val]
  have h1 : χ (unitResidue n x)⁻¹ * χ (unitResidue n x) = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit _ hru, map_one]
  exact eq_inv_of_mul_eq_one_left h1

private theorem ratArch_centralScalar_val (y : (𝔸ℚ)ˣ) :
    ((ratArch (centralScalar (𝓞 ℚ) ℚ y) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = archCoord y • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply]
  show InfinitePlace.Completion.ringEquivRealOfIsReal
      (isReal_rat_infinitePlace default)
      ((((centralScalar (𝓞 ℚ) ℚ y : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) 𝔸ℚ) i j).1 default) = _
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, ite_eq_left rfl, smul_eq_mul, mul_one,
      show (default : InfinitePlace ℚ) = Rat.infinitePlace from Subsingleton.elim _ _]
    rfl
  · rw [centralScalar_apply_ne y h, ite_eq_right h, smul_zero]
    exact map_zero _

private theorem det_ratArch_centralScalar (y : (𝔸ℚ)ˣ) :
    (ratArch (centralScalar (𝓞 ℚ) ℚ y)).det.val = archCoord y * archCoord y := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, ratArch_centralScalar_val, Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin, sq]

private theorem weightOneArchLift_mul_ratArch_centralScalar (f : ℍ → ℂ) (H : GL (Fin 2) ℝ)
    (x : (𝔸ℚ)ˣ) :
    weightOneArchLift f (H * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)))
      = ((archCoord (unitPart x) : ℝ) : ℂ) * weightOneArchLift f H := by
  have hcomm : H * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x))
      = ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)) * H := by
    apply Units.ext
    show (H : Matrix (Fin 2) (Fin 2) ℝ) * (ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)) : Matrix (Fin 2) (Fin 2) ℝ)
      = (ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)) : Matrix (Fin 2) (Fin 2) ℝ) * (H : Matrix (Fin 2) (Fin 2) ℝ)
    rw [ratArch_centralScalar_val, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hcomm]
  exact weightOneArchLift_scalar_mul f _ H _ (archCoord_unitPart_pos x) (ratArch_centralScalar_val _)

private theorem weightOneArchLift_gamma0_mul {n : ℕ} (f : ℍ → ℂ) (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 n) (M : GL (Fin 2) ℝ) (hM : 0 < M.det.val) :
    weightOneArchLift f ((γ : GL (Fin 2) ℝ) * M)
      = χ ((γ 1 1 : ℤ) : ZMod n) * weightOneArchLift f M := by
  have hσ : σ M (χ ((γ 1 1 : ℤ) : ZMod n)) = χ ((γ 1 1 : ℤ) : ZMod n) := by
    rw [σ, ite_eq_left hM]
    rfl
  rw [weightOneArchLift_def, weightOneArchLift_def, SlashAction.slash_mul, hχ γ hγ,
    ModularForm.smul_slash, map_mul, Units.val_mul, det_coe_SL, one_mul, Pi.smul_apply, hσ,
    smul_eq_mul]
  ring

private theorem weightOneLift_centralScalar_unitPart_mul {n : ℕ} [NeZero n] (hn : n ≠ 0)
    (f : ℍ → ℂ) (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (x : (𝔸ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (unitPart x) * g)
      = (χ (unitResidue n x))⁻¹ * ((archCoord (unitPart x) : ℝ) : ℂ)
          * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨ε, hε, hχε, hkε⟩ := exists_twist n χ x
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := hasWeightOneDecomp_of_ne_bot hN g
  have hglArch_u : glArch (𝓞 ℚ) ℚ u = 1 := ((mem_U_iff _ u).mp hu).2
  have hfin_u : glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) :=
    ((mem_U_iff _ u).mp hu).1

  have hprod : centralScalar (𝓞 ℚ) ℚ (unitPart x) * g
      = globalPoints (𝓞 ℚ) ℚ (γ * (Matrix.SpecialLinearGroup.mapGL ℚ ε)⁻¹)
        * (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
            * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u) := by
    rw [hg, map_mul, map_inv, ← mul_assoc, centralScalar_comm]
    group

  have hkf : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
        * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u)
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [map_mul, map_mul, map_mul, hfin, mul_one, ← map_mul]
    exact mul_mem hkε hfin_u

  have hratk : ratArch (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
        * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u)
      = (ε : GL (Fin 2) ℝ) * (ratArch h * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x))) := by
    rw [ratArch_mul, ratArch_mul, ratArch_mul, ratArch_globalPoints_mapGL,
      ratArch_eq_one_of_glArch_eq_one hglArch_u, mul_one, mul_assoc]
  have hdetH : 0 < (ratArch h).det.val := by
    rw [← ratArchGL2_eq_ratArch]
    exact hpos
  have hdetM : 0 < (ratArch h * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x))).det.val := by
    rw [map_mul, Units.val_mul, det_ratArch_centralScalar]
    exact mul_pos hdetH (mul_pos (archCoord_unitPart_pos x) (archCoord_unitPart_pos x))
  have hdetk : 0 < (ratArch 1 * ratArch (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
        * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u)).det.val := by
    rw [ratArch_one, one_mul, hratk, map_mul, Units.val_mul, det_coe_SL, one_mul]
    exact hdetM
  have hR7 := weightOneLift_mul_eq hn f hf
    (g₀ := globalPoints (𝓞 ℚ) ℚ (γ * (Matrix.SpecialLinearGroup.mapGL ℚ ε)⁻¹))
    (γ₀ := γ * (Matrix.SpecialLinearGroup.mapGL ℚ ε)⁻¹)
    (one_mem _) (map_one (glFin (𝓞 ℚ) ℚ)) (by rw [mul_one, mul_one]) _ hkf hdetk
  rw [hprod, hR7, ratArch_one, one_mul, hratk, weightOneArchLift_gamma0_mul f χ hχ ε hε _ hdetM,
    weightOneArchLift_mul_ratArch_centralScalar, hχε,
    weightOneLift_eq hn f hf g γ h u hu hfin hpos hg, ratArchGL2_eq_ratArch, mul_assoc]

private theorem weightOneLift_centralScalar_mul_eq {n : ℕ} [NeZero n] (hn : n ≠ 0)
    (f : ℍ → ℂ) (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (x : (𝔸ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hprin : ∀ q : ℚˣ,
      MeasureTheory.distribHaarChar 𝔸ℚ (Units.map (algebraMap ℚ 𝔸ℚ).toMonoidHom q) = 1)
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ x * g)
      = ((DirichletCharacter.dirichletIdeleChar χ x : ℂˣ) : ℂ)
          * ((MeasureTheory.distribHaarChar 𝔸ℚ x : ℝ) : ℂ)
          * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  conv_lhs => rw [← principal_mul_unitPart x, map_mul, mul_assoc, centralScalar_principal,
    weightOneLift_globalPoints_mul hn f hf]
  rw [weightOneLift_centralScalar_unitPart_mul hn f hf χ hχ x g,
    DirichletCharacter.coe_dirichletIdeleChar_apply, coe_distribHaarChar_eq_archCoord hprin hprod]

theorem weightOneLift_centralScalar_mul
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f) :
    ∀ (z : (productionPinsCompact ℚ).Z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g)
        = ((((DirichletCharacter.dirichletIdeleChar χ *
            (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
              (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          (productionPinsCompact ℚ).Z.subtype) z : ℂˣ) : ℂ) * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hprin := fun q : ℚˣ => @NumberField.AdeleRing.distribHaarChar_algebraMap ℚ _ _
    (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (NumberField.RingOfIntegers ℚ) ℚ) q
  have hprod := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ
  intro z g
  exact weightOneLift_centralScalar_mul_eq hn f hf χ hχ
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) g hprin hprod

end LanglandsTunnell

end
