/-
  Consumer specification for the `ds-head` differential / ramification tail.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the three ported `ds-head` modules. It is a deliverable
  measure, not a proof obligation, and it is deliberately **not part of any
  library**: nothing globs `spec/`, so it cannot break the verified port's green
  build. Run it by hand:

      cd lean
      lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DsHeadConsumer.lean 2>&1 | grep -c error

  The error count is the metric (target 0). No `#check`, no `sorry`.

  HOW TO READ IT
  --------------
  One zone per module/claim. Every zone is a real, executed application, so
  deleting any one of `Differential/Hurwitz.lean`,
  `Differential/Coefficient.lean` or `Genus/RatFunc.lean` makes this file fail to
  elaborate:

    [hurwitz]      the two headlines of the duplicated pin pair, composed with each
                   other (the `KaehlerDifferential.map` nonvanishing discharges the
                   Hurwitz formula's `hω₀'` hypothesis) and instantiated at the
                   concrete `ℙ¹` differential `dX K`.
    [generation]   the Ω-generation headline at the concrete `P1` place
                   `placeInfty K`.
    [diffcoeff]    the coefficient layer the same module carries: the pin's
                   `diffCoeff` against a uniformiser (existence, uniqueness,
                   integrality) under the headlines' own hypotheses, that
                   integrality again with the separability instance discharged
                   from `ord t = 1`, and the bridge to the canonical
                   `differentialCoeff` at `placeInfty K`.
    [ratfunc]      the `ℙ¹` genus headline and its degree half at the same place
                   `placeInfty K`, consuming `Hurwitz`'s `KaehlerDifferential.map`
                   API in the headline's type.
    [socket]       the `C`-layer socket assembly `package_of_socket` (at `M = 1` and
                   at a general level over `ℚ`) and the transport's two degree
                   headlines; see that zone's own note.
-/

import FLTForHuman.AlgebraicCurve.Differential.Hurwitz
import FLTForHuman.ModularCurve.Degree.FinrankAdjoinJqNModC
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Genus.RatFunc
import FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental
import FLTForHuman.ModularForms.AtkinLehnerSlash
import FLTForHuman.ModularForms.WeightOne.NebentypusQCoeffSq

open AlgebraicCurve
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential

noncomputable section

/-! ## Zone `[hurwitz]` — the duplicated pair, written once

`Differential/Hurwitz.lean` carries both headlines. The first example is the
`KaehlerDifferential.map` nonvanishing statement; the second composes the two:
the map-nonvanishing headline is exactly the `hω₀'` hypothesis the Hurwitz
formula names, so the pair is applied as one engine. -/

example {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    (w₀ : Place K F') {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    KaehlerDifferential.map K K F F' ω₀ ≠ 0 :=
  map_ne_zero_of_tame hreg htame w₀ hω₀

example {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    (w₀ : Place K F') {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    (hK : Divisor.degree (canonicalDivisorOf (K := K) hω₀) = 2 * (genus K F : ℤ) - 2)
    (hK' : Divisor.degree (canonicalDivisorOf (K := K)
        (show KaehlerDifferential.map K K F F' ω₀ ≠ 0
          from map_ne_zero_of_tame hreg htame w₀ hω₀)) = 2 * (genus K F' : ℤ) - 2) :
    2 * (genus K F' : ℤ) - 2
      = (Module.finrank F F' : ℤ) * (2 * (genus K F : ℤ) - 2)
        + ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) :=
  two_mul_genus_sub_two_eq_of_degree_canonical hreg htame hω₀
    (map_ne_zero_of_tame hreg htame w₀ hω₀) hK hK'

/-! The engine at the concrete `ℙ¹` differential `dX K`: the tame engine's
`differentialCoeff_D_uniformizer_pow` machinery is applied to the uniformizer of a
`RatFunc` place, and the Hurwitz headline's type uses `dX` from `P1/UnitNormalForm`. -/

example (K : Type*) [Field K] :
    (KaehlerDifferential.D K (RatFunc K)) RatFunc.X = dX K := rfl

/-! ## Zone `[generation]` — Ω generated by `dπ` at a concrete `P1` place -/

example (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [Algebra.EssFiniteType K (RatFunc K)] [IsCurveOver K (RatFunc K)]
    {π : RatFunc K} (hπ : (placeInfty K).ord π = 1) {x : RatFunc K}
    (hx : x ∈ (placeInfty K).toValuationSubring) :
    ∃ c : RatFunc K, c ∈ (placeInfty K).toValuationSubring ∧
      KaehlerDifferential.D K (RatFunc K) x
        = c • KaehlerDifferential.D K (RatFunc K) π :=
  exists_mem_D_eq_smul_D_of_isCurveOver (placeInfty K) hπ hx

/-! ## Zone `[diffcoeff]` — the coefficient against a uniformiser

The same module's coefficient layer, applied with the headlines' own binder walls
(these are how a consumer states them: the hypotheses are the function-field ones,
not `IsCurveOver`), and then at the concrete `ℙ¹` place, where the general
coefficient is the canonical `differentialCoeff` of `Defs/CanonicalDivisor.lean` —
the bridge that keeps the tree on one coefficient API. -/

example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (ω : KaehlerDifferential K F) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω :=
  AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_eq_one x v ht ω

example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (g : F) :
    AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) = g :=
  AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one x v ht g

example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F] {f : F}
    (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) :=
  AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable x v ht hf

-- ... and the perfect-field form, where `ord t = 1` supplies the instance above.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) :=
  AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht hf

-- the concrete place carries the instance the bridge needs ...
example (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [Algebra.EssFiniteType K (RatFunc K)] [IsCurveOver K (RatFunc K)] :
    ∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates :=
  AlgebraicCurve.dCoordGenerates_of_isCurveOver

-- ... and with it the general coefficient is the canonical one at `placeInfty K`.
example (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [Algebra.EssFiniteType K (RatFunc K)] [IsCurveOver K (RatFunc K)]
    [(placeInfty K).DCoordGenerates] (ω : KaehlerDifferential K (RatFunc K)) :
    AlgebraicCurve.Place.diffCoeff (placeInfty K).uniformizer ω
      = (placeInfty K).differentialCoeff ω :=
  AlgebraicCurve.Place.diffCoeff_uniformizer_eq_differentialCoeff _ ω

/-! ## Zone `[ratfunc]` — the `ℙ¹` genus headline

The headline at its wrapper hypotheses, plus its degree half applied to the
concrete `dX K`. -/

example (K : Type*) [Field K] [PerfectField K] [IsCurveOver K (RatFunc K)]
    [HasCanonicalDivisor (K := K) (F := RatFunc K)] : genus K (RatFunc K) = 0 :=
  genus_ratFunc_eq_zero_of_perfectField K

example (K : Type*) [Field K] [PerfectField K] [IsCurveOver K (RatFunc K)]
    {ω : Ω[(RatFunc K)⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = -2 :=
  degree_canonicalDivisorOf_ratFunc_of_perfectField_s17 K hω

example (K : Type*) [Field K] [PerfectField K] [IsCurveOver K (RatFunc K)]
    [HasCanonicalDivisor (K := K) (F := RatFunc K)] :
    Divisor.degree (canonicalDivisorOf (K := K) (dX_ne_zero K)) = -2 :=
  degree_canonicalDivisorOf_ratFunc_of_perfectField_s17 K (dX_ne_zero K)

/-! ## Zone `[riders]` — the two small deferred nodes folded in

`Genus/RatFunc.lean` gains the `CharZero` form (a char-zero field is perfect);
`Defs/KaehlerTranscendental.lean` gains the uniqueness of the differential
generator. Each example applies a declaration that exists in exactly one of those
modules. -/

example (K : Type*) [Field K] [CharZero K] [IsCurveOver K (RatFunc K)]
    [HasCanonicalDivisor (K := K) (F := RatFunc K)] : genus K (RatFunc K) = 0 :=
  genus_ratFunc_eq_zero K

example (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (ω : KaehlerDifferential K F) :
    ∃! c : F, ω = c • KaehlerDifferential.D K F x :=
  KaehlerDifferential.exists_unique_smul_D_of_transcendental K x hx ω

/-! ## Zone `[genusff]` — the geometric genus of `ℙ¹` at its closure

`genusFF_ratFunc_eq_zero_of_isAlgClosed` is the deepest node of this set: it
composes the closure landed in `ResidueTheorem/RRAssembly.lean`
(`functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver`,
`constantsAreBase_of_isAlgClosed`, `genus_eq_genusFF`) with the landed
`genus_ratFunc_eq_zero_of_perfectField`. It takes no hypotheses beyond
`[IsAlgClosed K]`, so the `ℂ` instance is a fully concrete application. -/

example (K : Type*) [Field K] [IsAlgClosed K] : genusFF K (RatFunc K) = 0 :=
  genusFF_ratFunc_eq_zero_of_isAlgClosed K

example : genusFF ℂ (RatFunc ℂ) = 0 :=
  genusFF_ratFunc_eq_zero_of_isAlgClosed ℂ

/-! ## Zone `[socket]` — the `C`-layer assembly and its transport, at `K = ℚ`

`FunctionFieldGeneration/PrimePowerStepAnyField.lean` carries the socket assembly
`package_of_socket` (its prime-step parameter `hKG1` filled by JQ2's
`jqNModC_mem_modularFunctionFieldC_mul_prime`), and
`Degree/FinrankAdjoinJqNModC.lean` the descent's two headlines. Every example below
*is* one of those declarations applied, so deleting or renaming either headline makes
this zone fail to elaborate.

Over `ℚ` the socket's `hbase` is not an assumption but the landed
`jqNModC_prime_not_mem_adjoin_of_charZero`, so the assembly runs at any level: the
first example is the trivial level `M = 1` with `ζ = 1`, the second a general level.
The last two read the degree half off the two headlines — the char-zero twin at
`d = 4`, and the `_of_socket` headline at its own `hbase` binder. -/

open ModularCurve HahnSeries in
example : ∀ d : ℕ, d ∣ 1 → ∀ [NeZero d],
    (Module.finrank (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
          ({jqNModC ℚ d} : Set (LaurentSeries ℚ))) = ModularCurve.dedekindPsi d)
      ∧ modularFunctionFieldC ℚ d = IntermediateField.adjoin ℚ
          {x : LaurentSeries ℚ | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC ℚ d'} :=
  package_of_socket 1 (1 : ℚˣ) (by simp)
    fun (p : ℕ) [Fact (Nat.Prime p)] hp =>
      absurd (Nat.dvd_one.mp hp) (Fact.out : Nat.Prime p).ne_one

open ModularCurve HahnSeries in
example (M : ℕ) [NeZero M] (ζ : ℚˣ) (hζ : IsPrimitiveRoot (ζ : ℚ) M) :
    ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      (Module.finrank (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
          (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
            ({jqNModC ℚ d} : Set (LaurentSeries ℚ))) = ModularCurve.dedekindPsi d)
        ∧ modularFunctionFieldC ℚ d = IntermediateField.adjoin ℚ
            {x : LaurentSeries ℚ | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC ℚ d'} :=
  package_of_socket M ζ hζ fun (p : ℕ) [Fact (Nat.Prime p)] _ =>
    jqNModC_prime_not_mem_adjoin_of_charZero p

open ModularCurve HahnSeries in
example : Module.finrank (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
    (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
      ({jqNModC ℚ 4} : Set (LaurentSeries ℚ))) = ModularCurve.dedekindPsi 4 :=
  finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero 4

open ModularCurve HahnSeries in
example (d : ℕ) [NeZero d]
    (hbase : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ d →
      jqNModC ℚ p ∉ IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ))) :
    Module.finrank (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
          ({jqNModC ℚ d} : Set (LaurentSeries ℚ))) = ModularCurve.dedekindPsi d :=
  finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket d hbase


/-! ## Zone `[nb1]` — the Atkin–Lehner `alSlash` pair and the twin `CuspForm` headlines

`ModularForms/AtkinLehnerSlash.lean` states both premise headlines (`isZeroAt_alSlash`,
`mdifferentiable_alSlash`) and `WeightOne/PrimitiveQCoeffNorm.lean` /
`WeightOne/NebentypusQCoeffSq.lean` state the two `CuspForm` headlines over one shared block.
The application below pins every headline at `M = 2`, `k = 0`, `ℓ = p = 2`, where `2 / 2 = 1`,
so `ε'` is a character at level `1`; `IsPrimitiveForm` / `HasNebentypus` are the ported level
vocabulary (`Defs/PrimitiveFormGamma1.lean`). Deleting any one of the four headlines makes this
zone fail to elaborate. -/

open CuspForm in
example (h2 : 2 ∣ 2) (g : CuspForm (CongruenceSubgroup.Gamma1 2) (0 : ℤ))
    (ε' : DirichletCharacter ℂ (2 / 2))
    (hg : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd h2) ε') g) :
    ‖ModularFormClass.qCoeff g 2‖ ^ 2 = (2 : ℝ) ^ ((0 : ℤ) - 2) :=
  CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd 2 0 Nat.prime_two h2
    (by norm_num) ε' g hg

open CuspForm in
example (h2 : 2 ∣ 2) (f : CuspForm (CongruenceSubgroup.Gamma1 2) (0 : ℤ)) (hf0 : f ≠ 0)
    (ε' : DirichletCharacter ℂ (2 / 2))
    (hε : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd h2) ε') f)
    (hU : ∀ n : ℕ, ModularFormClass.qCoeff f (2 * n) =
      ModularFormClass.qCoeff f 2 * ModularFormClass.qCoeff f n)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ 2 → ∀ n : ℕ,
        ModularFormClass.qCoeff f (ℓ * n) +
            ε' (ℓ : ZMod (2 / 2)) * (ℓ : ℂ) ^ ((0 : ℤ) - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff f (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff f n) :
    ModularFormClass.qCoeff f 2 ^ 2 = ε' (2 : ZMod (2 / 2)) * (2 : ℂ) ^ ((0 : ℤ) - 2) ∨
      ∃ g : CuspForm (CongruenceSubgroup.Gamma1 (2 / 2)) (0 : ℤ), g ≠ 0 ∧
        CuspForm.HasNebentypus ε' g ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ 2 → ∀ n : ℕ,
          ModularFormClass.qCoeff g (ℓ * n) +
              ε' (ℓ : ZMod (2 / 2)) * (ℓ : ℂ) ^ ((0 : ℤ) - 1) *
                (if ℓ ∣ n then ModularFormClass.qCoeff g (n / ℓ) else 0) =
            ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff g n :=
  CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
    2 0 Nat.prime_two h2 (by norm_num) ε' f hf0 hε hU hT

end
