/-
The Hasse-derivative descent of the modular polynomial, and its identifying data.

Two rows of the modular polynomial `Φ` (`X₀(N)`'s classical equation) that the modular-equation
development needs at its end:

* `ModularCurve.StarBank.hassePolyDescent` — the **Hasse-derivative descent**: the modular polynomial
  of the `q`-expansion of `jq` descends along the Hasse derivative, so that `Φ`'s coefficients can be
  computed from the level-one `q`-expansion of `E₄³/Δ` and its Hasse derivatives;
* `ModularCurve.ModularPolynomialData.eq_all` — two `ModularPolynomialData` structures with equal
  `q`-expansion data are **equal**: the polynomial (and the whole data bundle) is determined by
  `Φ(jq, jq_N) = 0` and the finrank of the adjoin, which is the uniqueness half of the
  modular-polynomial existence theorem.

The engine is the `q`-expansion model of the modular polynomial's coefficients
(`ModularCurve/JqIntegralRatios.lean`, `ModularForms/{JqAnalyticModel,LevelOneSlash,
IsArithmeticQExpansion}.lean`), the modular-equation construction
(`ModularCurve/ModularEquation/Construction.lean`) and the function-field generation capstone
(`ModularCurve/FunctionFieldGeneration/Capstone.lean`).

## Substitutions (this order's substitute pass)

Both rows are consumers, so most of their surface was already public in the port. What is
**imported** rather than re-proved, and why the pin's copy is not restated:

* `ModularCurve.jqModC_pow` (`ModularCurve/Defs/JqCoeff.lean`, public, `spec-pin:`
  `Theorems/Thm_ModularCurve_jqModC_pow.lean`) is the pin's `W1.jqModC_pow_eq` **verbatim** —
  same binders `(K : Type*) [CommRing K] (n : ℕ)`, same statement.  The pin's `W1` copy is
  dropped; `W1.jqModC_pow_mul_etaBlock` below rewrites with the port's home.
* `HahnSeries.coeff_single_zero_mul` (mathlib, `RingTheory/HahnSeries/Multiplication.lean`) is the
  pin's `W1.coeff_single_zero_mul` verbatim; the pin's one-line restatement is dropped.
* `ModularCurve.algebraMap_laurentSeries_eq_single` (`ModularCurve/Defs/Laurent.lean`) is the
  pin's `W1.algebraMap_laurent_eq_single` at `[Field L]`; the pin's `CommRing` spelling is kept
  here as `W1.algebraMap_laurent_eq_single` because the ℤ-case of the headline proof needs it at
  `ℤ` (the port's home is `Field`-only).  **Generalisation candidate**: widening
  `Defs/Laurent.lean`'s copy to `[CommRing L]` retires this duplicate — a `Defs/` edit is outside
  this order.
* The second row's whole engine is public in the port:
  `ModularCurve.evalAtJGen_injective` and `ModularCurve.aeval_jqN_toAdjoin`
  (`ModularEquation/Existence.lean`), `ModularCurve.toAdjoin_eq_minpoly_all`
  (`ModularPolynomialUniquenessIrreducible.lean`, whose own wire names this row's `S_` file).
  The pin's `W1` prelude
  of that row (`evalAtJGen_injective`, `aeval_jqN_toAdjoin`, `natDegree_toAdjoin`,
  `toAdjoin_eq_minpoly_all`) is therefore **not** restated — `eq_all` below is the pin's eleven
  lines and nothing else.  The pin's `private` copies in `S_…:27-49` are the same four lemmas.
* The pin's three anonymous `example` probes of the first row (`S_…:352-395`: the discriminant
  identity, `constantCoeff (X * dedekindEtaUnit) = 0`, and the falsifier of the `N = 1` case) are
  node-local regression checks of imported lemmas, consumed by nothing: dropped, as this set's
  other orders drop their `example` probes.

## Names

The pin's `W1` prelude namespace is kept (`ModularCurve.W1`), following
`ModularCurve/StarBank/Norm.lean`'s and `ModularCurve/Defs/TS.lean`'s precedents for this pin
family.  The pin's generated `P2MW.S_…` label is dropped, as always.

## Axioms, and the heartbeat probe pair (recorded, never installed)

`#print axioms` on all ten public declarations of this module — and on
`ModularCurve.card_quotient_gamma0_le_dedekindPsi` of `Gamma0DedekindPsi.lean` — is
`[propext, Classical.choice, Quot.sound]` for every one, no `sorryAx`
(`lean/tmp/af106/AF106E-axioms.log`).

The playbook's **downward** heartbeat ladder, one run per value, over this file at
`-DautoImplicit=false`:

| cap | verdict |
|---:|---|
| 40000 | ok |
| 20000 | ok |
| 15000 | FAIL — `:180:0`, the `StarBank.hassePolyDescent` statement (`whnf`) |
| 12000 | FAIL — `:386:6`, the `hZsum` `rw` list (`isDefEq`) |
| 10000 | FAIL — `:348:16`, `⟨0, map_zero _⟩` in `hlifts` (`isDefEq`) |
| 1000 | FAIL — `:126:59`, `jqModC_pow_mul_etaBlock`'s `map_pow` step (`whnf`) |

**The pair is 20000 ok / 15000 fail**: the module's floor sits between the two, far below the
lakefile's 4 M bound, and **no cap is installed** — no `set_option maxHeartbeats`, no
`set_option synthInstance.maxHeartbeats`, and no `attribute [-instance]`/`[-simp]` wall (the pin
carries such a wall; it is not transcribed).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_StarBank_hassePolyDescent.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean>

spec-pin: Theorems/Thm_ModularCurve_StarBank_hassePolyDescent.lean
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean
spec-pin: P2M/Sol/S_ModularCurve_StarBank_hassePolyDescent.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_all.lean
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.ModularEquation.Construction
import FLTForHuman.ModularCurve.ModularPolynomialUniquenessIrreducible
import FLTForHuman.ModularForms.IsArithmeticQExpansion
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularForms.LevelOneSlash

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries ModularCurve UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

namespace W1

/-- The identity `ℤ →+* ℤ` is `Int.castRingHom ℤ`, so the `ℤ`-coefficient base change of an
integral power series is itself.  The pin's `S_…:22`, verbatim. -/
theorem powerSeries_map_intCast_self (u : PowerSeries ℤ) : u.map (Int.castRingHom ℤ) = u := by
  rw [RingHom.ext_int (Int.castRingHom ℤ) (RingHom.id ℤ)]
  exact congrFun PowerSeries.map_id u

/-- `j(q)^a` is `q^(-a)` times the `a`-th power of the integral numerator — the pin's
`W1.jqModC_pow_mul_etaBlock`'s engine for the `q`-grading.  The pin's `W1.jqModC_pow_eq` is
`ModularCurve.jqModC_pow` (`Defs/JqCoeff.lean`) verbatim and is not restated here. -/
theorem jqModC_pow_mul_etaBlock (K : Type*) [CommRing K] (a N : ℕ) :
    jqModC K ^ a
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K))) ^ N
      = HahnSeries.single ((N : ℤ) - a) 1
        * HahnSeries.ofPowerSeries ℤ K
            (jNum.map (Int.castRingHom K) ^ a * dedekindEtaUnit.map (Int.castRingHom K) ^ N) := by
  have h1 : N • (1 : ℤ) = (N : ℤ) := by simp
  rw [jqModC_pow, mul_pow, HahnSeries.single_pow, one_pow, h1,
    show (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K))) ^ N
        = HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K) ^ N) from
      (map_pow _ _ _).symm,
    mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul,
    show HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K) ^ a)
          * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K) ^ N)
        = HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K) ^ a
            * dedekindEtaUnit.map (Int.castRingHom K) ^ N) from (map_mul _ _ _).symm,
    show (-(a : ℤ) + (N : ℤ)) = (N : ℤ) - a from by ring]

/-- Coefficient of a single-`q`-monomial block above its pole: the pin's
`W1.coeff_single_mul_ofPowerSeries_nonneg`, verbatim. -/
theorem coeff_single_mul_ofPowerSeries_nonneg {K : Type*} [Semiring K] (c : ℤ)
    (U : PowerSeries K) (n : ℕ) :
    (HahnSeries.single c (1 : K) * HahnSeries.ofPowerSeries ℤ K U).coeff (c + (n : ℤ))
      = PowerSeries.coeff n U := by
  rw [HahnSeries.coeff_single_mul, one_mul, add_sub_cancel_left]
  exact HahnSeries.ofPowerSeries_apply_coeff U n

/-- Coefficient of a single-`q`-monomial block below its pole: zero.  The pin's
`W1.coeff_single_mul_ofPowerSeries_neg`, verbatim. -/
theorem coeff_single_mul_ofPowerSeries_neg {K : Type*} [Semiring K] (c : ℤ)
    (U : PowerSeries K) {g : ℤ} (hg : g < c) :
    (HahnSeries.single c (1 : K) * HahnSeries.ofPowerSeries ℤ K U).coeff g = 0 := by
  rw [HahnSeries.coeff_single_mul, one_mul,
    ModularCurve.ofPowerSeries_coeff_of_neg _ (show g - c < 0 by omega)]

/-- Coefficients commute with the `ℤ → ℂ` base change of an integral `q`-expansion: the pin's
`W1.coeff_ofPowerSeries_map`, verbatim. -/
theorem coeff_ofPowerSeries_map (U : PowerSeries ℤ) (g : ℤ) :
    (HahnSeries.ofPowerSeries ℤ ℂ (U.map (Int.castRingHom ℂ))).coeff g
      = (((HahnSeries.ofPowerSeries ℤ ℤ U).coeff g : ℤ) : ℂ) := by
  rcases le_or_gt 0 g with hg | hg
  · lift g to ℕ using hg
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, Int.coe_castRingHom]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hg,
      ModularCurve.ofPowerSeries_coeff_of_neg _ hg, Int.cast_zero]

/-- Constants of a commutative coefficient ring are the `q⁰`-monomial: the pin's
`W1.algebraMap_laurent_eq_single`, verbatim.  `Defs/Laurent.lean`'s
`algebraMap_laurentSeries_eq_single` is this statement at `[Field L]`; the headline's ℤ-case
needs it at `ℤ`, hence the `CommRing` copy. -/
theorem algebraMap_laurent_eq_single (K : Type*) [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single (0 : ℤ) c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

end W1

namespace StarBank

/-- **The Hasse-derivative descent of the modular polynomial.**  For a weight-`12N` level-one form
`F` whose `q`-expansion is the base change of an integral series `T` with nonzero constant term,
there is `G : ℤ[X]` of degree `N` with `G.coeff N = constantCoeff T` and

  `T(q) = G(j(q)) · (q · η(q)^24)^N`,

i.e. the level-`N` modular polynomial's `q`-expansion is computed from level one's `E₄³/Δ`, and its
coefficients are the integers obtained by the `q`-grading descent (`hstep` below: the diagonal
coefficient is `1`, so `P.coeff i` is a integer whenever the higher ones are, by downward
induction).  The pin's `S_…:88` (its `private` copy) and `Theorems/Thm_…` (public) — stated once,
public, here. -/
theorem hassePolyDescent {N : ℕ}
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑F)
    (h0 : PowerSeries.constantCoeff T ≠ 0) :
    ∃ G : Polynomial ℤ, G.natDegree = N ∧ G.coeff N = PowerSeries.constantCoeff T ∧
      HahnSeries.ofPowerSeries ℤ ℤ T
        = Polynomial.aeval (ModularCurve.jqModC ℤ) G
          * (HahnSeries.single (1 : ℤ) 1
              * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24) ^ N := by
  obtain ⟨P, hPdeg, hPid⟩ := ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne N F
  rw [← ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, ← hT,
    ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit] at hPid
  have hXded : HahnSeries.ofPowerSeries ℤ ℂ
      ((PowerSeries.X * ModularCurve.dedekindEtaUnit).map (Int.castRingHom ℂ))
      = HahnSeries.single (1 : ℤ) 1
        * HahnSeries.ofPowerSeries ℤ ℂ (dedekindEtaUnit.map (Int.castRingHom ℂ)) := by
    rw [map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X]
  rw [hXded] at hPid

  have hCa : ∀ a : ℕ, (jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ)
      = jNum.map (Int.castRingHom ℂ) ^ a * dedekindEtaUnit.map (Int.castRingHom ℂ) ^ N := by
    intro a
    rw [map_mul, map_pow, map_pow]
  have hsum : Polynomial.aeval (jqModC ℂ) P
      * (HahnSeries.single (1 : ℤ) 1
          * HahnSeries.ofPowerSeries ℤ ℂ (dedekindEtaUnit.map (Int.castRingHom ℂ))) ^ N
      = ∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (P.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℂ
                    ((jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ))) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
      Polynomial.sum_over_range' P (fun n => by rw [map_zero, zero_mul]) (N + 1)
        (Nat.lt_succ_of_le hPdeg), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, ModularCurve.W1.algebraMap_laurent_eq_single,
      ModularCurve.W1.jqModC_pow_mul_etaBlock ℂ a N, ← hCa a]
  rw [hsum] at hPid

  have hkey : ∀ i : ℕ, i ≤ N →
      ((PowerSeries.coeff (N - i) T : ℤ) : ℂ)
        = ∑ a ∈ Finset.range (N + 1), P.coeff a *
            (if i ≤ a
              then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
              else 0) := by
    intro i hi
    have h1 := congrArg (fun x : LaurentSeries ℂ => x.coeff ((N : ℤ) - i)) hPid
    have hL : (HahnSeries.ofPowerSeries ℤ ℂ (T.map (Int.castRingHom ℂ))).coeff ((N : ℤ) - i)
        = ((PowerSeries.coeff (N - i) T : ℤ) : ℂ) := by
      rw [show ((N : ℤ) - i) = ((N - i : ℕ) : ℤ) from by omega,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, Int.coe_castRingHom]
    have hR : (∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (P.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℂ
                    ((jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ)))).coeff
            ((N : ℤ) - i)
        = ∑ a ∈ Finset.range (N + 1), P.coeff a *
            (if i ≤ a
              then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
              else 0) := by
      rw [HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [HahnSeries.coeff_single_zero_mul]
      congr 1
      by_cases hia : i ≤ a
      · rw [ite_eq_left hia, show ((N : ℤ) - i) = ((N : ℤ) - a) + ((a - i : ℕ) : ℤ) from by omega,
          ModularCurve.W1.coeff_single_mul_ofPowerSeries_nonneg, PowerSeries.coeff_map,
          Int.coe_castRingHom]
      · rw [ite_eq_right hia]
        exact ModularCurve.W1.coeff_single_mul_ofPowerSeries_neg _ _ (by omega)
    rw [hL, hR] at h1
    exact h1

  have hdiag : ∀ i : ℕ, PowerSeries.coeff 0 (jNum ^ i * dedekindEtaUnit ^ N) = 1 := by
    intro i
    have h1 : PowerSeries.constantCoeff (jNum ^ i * dedekindEtaUnit ^ N) = 1 := by
      rw [map_mul, map_pow, map_pow, ModularCurve.constantCoeff_jNum,
        ModularCurve.constantCoeff_dedekindEtaUnit, one_pow, one_pow, one_mul]
    rw [← h1]
    exact congrFun PowerSeries.coeff_zero_eq_constantCoeff _

  have hPN : P.coeff N = ((PowerSeries.constantCoeff T : ℤ) : ℂ) := by
    have hk := hkey N le_rfl
    have hdiagN : (if N ≤ N
        then ((PowerSeries.coeff (N - N) (jNum ^ N * dedekindEtaUnit ^ N) : ℤ) : ℂ)
        else 0) = 1 := by
      rw [ite_eq_left le_rfl, Nat.sub_self, hdiag N, Int.cast_one]
    rw [Finset.sum_eq_single_of_mem N (Finset.mem_range.mpr (Nat.lt_succ_self N))
      (fun a ha hne => by
        rw [ite_eq_right (show ¬N ≤ a from by
          have := Finset.mem_range.mp ha
          omega), mul_zero]), hdiagN, mul_one, Nat.sub_self] at hk
    rw [← hk]
    congr 1
    exact congrFun PowerSeries.coeff_zero_eq_constantCoeff T

  have hstep : ∀ i : ℕ, i ≤ N →
      (∀ a : ℕ, a ≤ N → i < a → P.coeff a ∈ Set.range ⇑(Int.castRingHom ℂ)) →
      P.coeff i ∈ Set.range ⇑(Int.castRingHom ℂ) := by
    intro i hi hIH
    have hk := hkey i hi
    have hmem : i ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hdiagterm : (if i ≤ i
        then ((PowerSeries.coeff (i - i) (jNum ^ i * dedekindEtaUnit ^ N) : ℤ) : ℂ)
        else 0) = 1 := by
      rw [ite_eq_left le_rfl, Nat.sub_self, hdiag i, Int.cast_one]
    rw [← Finset.add_sum_erase _ _ hmem, hdiagterm, mul_one] at hk
    have hPi : P.coeff i
        = ((PowerSeries.coeff (N - i) T : ℤ) : ℂ)
          - ∑ a ∈ (Finset.range (N + 1)).erase i, P.coeff a *
              (if i ≤ a
                then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
                else 0) := by
      rw [hk]
      ring
    rw [hPi]
    have hSmem : (∑ a ∈ (Finset.range (N + 1)).erase i, P.coeff a *
        (if i ≤ a
          then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
          else 0)) ∈ (Int.castRingHom ℂ).range := by
      refine Subring.sum_mem _ fun a ha => ?_
      by_cases hia : i ≤ a
      · have haN : a ≤ N := by
          have := Finset.mem_range.mp (Finset.mem_of_mem_erase ha)
          omega
        have hlt : i < a := lt_of_le_of_ne hia (Ne.symm (Finset.ne_of_mem_erase ha))
        obtain ⟨z, hz⟩ := hIH a haN hlt
        rw [ite_eq_left hia, ← hz]
        refine Subring.mul_mem _ (RingHom.mem_range.mpr ⟨z, rfl⟩)
          (RingHom.mem_range.mpr
            ⟨PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N),
              by rw [Int.coe_castRingHom]⟩)
      · rw [ite_eq_right hia, mul_zero]
        exact Subring.zero_mem _
    obtain ⟨zS, hzS⟩ := RingHom.mem_range.mp hSmem
    exact ⟨PowerSeries.coeff (N - i) T - zS, by rw [map_sub, hzS, Int.coe_castRingHom]⟩

  have hmemP : ∀ i : ℕ, i ≤ N → P.coeff i ∈ Set.range ⇑(Int.castRingHom ℂ) := by
    have H : ∀ j : ℕ, ∀ i : ℕ, i ≤ N → N - i ≤ j →
        P.coeff i ∈ Set.range ⇑(Int.castRingHom ℂ) := by
      intro j
      induction j with
      | zero =>
        intro i hi hj
        exact hstep i hi fun a ha hia => absurd hia (by omega)
      | succ j IH =>
        intro i hi hj
        exact hstep i hi fun a ha hia => IH a ha (by omega)
    exact fun i hi => H N i hi (by omega)

  have hlifts : P ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rcases (show n ≤ N ∨ N < n from by omega) with hn | hn
    · exact hmemP n hn
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPdeg hn)]
      exact ⟨0, map_zero _⟩
  obtain ⟨G, hG⟩ := (Polynomial.mem_lifts P).mp hlifts

  have hGcoeff : ∀ n : ℕ, ((G.coeff n : ℤ) : ℂ) = P.coeff n := by
    intro n
    rw [← hG, Polynomial.coeff_map, Int.coe_castRingHom]
  have hGN : G.coeff N = PowerSeries.constantCoeff T := by
    apply Int.cast_injective (α := ℂ)
    rw [hGcoeff N, hPN]
  have hGdeg : G.natDegree = N := by
    refine le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_)
      (Polynomial.le_natDegree_of_ne_zero ?_)
    · apply Int.cast_injective (α := ℂ)
      rw [hGcoeff m, Int.cast_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPdeg hm)
    · rw [hGN]
      exact h0
  refine ⟨G, hGdeg, hGN, ?_⟩

  have hblock : HahnSeries.single (1 : ℤ) (1 : ℤ)
      * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24
      = HahnSeries.single (1 : ℤ) 1
        * HahnSeries.ofPowerSeries ℤ ℤ (dedekindEtaUnit.map (Int.castRingHom ℤ)) := by
    rw [← map_pow, ← dedekindEtaUnit, ModularCurve.W1.powerSeries_map_intCast_self]
  have hZsum : Polynomial.aeval (jqModC ℤ) G
      * (HahnSeries.single (1 : ℤ) 1
          * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24) ^ N
      = ∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (G.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N)) := by
    rw [hblock, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
      Polynomial.sum_over_range' G (fun n => by rw [map_zero, zero_mul]) (N + 1)
        (show G.natDegree < N + 1 by omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, ModularCurve.W1.algebraMap_laurent_eq_single,
      ModularCurve.W1.jqModC_pow_mul_etaBlock ℤ a N,
      ModularCurve.W1.powerSeries_map_intCast_self jNum,
      ModularCurve.W1.powerSeries_map_intCast_self dedekindEtaUnit]
  rw [hZsum]
  ext g
  have hfinal : (((HahnSeries.ofPowerSeries ℤ ℤ T).coeff g : ℤ) : ℂ)
      = (((∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (G.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N))).coeff g
          : ℤ) : ℂ) :=
    calc (((HahnSeries.ofPowerSeries ℤ ℤ T).coeff g : ℤ) : ℂ)
      = (HahnSeries.ofPowerSeries ℤ ℂ (T.map (Int.castRingHom ℂ))).coeff g :=
        (ModularCurve.W1.coeff_ofPowerSeries_map T g).symm
    _ = (∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (P.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℂ
                    ((jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ)))).coeff g := by
        rw [hPid]
    _ = ∑ a ∈ Finset.range (N + 1),
          (((HahnSeries.single (0 : ℤ) (G.coeff a)
              * (HahnSeries.single ((N : ℤ) - a) 1
                  * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N))).coeff g
            : ℤ) : ℂ) := by
        rw [HahnSeries.coeff_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [HahnSeries.coeff_single_zero_mul, HahnSeries.coeff_single_zero_mul,
          Int.cast_mul, ← hGcoeff a]
        congr 1
        rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, one_mul, one_mul]
        exact ModularCurve.W1.coeff_ofPowerSeries_map _ _
    _ = (((∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (G.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N))).coeff g
          : ℤ) : ℂ) := by
        rw [HahnSeries.coeff_sum]
        exact (map_sum (Int.castRingHom ℂ) _ _).symm
  exact_mod_cast hfinal

end StarBank

namespace W1

/-- The `Y`-degree of the transported datum is `ψ(N)`: mapping `Φ` along the level-one
evaluation does not change its degree, and the datum's degree is `ψ(N)` by construction.
The pin's `S_…:33`; the port's two copies of it (`ModularEquation/Split.lean`,
`ModularPolynomialUniquenessIrreducible.lean`) are `private`, so the row is transcribed here at
the pin's name — its only consumer, `toAdjoin_eq_minpoly_all`, is the port's own public
`ModularCurve.toAdjoin_eq_minpoly_all` and folds this `rw` into its proof. -/
theorem natDegree_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

end W1

namespace ModularPolynomialData

/-- **The datum is determined by its polynomial.**  Two `ModularPolynomialData`s at the same level
are equal: applying `evalAtJGen` to `Φ` is injective, and the image is `toAdjoin`, which by
`toAdjoin_eq_minpoly_all` is `minpoly ℚ⟮jq⟯ (jqN N)` on both sides.  The pin's `S_…:54` (its
`private` copy) and `Theorems/Thm_…:8` (public) — stated once, public, here. -/
theorem eq_all (N : ℕ) [NeZero N] (d d' : ModularPolynomialData N) : d = d' := by
  have h : d.Φ = d'.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    change d.toAdjoin = d'.toAdjoin
    rw [toAdjoin_eq_minpoly_all, toAdjoin_eq_minpoly_all]
  cases d; cases d'
  cases h
  rfl

/-- The datum's type is a subsingleton: `eq_all`, packaged.  The pin's `S_…:66`, verbatim. -/
theorem subsingleton (N : ℕ) [NeZero N] : Subsingleton (ModularPolynomialData N) :=
  ⟨eq_all N⟩

end ModularPolynomialData

end ModularCurve
