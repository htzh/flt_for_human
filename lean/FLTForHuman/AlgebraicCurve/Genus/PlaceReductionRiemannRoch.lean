/-
Riemann–Roch under a place reduction.

For a curve `F/K` with a finite extension of the constant field `E/K` and `FE = E ⊗ F`, a place
reduction `ρ : Place E FE → Place K F` pulls a divisor back along `Divisor.mapDomain`; this module
proves that the Riemann–Roch space does not grow under it:

* `exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le` — there is a finite set of
  places outside which `mapDomain ρ` is controlled, and `finrank 𝓛 (mapDomain ρ D) ≤ finrank 𝓛 D`;
* `finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction` — the same
  inequality from the residue span (`finrank_span_residue_eq_finrank`), in the direction the genus
  comparison consumes.

The first row carries **14 premises** — the set's named risk. Its engine is assembled from four
already-ported layers, and this module is the assembly that no earlier set could place because it
needs all four at once: AF106C's `Divisor.mapDomain_placeReduction_eq_ord_of_retraction` and the
section/retraction calculus (`DivisorPlaceReduction.lean`, `RegularProlongationRetraction.lean`), the
constant-field-extension place dictionary (`Place/ConstantFieldExtension.lean`), the genus equality
and the index theorems (`Genus/ConstantFieldExtension.lean`, `Genus/Index.lean`,
`Genus/Stichtenoth.lean`, `ResidueTheorem/RRAssembly.lean`), and the canonical-divisor data
(`Canonical/HasCanonicalDivisor.lean`, `Canonical/DCoordGenerates.lean`).

The statements are the pin's `Divisor.*` namespace statements; the home is the `Genus/` directory
because the subject is the *genus* conclusion — a Riemann–Roch dimension compared across a base
change — and not the divisor calculus itself.

## The rows

* `AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le` — 687 pin `S_` lines.
* `AlgebraicCurve.Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction` — 510 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction.lean

PORT NOTES (SET-AF107, order B).

* **Engine diff.** The two `S_` wires carry **52 rows** (30 + 22) over **41 distinct names**.
  This module declares **24** of them — the 22 unique engine rows plus the two headlines, stated
  at the `Theorems/` wrappers' names (`…Divisor.exists_finset_…_le`,
  `…Divisor.finrank_riemannRochSpace_le_…`), which is what the pin's two `solution` rows export —
  and **substitutes 17**. The pin's repeated `RationalPlace` block is one block in the port, so the
  two files' shared rows (`valuation_algebraMap_eq_one`, `valuation_algebraMap_le_one`,
  `const_unique`, `sigmaFun`, `sigmaFun_spec`, `sigmaFun_eq_iff`, `sigma`, `sigma_spec`,
  `sigma_eq_iff`, `ker_sigma`, `sigma_algebraMap`, `mapDomain_nonneg`) are written once here.
* **Namespaces.** The generated labels `DeuringGenericUpperBound` and `DeuringLowerSemicontinuity`
  become the subject namespaces `AlgebraicCurve.PlaceReductionRiemannRoch.GenericUpperBound` and
  `…LowerSemicontinuity` (the pin's two engines, kept apart because each has its own `main`). The
  pin's `p2m_open`/`p2m_export`/`p2m_reactivate` staging, its `attribute [-instance]`/`[-simp]`
  walls and its `import Mathlib` are not transcribed; **no** `set_option` is installed here.
* **Substitutions taken (17, all public in the port, imported and never re-proved).**
  `valuation_algebraMap_eq_one`, `valuation_algebraMap_le_one`, `const_unique`, `sigmaFun`,
  `sigmaFun_spec`, `sigmaFun_eq_iff`, `sigma`, `sigma_spec`, `sigma_eq_iff` are
  `AlgebraicCurve.DeuringNormResidue.*` — byte-identical to the pin's block, and the same
  `A`-hypothesis set (`A : ValuationSubring E`, `hKA`, `hArat`), so the `sigma`-side of the pin's
  engine costs nothing. `ker_sigma` is `AlgebraicCurve.PlaceInftyReduction.ker_sigma` (same
  statement, proved there from `Place.ord_nonneg_of_mem`'s toolbox). `ord_nonneg_of_mem`,
  `mem_iff_ord_nonneg`, `one_le_ord_of_mem_of_inv_not_mem`, `ord_eq_zero_of_mem_of_inv_mem` are the
  pin's `vs`-named twins in `AlgebraicCurve.Place` (`…_vs`, `…_vs`, `…`,
  `…` — the pin's no-nonzero-hypothesis forms). `ord_algebraMap_eq_zero` is
  `AlgebraicCurve.Place.ord_algebraMap` (`v.ord (algebraMap K F c) = 0`), *not* the
  `port_advise` match. `hasCanonicalDivisor_of_fg` is
  `AlgebraicCurve.hasCanonicalDivisor_of_charZero` (`IsCurveOver/ConstantFieldExtensionExists.lean`).
  `linearIndependent_pow_of_transcendental` is `AlgebraicCurve.linearIndependent_pow_of_transcendental`
  (`Genus/Stichtenoth.lean`), whose pin-shaped statement is that of the `S_` file's row.
* **Substitution rejected.** `port_advise` sends `ord_algebraMap_eq_zero` to
  `ModularCurve.Es1a1.es1a10_ncPole_ord_algebraMap` (`WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean`)
  on the strength of the bare type `Place.ord (algebraMap _ _ _) = 0`; its `Place` is a different
  one and its hypotheses are the pole side of the `X₁` dictionary. The honest match is
  `AlgebraicCurve.Place.ord_algebraMap` (FR-0266, read the body).
* **One premise needs an instance the pin does not.** The pin's `hasCanonicalDivisor_of_fg`
  needs `[IsAlgClosed K]`; the port's `hasCanonicalDivisor_of_charZero` needs `[CharZero K]`. Both
  uses here are dischargeable: the ambient `[CharZero K]` covers `K`, and for `E` the derivation is
  the one line `charZero_of_injective_algebraMap (algebraMap K E).injective` (the same one
  `genus_eq_of_constantFieldExtension_of_isAlgClosed` uses). No statement moves.
* **`haveI`/`letI` are written `have`/`let` (23 sites).** The pin's `haveI`/`letI` are all
  instance introductions inside a `Prop` goal, which `linter.style.haveILetI` flags; per the
  set's house policy they are rewritten rather than silenced, and in this Lean a `have`/`let`
  whose type is a class is still a local instance for instance resolution. **No linter is silenced
  in this module**, and the module elaborates with no output at all at the edit loop's 200 k cap.
* **One proof body departs from the pin.** `linearIndependent_adjoin_simple_of_pow_mul` (and
  `algebraMap_mem_adjoin_simple` with it) is `private` in `AlgebraicCurve/Genus/ConstantFieldExtension.lean`,
  so it is not importable and is transcribed. The pin closes its proof with
  `LinearIndependent.localization (IntermediateField.adjoin K' {x}) (nonZeroDivisors …)`, which
  needs the instance `Algebra ↥K'[x] ↥K'⟮x⟯` — absent from this mathlib (`synthInstanceFailed`,
  measured). The body transcribed is the port's own private proof of the same statement, which
  folds the subalgebra step into the denominator-clearing argument. The **statement is the pin's**
  and its hash matches the `S_` row.
* **Heartbeat probe pair, recorded and NOT installed.** The whole module is silent at
  `-DmaxHeartbeats=40000` and first fails at `20000`, on `finrank_adjoin_algebraMap_eq`
  (`…:770:0: (deterministic) timeout at whnf, maximum number of heartbeats (20000) has been
  reached`). Down the ladder the first over-budget declaration is `step` at `10000` (`:461`),
  `apply_eq_of_comap_eq` at `5000` (`:319`) and the `simp` inside `sigma_algebraMap` at `1000`
  (`:169`), i.e. no single subterm dominates: the two Riemann–Roch numerics carry the top cost and
  the residue/valuation instantiation the rest. So the module needs ≤ 40 k, five times under the
  edit loop's 200 k cap and a hundred under the lakefile's 4 M. The module carries no
  `set_option maxHeartbeats` / `synthInstance.maxHeartbeats`; the pin carries none either.
* **The one `dedup` cluster is the pin's headline↔engine pair.** `dedup --within` reports one
  `shape` cluster (2 copies, intra-module): `…LowerSemicontinuity.main` against the second headline
  `…Divisor.finrank_riemannRochSpace_le_…`, removable 21 lines. That is the pin's own
  `solution`/`main` pair — the pin's `solution` row *is* `DeuringLowerSemicontinuity.main K F E FE …`
  applied, so the headline's binder list necessarily restates `main`'s and cannot be removed without
  changing the wrapper's statement this module is wired to. The first headline is a *different*
  statement from `GenericUpperBound.main` (`Good K F D`, a `Prop` with a finite set), which is why
  the order stresses that the second row is not implied by the first: they are two engines, not one.
* **Gates measured on this module.** `check_port --force`: 24 `ok`, 0 mismatch, 0 missing, 0 own.
  Edit loop at `-DmaxHeartbeats=200000`: silent (no output at all). Locked `lake build`: 0 warning
  lines naming this file. `#print axioms` on all 24 public declarations:
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. `move_dead --dry-run`: 0 declarations,
  0 lines. Engine diff: 4 pin sources, 54 pin rows, 24 module declarations — 23 by statement hash,
  0 by name only, 0 unaccounted.
-/

import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.DivisorPlaceReduction
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionExists
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.RegularProlongationFinrank
import FLTForHuman.AlgebraicCurve.RegularProlongationRetraction
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

open AlgebraicCurve
open KaehlerDifferential

set_option autoImplicit false

namespace AlgebraicCurve

namespace PlaceReductionRiemannRoch

open DeuringNormResidue

/-! ## The rational-place residue, shared by the two engines

The pin repeats the whole `RationalPlace` block in both of its `S_` files; here it is
`AlgebraicCurve.DeuringNormResidue`'s, imported.  What is *not* there and is written once below is
`sigma_apply`, `sigma_algebraMap` and `sigma_surjective` (the pin's rows of the same names), plus the
`Finsupp.mapDomain` non-negativity that both engines need.

Substituted (imported, not re-proved) from the port's own copies of the pin's helpers:
`valuation_algebraMap_eq_one`, `valuation_algebraMap_le_one`, `const_unique`, `sigmaFun`,
`sigmaFun_spec`, `sigmaFun_eq_iff`, `sigma`, `sigma_spec`, `sigma_eq_iff` are
`AlgebraicCurve.DeuringNormResidue.*` (byte-identical block); `ker_sigma` is
`AlgebraicCurve.PlaceInftyReduction.ker_sigma`. -/

section RationalPlace

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
  (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)

theorem sigma_apply (a : A) : sigma A hKA hArat a = sigmaFun A hArat a := rfl

theorem sigma_algebraMap (k : K) :
    sigma A hKA hArat ⟨algebraMap K E k, hKA k⟩ = k := by
  rw [sigma_eq_iff]
  simp

theorem sigma_surjective : Function.Surjective (sigma A hKA hArat) :=
  fun k => ⟨⟨algebraMap K E k, hKA k⟩, sigma_algebraMap A hKA hArat k⟩

end RationalPlace

theorem mapDomain_nonneg {α β : Type*} (r : α → β) {G : α →₀ ℤ} (hG : ∀ a, 0 ≤ G a) (b : β) :
    0 ≤ Finsupp.mapDomain r G b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun a _ => ?_
  show 0 ≤ Finsupp.single (r a) (G a) b
  rw [Finsupp.single_apply]
  split_ifs
  · exact hG a
  · exact le_rfl

/-! ## The generic-degree upper bound

The pin's `DeuringGenericUpperBound`: Riemann–Roch in both directions gives `finrank 𝓛 (mapDomain ρ D)
≤ finrank 𝓛 D` for divisors of degree at least `2g - 1` (`base`), and single-place induction
(`step`) descends to every divisor, with `sep` supplying the finite set of places the reduction must
avoid. -/

namespace GenericUpperBound

section PlaceToolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- A valuation subring between `v.toValuationSubring` and `⊤` that is not `⊤` is
`v.toValuationSubring`: the order at `v` separates points. -/
theorem toValuationSubring_eq_of_le_of_ne_top {B : ValuationSubring F}
    (h : v.toValuationSubring ≤ B) (hB : B ≠ ⊤) : v.toValuationSubring = B := by
  refine le_antisymm h fun y hy => ?_
  by_contra hyp
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyp (zero_mem _)
  have hordy : v.ord y < 0 := by
    by_contra h'
    exact hyp ((v.mem_iff_ord_nonneg_vs y).mpr (not_lt.mp h'))
  apply hB
  refine eq_top_iff.mpr fun z _ => ?_
  rcases eq_or_ne z 0 with rfl | hz0
  · exact zero_mem _
  obtain ⟨m, hm⟩ : ∃ m : ℕ, -v.ord z ≤ m := ⟨(-v.ord z).toNat, Int.self_le_toNat _⟩
  have hyi0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have h1 : 1 ≤ -v.ord y := by omega
  have hw : z * y⁻¹ ^ m ∈ v.toValuationSubring := by
    rw [v.mem_iff_ord_nonneg_vs, v.ord_mul hz0 (pow_ne_zero _ hyi0), ← zpow_natCast, v.ord_zpow,
      v.ord_inv]
    have h3 : (m : ℤ) ≤ (m : ℤ) * -v.ord y := le_mul_of_one_le_right (Nat.cast_nonneg m) h1
    linarith
  have hz : z = z * y⁻¹ ^ m * y ^ m := by
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hy0, one_pow, mul_one]
  rw [hz]
  exact mul_mem (h hw) (pow_mem hy m)

theorem eq_of_le {v w : Place K F} (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  Place.ext (toValuationSubring_eq_of_le_of_ne_top v h w.ne_top')

end PlaceToolkit

section Degree

theorem degree_eq_sum_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum fun _ n => n := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  simp [hdeg v]

theorem degree_mapDomain_of_deg_eq_one {K F K' F' : Type*} [Field K] [Field F] [Algebra K F]
    [Field K'] [Field F'] [Algebra K' F']
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K' F', w.deg = 1)
    (r : Place K' F' → Place K F) (D : Divisor K' F') :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  rw [degree_eq_sum_of_deg_eq_one hdeg, degree_eq_sum_of_deg_eq_one hdeg',
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

end Degree

section OneField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]

/-- Riemann–Roch's numerical content: Riemann's inequality, and equality in the range where the
index of specialty vanishes. -/
theorem riemannRoch_numerics [HasCanonicalDivisor (K := K) (F := F)]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (D : Divisor K F) :
    Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ) ∧
      (2 * (genus K F : ℤ) - 1 ≤ Divisor.degree D →
        (ell D : ℤ) = Divisor.degree D + 1 - (genus K F : ℤ)) := by
  obtain ⟨x, hx, hfd⟩ := hfg
  have : Algebra.EssFiniteType K F := essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  have : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have hRR : ∀ D' : Divisor K F,
      (ell D' : ℤ) - (ell (canonicalDivisorOf hω - D') : ℤ) =
        Divisor.degree D' + 1 - (genus K F : ℤ) := fun D' =>
    functionFieldRiemannRoch_of_isAlgClosed_of_transcendental hx hfd hω D'
  have h0 := hRR 0
  have hW := hRR (canonicalDivisorOf hω)
  have hD := hRR D
  rw [sub_zero, map_zero, zero_add] at h0
  rw [sub_self] at hW
  have hdegW : Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 := by linarith
  refine ⟨?_, fun hdeg => ?_⟩
  · have : (0 : ℤ) ≤ ell (canonicalDivisorOf hω - D) := Int.natCast_nonneg _
    linarith
  · have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
      rw [map_sub, hdegW]
      linarith
    have hzero : ell (canonicalDivisorOf hω - D) = 0 := by
      show Module.finrank K ↥(LSpace (canonicalDivisorOf hω - D)) = 0
      rw [lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
    rw [hzero, Nat.cast_zero, sub_zero] at hD
    exact hD

end OneField

/-- The pin's `Good K F D`: the conclusion of the module, made a hypothesis so that the induction of
`good_of_le` can consume it. -/
def Good (K F : Type*) {E FE : Type*} [Field K] [Field F] [Field E] [Field FE] [Algebra K F]
    [Algebra E FE] [Algebra K E] [Algebra F FE] (D : Divisor E FE) : Prop :=
  ∃ S : Finset E, (0 : E) ∉ S ∧
    ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
      (∀ k : K, algebraMap K E k ∈ A) →
      (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
      (∀ s ∈ S, A.valuation s = 1) →
      (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
        ∃ a : E, a ∈ A ∧
          P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
      Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) ≤
        Module.finrank E (riemannRochSpace D)

section Main

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
  [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
  [IsAlgClosed K] [CharZero K] [IsAlgClosed E] [IsCurveOver K F] [IsCurveOver E FE]

omit [CharZero K] [IsAlgClosed E] [IsCurveOver E FE] in

/-- A reduction compatible with the restriction of `P₀` agrees with `p₀` there: the residue of
`p₀` is the constant field, so `r P₀` cannot be a strictly larger valuation subring. -/
theorem apply_eq_of_comap_eq
    {p₀ : Place K F} {P₀ : Place E FE}
    (hP₀ : P₀.toValuationSubring.comap (algebraMap F FE) = p₀.toValuationSubring)
    {A : ValuationSubring E} {r : Place E FE → Place K F}
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) :
    r P₀ = p₀ := by
  symm
  refine eq_of_le fun f hf => ?_

  have : Module.Finite K p₀.ResidueField := IsCurveOver.finite_residueField p₀
  have : Algebra.IsIntegral K p₀.ResidueField := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K p₀.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨k, hk⟩ := hbij.2 (IsLocalRing.residue p₀.toValuationSubring ⟨f, hf⟩)
  have hmax : (⟨f, hf⟩ : p₀.toValuationSubring) - algebraMap K p₀.toValuationSubring k ∈
      IsLocalRing.maximalIdeal p₀.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hk,
      IsScalarTower.algebraMap_apply K p₀.toValuationSubring p₀.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hr]
  refine ⟨algebraMap K E k, hKA k, ?_⟩
  have hu : f - algebraMap K F k ∈ p₀.toValuationSubring := sub_mem hf (p₀.algebraMap_mem' k)
  have huO : algebraMap F FE (f - algebraMap K F k) ∈ P₀.toValuationSubring := by
    rw [← ValuationSubring.mem_comap, hP₀]
    exact hu
  have hEq : algebraMap F FE f - algebraMap E FE (algebraMap K E k) =
      algebraMap F FE (f - algebraMap K F k) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply K E FE, ← IsScalarTower.algebraMap_apply K F FE]
  rw [hEq]
  refine (P₀.toValuationSubring.valuation_lt_one_iff ⟨_, huO⟩).mp ?_
  by_contra hnot
  have hunit : IsUnit (⟨algebraMap F FE (f - algebraMap K F k), huO⟩ : P₀.toValuationSubring) := by
    by_contra h
    exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
  have hv1 : P₀.toValuationSubring.valuation (algebraMap F FE (f - algebraMap K F k)) = 1 :=
    (P₀.toValuationSubring.valuation_eq_one_iff _).mp hunit
  have hu0 : f - algebraMap K F k ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hv1
    exact zero_ne_one hv1
  have hinv : (f - algebraMap K F k)⁻¹ ∈ p₀.toValuationSubring := by
    rw [← hP₀, ValuationSubring.mem_comap, map_inv₀, ← ValuationSubring.valuation_le_one_iff]
    exact le_of_eq (by rw [map_inv₀, hv1, inv_one])
  have hunit' : IsUnit ((⟨f, hf⟩ : p₀.toValuationSubring) -
      algebraMap K p₀.toValuationSubring k) := by
    have hcoe : (((⟨f, hf⟩ : p₀.toValuationSubring) - algebraMap K p₀.toValuationSubring k :
        p₀.toValuationSubring) : F) = f - algebraMap K F k := by
      simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
    refine isUnit_iff_exists_inv.mpr ⟨⟨(f - algebraMap K F k)⁻¹, hinv⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one]
    exact mul_inv_cancel₀ hu0
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmax) hunit'

/-- The finite set of places a reduction must avoid, at one place `Q ≠ P₀` over `p₀`. -/
theorem sep
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    {p₀ : Place K F} {P₀ : Place E FE}
    (huniq : ∀ Q : Place E FE,
      Q.toValuationSubring.comap (algebraMap F FE) = p₀.toValuationSubring → Q = P₀)
    {Q : Place E FE} (hQ : Q ≠ P₀) :
    ∃ T : Finset E, (0 : E) ∉ T ∧
      ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
        (∀ k : K, algebraMap K E k ∈ A) →
        (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
        (∀ s ∈ T, A.valuation s = 1) →
        (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
          ∃ a : E, a ∈ A ∧
            P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
        r Q ≠ p₀ := by
  classical
  by_cases hint : ∀ f : F, algebraMap F FE f ∈ Q.toValuationSubring
  ·
    obtain ⟨e, he⟩ :=
      (Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension K F hfg E FE hfgE
        hgen).2 Q hint
    obtain ⟨t, ht⟩ : ∃ t : F, t ∉ p₀.toValuationSubring := by
      by_contra h
      exact p₀.ne_top' (eq_top_iff.mpr fun t _ => not_not.mp (not_exists.mp h t))
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact ht (zero_mem _)
    have heinj : Function.Injective e := (e : F →+* E).injective
    have het : e t ≠ 0 := (map_ne_zero_iff e heinj).mpr ht0
    refine ⟨{e t}, ?_, fun A r hKA hArat hT hr hrQ => ?_⟩
    · rw [Finset.mem_singleton]
      exact fun h => het h.symm
    have hetA : e t ∈ A :=
      (A.valuation_le_one_iff _).mp (le_of_eq (hT _ (Finset.mem_singleton_self _)))
    have hmem : t ∈ (r Q).toValuationSubring := (hr Q t).mpr ⟨e t, hetA, he t⟩
    rw [hrQ] at hmem
    exact ht hmem
  ·
    obtain ⟨f, hf⟩ := not_forall.mp hint
    refine ⟨∅, by simp, fun A r hKA hArat _ hr hrQ => ?_⟩
    have hle : p₀.toValuationSubring ≤ Q.toValuationSubring.comap (algebraMap F FE) := by
      intro u hu
      rw [ValuationSubring.mem_comap]
      rw [← hrQ] at hu
      obtain ⟨a, -, hva⟩ := (hr Q u).mp hu
      have hmem : algebraMap F FE u - algebraMap E FE a ∈ Q.toValuationSubring :=
        (Q.toValuationSubring.valuation_le_one_iff _).mp hva.le
      have := add_mem hmem (Q.algebraMap_mem' a)
      rwa [sub_add_cancel] at this
    have hne : Q.toValuationSubring.comap (algebraMap F FE) ≠ ⊤ := by
      intro htop
      have hmem : f ∈ (⊤ : ValuationSubring F) := ValuationSubring.mem_top f
      rw [← htop] at hmem
      exact hf (ValuationSubring.mem_comap.mp hmem)
    exact hQ (huniq Q (toValuationSubring_eq_of_le_of_ne_top p₀ hle hne).symm)

/-- Above the Riemann–Roch threshold the two dimensions agree, so `Good` holds with no exceptional
set at all. -/
theorem base [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := E) (F := FE)]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) (hdeg : 2 * (genus K F : ℤ) - 1 ≤ Divisor.degree D) : Good K F D := by
  refine ⟨∅, by simp, fun A r _ _ _ _ => ?_⟩
  have hgenus : genus E FE = genus K F :=
    genus_eq_of_constantFieldExtension_of_isAlgClosed K F E FE hfg hfgE hgen
  have hdegr : Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D :=
    degree_mapDomain_of_deg_eq_one (fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v)
      (fun w => IsCurveOver.deg_eq_one_of_isAlgClosed w) r D
  have hK := (riemannRoch_numerics (K := K) (F := F) hfg (Finsupp.mapDomain r D)).2
    (by rw [hdegr]; exact hdeg)
  have hE := (riemannRoch_numerics (K := E) (F := FE) hfgE D).1
  rw [hgenus] at hE
  have h : (ell (Finsupp.mapDomain r D) : ℤ) ≤ ell D := by
    rw [hK, hdegr]
    exact hE
  exact_mod_cast h

/-- One step of the induction: `Good` descends from `D + P₀` to `D`. -/
theorem step
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    {p₀ : Place K F} {P₀ : Place E FE}
    (hP₀ : P₀.toValuationSubring.comap (algebraMap F FE) = p₀.toValuationSubring)
    (huniq : ∀ Q : Place E FE,
      Q.toValuationSubring.comap (algebraMap F FE) = p₀.toValuationSubring → Q = P₀)
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    [FiniteDimensional E (LSpace (0 : Divisor E FE))]
    (D : Divisor E FE) (hD : Good K F (D + Finsupp.single P₀ 1)) : Good K F D := by
  classical
  obtain ⟨S', h0S', hS'⟩ := hD
  have hmono : ∀ r : Place E FE → Place K F,
      riemannRochSpace (Finsupp.mapDomain r D) ≤
        riemannRochSpace (Finsupp.mapDomain r (D + Finsupp.single P₀ 1)) := fun r => by
    refine lSpace_mono ?_
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    exact le_add_of_nonneg_right (Finsupp.single_nonneg.mpr zero_le_one)
  by_cases hex : riemannRochSpace (D + Finsupp.single P₀ 1) ≤ riemannRochSpace D
  ·
    refine ⟨S', h0S', fun A r hKA hArat hS hr => ?_⟩
    have := finiteDimensional_lSpace (K := K) (F := F)
      (Finsupp.mapDomain r (D + Finsupp.single P₀ 1))
    have := finiteDimensional_lSpace (K := E) (F := FE) D
    calc Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D))
        ≤ Module.finrank K (riemannRochSpace (Finsupp.mapDomain r (D + Finsupp.single P₀ 1))) :=
          Submodule.finrank_mono (hmono r)
      _ ≤ Module.finrank E (riemannRochSpace (D + Finsupp.single P₀ 1)) := hS' A r hKA hArat hS hr
      _ ≤ Module.finrank E (riemannRochSpace D) := Submodule.finrank_mono hex

  obtain ⟨f, hf1, hf2⟩ : ∃ f, f ∈ riemannRochSpace (D + Finsupp.single P₀ 1) ∧
      f ∉ riemannRochSpace D := by
    rw [SetLike.le_def, not_forall] at hex
    obtain ⟨f, hf⟩ := hex
    exact ⟨f, Classical.not_imp.mp hf⟩
  have hfne : f ≠ 0 := by
    rintro rfl
    exact hf2 (zero_mem _)
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := E) f hfne
  have hlow : ∀ Q : Place E FE, -(D Q) - Finsupp.single P₀ 1 Q ≤ Df Q := fun Q => by
    have h := ((mem_riemannRochSpace_iff.mp hf1) Q).resolve_left hfne
    rw [Finsupp.add_apply] at h
    rw [hDf]
    linarith
  have hDfP₀ : Df P₀ = -(D P₀) - 1 := by
    obtain ⟨Q, hQ⟩ : ∃ Q : Place E FE, ¬(f = 0 ∨ -(D Q) ≤ Q.ord f) := by
      by_contra h
      exact hf2 (mem_riemannRochSpace_iff.mpr fun Q => not_not.mp (not_exists.mp h Q))
    rw [not_or, not_le, ← hDf] at hQ
    have h1 := hlow Q
    by_cases hQP : Q = P₀
    · subst hQP
      rw [Finsupp.single_eq_same] at h1
      linarith [hQ.2]
    · rw [Finsupp.single_eq_of_ne hQP] at h1
      linarith [hQ.2]

  obtain ⟨G, hGdef⟩ : ∃ G : Divisor E FE, G = Df + (D + Finsupp.single P₀ 1) := ⟨_, rfl⟩
  have hG0 : ∀ Q, 0 ≤ G Q := fun Q => by
    rw [hGdef, Finsupp.add_apply, Finsupp.add_apply]
    have := hlow Q
    linarith
  have hGP₀ : G P₀ = 0 := by
    rw [hGdef, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, hDfP₀]
    ring

  have hsep' : ∀ Q : Place E FE, Q ≠ P₀ → ∃ T : Finset E, (0 : E) ∉ T ∧
      ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
        (∀ k : K, algebraMap K E k ∈ A) →
        (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
        (∀ s ∈ T, A.valuation s = 1) →
        (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
          ∃ a : E, a ∈ A ∧
            P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
        r Q ≠ p₀ :=
    fun Q hQ => sep hfg hfgE hgen huniq hQ
  choose! T hT0 hT using hsep'
  refine ⟨S' ∪ G.support.biUnion T, ?_, fun A r hKA hArat hS hr => ?_⟩
  · rw [Finset.mem_union, not_or]
    refine ⟨h0S', fun hmem => ?_⟩
    obtain ⟨Q, hQ, h0Q⟩ := Finset.mem_biUnion.mp hmem
    have hQne : Q ≠ P₀ := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hQ) hGP₀
    exact hT0 Q hQne h0Q
  have hS'A : ∀ s ∈ S', A.valuation s = 1 := fun s hs => hS s (Finset.mem_union_left _ hs)
  have hrP₀ : r P₀ = p₀ := apply_eq_of_comap_eq hP₀ hKA hr
  have hrQ : ∀ Q ∈ G.support, r Q ≠ p₀ := fun Q hQ => by
    have hQne : Q ≠ P₀ := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hQ) hGP₀
    exact hT Q hQne A r hKA hArat
      (fun s hs => hS s (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨Q, hQ, hs⟩))) hr

  obtain ⟨O, ρ, hOA, hker, -, hreg, hρF⟩ :=
    exists_regularProlongation_retraction_of_constantField_valuationSubring
      K F E FE hfg hfgE hgen A hKA (sigma A hKA hArat) (PlaceInftyReduction.ker_sigma A hKA hArat)
      (sigma_algebraMap A hKA hArat)
  obtain ⟨c, hcf, hρc⟩ := hreg f hfne
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hρc
    have h0 : (⟨(0 : E) • f, hcf⟩ : O) = 0 := Subtype.ext (zero_smul _ _)
    rw [h0, map_zero]
  have hDcf : ∀ Q : Place E FE, Df Q = Q.ord (((⟨c • f, hcf⟩ : O) : FE)) := fun Q => by
    show Df Q = Q.ord (c • f)
    rw [hDf Q, Algebra.smul_def, Q.ord_mul ((map_ne_zero _).mpr hc0) hfne,
      Place.ord_algebraMap Q c, zero_add]

  have hcomp : ∀ v : Place K F, Finsupp.mapDomain r Df v = v.ord (ρ ⟨c • f, hcf⟩) := fun v =>
    Divisor.mapDomain_placeReduction_eq_ord_of_retraction K F E FE hfg hfgE hgen A r hKA hArat hr
      O ρ hOA hker hρF ⟨c • f, hcf⟩ hρc Df hDcf v
  have hgin : ρ ⟨c • f, hcf⟩ ∈
      riemannRochSpace (Finsupp.mapDomain r (D + Finsupp.single P₀ 1)) := by
    refine mem_riemannRochSpace_iff.mpr fun v => Or.inr ?_
    have h := mapDomain_nonneg r hG0 v
    rw [hGdef, Finsupp.mapDomain_add, Finsupp.add_apply, hcomp] at h
    linarith
  have hGr : Finsupp.mapDomain r G p₀ = 0 := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    show Finsupp.single (r Q) (G Q) p₀ = 0
    exact Finsupp.single_eq_of_ne (Ne.symm (hrQ Q hQ))
  have hgnot : ρ ⟨c • f, hcf⟩ ∉ riemannRochSpace (Finsupp.mapDomain r D) := by
    intro hmem
    have h1 := ((mem_riemannRochSpace_iff.mp hmem) p₀).resolve_left hρc
    have h2 := hGr
    rw [hGdef, Finsupp.mapDomain_add, Finsupp.mapDomain_add, Finsupp.add_apply,
      Finsupp.add_apply, hcomp, Finsupp.mapDomain_single, hrP₀, Finsupp.single_eq_same] at h2
    linarith
  have hlt : riemannRochSpace (Finsupp.mapDomain r D) <
      riemannRochSpace (Finsupp.mapDomain r (D + Finsupp.single P₀ 1)) :=
    lt_of_le_of_ne (hmono r) fun h => hgnot (by rw [h]; exact hgin)
  have := finiteDimensional_lSpace (K := K) (F := F)
    (Finsupp.mapDomain r (D + Finsupp.single P₀ 1))
  have := finiteDimensional_lSpace (K := E) (F := FE) D
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have h4 := hS' A r hKA hArat hS'A hr
  have h5 : Module.finrank E (riemannRochSpace (D + Finsupp.single P₀ 1)) ≤
      Module.finrank E (riemannRochSpace D) + 1 := by
    have h := ell_le_ell_sub_single_add_deg (K := E) (F := FE) (D + Finsupp.single P₀ 1) P₀
    rwa [add_sub_cancel_right, IsCurveOver.deg_eq_one_of_isAlgClosed P₀] at h
  omega

/-- The induction over the degree. -/
theorem good_of_le [HasCanonicalDivisor (K := K) (F := F)]
    [HasCanonicalDivisor (K := E) (F := FE)]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    {p₀ : Place K F} {P₀ : Place E FE}
    (hP₀ : P₀.toValuationSubring.comap (algebraMap F FE) = p₀.toValuationSubring)
    (huniq : ∀ Q : Place E FE,
      Q.toValuationSubring.comap (algebraMap F FE) = p₀.toValuationSubring → Q = P₀)
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    [FiniteDimensional E (LSpace (0 : Divisor E FE))] :
    ∀ (m : ℕ) (D : Divisor E FE), 2 * (genus K F : ℤ) - 1 - m ≤ Divisor.degree D →
      Good K F D := by
  intro m
  induction m with
  | zero =>
    intro D h
    exact base hfg hfgE hgen D (by simpa using h)
  | succ m ih =>
    intro D h
    refine step hfg hfgE hgen hP₀ huniq D (ih _ ?_)
    rw [map_add, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed P₀]
    push_cast at h ⊢
    linarith

theorem main
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) : Good K F D := by
  classical
  rcases isEmpty_or_nonempty (Place K F) with hemp | ⟨⟨p₀⟩⟩
  ·
    refine ⟨∅, by simp, fun A r _ _ _ _ => ?_⟩
    have htop : riemannRochSpace (Finsupp.mapDomain r D) = ⊤ :=
      eq_top_iff.mpr fun f _ => mem_riemannRochSpace_iff.mpr fun v => (IsEmpty.false v).elim
    have hnf : ¬FiniteDimensional K F := by
      intro hfin
      obtain ⟨x, hx, -⟩ := hfg
      exact hx (Algebra.IsAlgebraic.isAlgebraic (R := K) x)
    rw [htop, finrank_top, Module.finrank_of_not_finite hnf]
    exact Nat.zero_le _
  · obtain ⟨P₀, hP₀, -, huniq⟩ :=
      Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE hgen p₀
    have : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
      RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F
        (constantsAreBase_of_deg_eq_one p₀ (IsCurveOver.deg_eq_one_of_isAlgClosed p₀))
    have : FiniteDimensional E (LSpace (0 : Divisor E FE)) :=
      RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase E FE
        (constantsAreBase_of_deg_eq_one P₀ (IsCurveOver.deg_eq_one_of_isAlgClosed P₀))
    have := hasCanonicalDivisor_of_charZero K F hfg
    -- The port's `hasCanonicalDivisor_of_charZero` asks `[CharZero E]`, which the pin's
    -- `hasCanonicalDivisor_of_fg` does not; derived here from the ambient `[CharZero K]`.
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
    have := hasCanonicalDivisor_of_charZero E FE hfgE
    exact good_of_le hfg hfgE hgen hP₀ huniq
      ((2 * (genus K F : ℤ) - 1 - Divisor.degree D).toNat) D
      (by linarith [Int.self_le_toNat (2 * (genus K F : ℤ) - 1 - Divisor.degree D)])

end Main

end GenericUpperBound

/-! ## Lower semicontinuity of the Riemann–Roch dimension

The pin's `DeuringLowerSemicontinuity`: the inequality in the direction the genus comparison
consumes, read off the residue span of a regular prolongation
(`RegularProlongation.finrank_span_residue_eq_finrank`). -/

open Module

namespace LowerSemicontinuity

section Degree

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

open Polynomial in

/-- `u` stays linearly independent over `K'⟮x⟯` as soon as every `x^p · u` family is independent
over `K'`. -/
theorem linearIndependent_adjoin_simple_of_pow_mul {K' L : Type*} [Field K'] [Field L]
    [Algebra K' L] (x : L) {ι : Type*} (u : ι → L)
    (h : LinearIndependent K' fun p : ℕ × ι => x ^ p.1 * u p.2) :
    LinearIndependent (IntermediateField.adjoin K' ({x} : Set L)) u := by
  classical
  -- Clear denominators: every element of `K'⟮x⟯` is `p(x) / q(x)` with `q(x) != 0`.  The pin
  -- closes from the subalgebra case by `LinearIndependent.localization`; the instance
  -- `Algebra ↥K'[x] ↥K'⟮x⟯` that needs is not in this mathlib, so the subalgebra step is folded in.
  have key : ∀ l : IntermediateField.adjoin K' ({x} : Set L),
      ∃ p q : K'[X], aeval x q ≠ 0 ∧ (l : L) * aeval x q = aeval x p := by
    intro l
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K' (l : L)).mp l.2
    by_cases hs : aeval x s = 0
    · exact ⟨0, 1, by simp, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
    · exact ⟨r, s, hs, by rw [hrs, div_mul_cancel₀ _ hs]⟩
  rw [linearIndependent_iff'] at h ⊢
  intro s g hg i hi
  choose p q hq hpq using fun j => key (g j)
  set Q : K'[X] := ∏ j ∈ s, q j with hQ
  have hQ0 : aeval x Q ≠ 0 := by
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hq j
  let P : ι → K'[X] := fun j => p j * ∏ k ∈ s.erase j, q k
  have hP : ∀ j ∈ s,
      ((g j : IntermediateField.adjoin K' ({x} : Set L)) : L) * aeval x Q = aeval x (P j) := by
    intro j hj
    rw [hQ, ← Finset.mul_prod_erase s q hj, map_mul, ← mul_assoc, hpq j, ← map_mul]
  have hrelL : ∑ j ∈ s, ((g j : IntermediateField.adjoin K' ({x} : Set L)) : L) * u j = 0 := by
    have := hg
    simpa [IntermediateField.smul_def, smul_eq_mul] using this
  have hrelQ : ∑ j ∈ s, aeval x (P j) * u j = 0 := by
    have := congrArg (fun z : L => z * aeval x Q) hrelL
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hP j hj]; ring
  set N : ℕ := (s.sup fun j => (P j).natDegree) + 1 with hN
  have hdeg : ∀ j ∈ s, (P j).natDegree < N := fun j hj =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (P j).natDegree) hj)
  have hkey := h (Finset.range N ×ˢ s) (fun q => (P q.2).coeff q.1) ?_
  swap
  · rw [← hrelQ, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_eq_sum_range' (hdeg j hj), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_mul_assoc]
  have hPi : P i = 0 := by
    ext k
    by_cases hk : k < N
    · simpa using hkey (k, i) (Finset.mk_mem_product (Finset.mem_range.mpr hk) hi)
    · rw [coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i hi) (not_lt.mp hk))
  have h1 := hP i hi
  rw [hPi, map_zero, mul_eq_zero] at h1
  rcases h1 with h2 | h2
  · exact Subtype.ext h2
  · exact absurd h2 hQ0

theorem algebraMap_mem_adjoin_simple {K A K' B : Type*} [Field K] [Field A] [Field K'] [Field B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra K' B] [Algebra K K'] [IsScalarTower K K' B] (x : A)
    {e : A} (he : e ∈ IntermediateField.adjoin K ({x} : Set A)) :
    algebraMap A B e ∈ IntermediateField.adjoin K' ({algebraMap A B x} : Set B) := by
  have hle : (IntermediateField.adjoin K ({x} : Set A)).map (IsScalarTower.toAlgHom K A B) ≤
      (IntermediateField.adjoin K' ({algebraMap A B x} : Set B)).restrictScalars K := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact IntermediateField.mem_adjoin_simple_self K' (algebraMap A B x)
  exact hle ⟨e, he, rfl⟩

/-- The degree of the constant-field extension, computed from the two generators: a constant-field
extension does not change `[K'⟮x⟯ : K']` — hence `finrank (K'⟮x⟯) F' = finrank (K⟮x⟯) F`. -/
theorem finrank_adjoin_algebraMap_eq [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {x : F} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    finrank (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F' =
      finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  classical
  have := hfin
  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  set x' : F' := algebraMap F F' x with hx'
  set E' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hE'
  set m := finrank E F with hm_def
  let bF := Module.finBasis E F

  let xE : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hxEt : Transcendental K xE := by
    have : Function.Injective (algebraMap E F) := (algebraMap E F).injective
    rw [← transcendental_algebraMap_iff this]
    exact hx
  have hpow : LinearIndependent K fun k : ℕ => xE ^ k := linearIndependent_pow_of_transcendental hxEt
  have h1 : LinearIndependent K fun q : ℕ × Fin m => (xE ^ q.1 • bF q.2 : F) :=
    linearIndependent_smul hpow bF.linearIndependent

  have hW := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F' hfg hfg' hgen h1
  have hW' : LinearIndependent K' fun p : ℕ × Fin m => x' ^ p.1 * algebraMap F F' (bF p.2) := by
    convert hW using 1
    funext p
    simp only [hx', IntermediateField.algebraMap_apply, Algebra.smul_def, map_mul, map_pow, xE]

  set b' : Fin m → F' := fun i => algebraMap F F' (bF i) with hb'
  have hu : LinearIndependent E' b' := linearIndependent_adjoin_simple_of_pow_mul x' b' hW'

  set V : Submodule E' F' := Submodule.span E' (Set.range b') with hV_def
  have hEE' : ∀ e : E, algebraMap F F' (e : F) ∈ E' := fun e =>
    algebraMap_mem_adjoin_simple (K' := K') x e.2
  have hFV : ∀ f : F, algebraMap F F' f ∈ V := by
    intro f
    rw [← bF.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap F F' (bF.repr f i • bF i) =
        (⟨algebraMap F F' (bF.repr f i : F), hEE' _⟩ : E') • b' i := by
      rw [IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul, map_mul,
        smul_eq_mul]
    rw [this]
    exact V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hVV : V * V ≤ V := by
    rw [hV_def, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show b' i * b' j ∈ V
    rw [hb']; dsimp only; rw [← map_mul]; exact hFV _
  have h1V : (1 : F') ∈ V := by simpa using hFV 1
  let A : Subalgebra E' F' :=
    { carrier := V
      mul_mem' := fun ha hb => hVV (Submodule.mul_mem_mul ha hb)
      one_mem' := h1V
      add_mem' := fun ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun e' => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem _ h1V }
  have hAfg : (Subalgebra.toSubmodule A).FG := Submodule.fg_span (Set.finite_range b')
  have hinv : ∀ z ∈ A, z⁻¹ ∈ A := fun z hz =>
    A.inv_mem_of_algebraic (x := ⟨z, hz⟩) (IsIntegral.of_mem_of_fg A hAfg z hz).isAlgebraic
  let IF : IntermediateField K' F' := (A.restrictScalars K').toIntermediateField hinv
  have hIF : IF = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    exact hFV f
  have hVtop : V = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IF := hIF ▸ IntermediateField.mem_top
    exact hz
  have : Module.Finite E' F' := ⟨hVtop ▸ Submodule.fg_span (Set.finite_range b')⟩
  have hle : Module.finrank E' F' ≤ m := by
    have := finrank_range_le_card (R := E') b'
    unfold Set.finrank at this
    rw [← hV_def, hVtop, finrank_top, Fintype.card_fin] at this
    exact this

  refine le_antisymm hle ?_
  simpa using hu.fintype_card_le_finrank

end Degree

/-- A generator transcendental over `K'` is transcendental over the subfield `k` (with `k → K'`
surjective), and the two `adjoin`-extensions have the same degree. -/
theorem transfer_fg {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
    [Algebra k L] [IsScalarTower k K L] (hk : Function.Surjective (algebraMap k K))
    {x : L} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L) :
    Transcendental k x ∧ FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L ∧
      Module.finrank (IntermediateField.adjoin k ({x} : Set L)) L =
        Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
  have hxk : Transcendental k x := hx.restrictScalars (algebraMap k K).injective
  have hrange : Set.range (algebraMap k L) = Set.range (algebraMap K L) := by
    rw [IsScalarTower.algebraMap_eq k K L, RingHom.coe_comp, Set.range_comp, hk.range_eq,
      Set.image_univ]
  have hmem : ∀ y : L, y ∈ IntermediateField.adjoin k ({x} : Set L) ↔
      y ∈ IntermediateField.adjoin K ({x} : Set L) := fun y => by
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield, hrange,
      ← IntermediateField.adjoin_toSubfield, IntermediateField.mem_toSubfield]
  let j : IntermediateField.adjoin k ({x} : Set L) ≃+* IntermediateField.adjoin K ({x} : Set L) :=
    { toFun := fun y => ⟨y, (hmem y).mp y.2⟩
      invFun := fun y => ⟨y, (hmem y).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc : (algebraMap (IntermediateField.adjoin K ({x} : Set L)) L).comp j.toRingHom =
      (RingEquiv.refl L).toRingHom.comp
        (algebraMap (IntermediateField.adjoin k ({x} : Set L)) L) :=
    RingHom.ext fun _ => rfl
  have := hfin
  refine ⟨hxk, ?_, Algebra.finrank_eq_of_equiv_equiv j (RingEquiv.refl L) hc⟩
  exact Module.Finite.of_equiv_equiv j.symm (RingEquiv.refl L) (RingHom.ext fun _ => rfl)

/-- A bijective algebra map does not change the `finrank`. -/
theorem finrank_eq_of_bijective_algebraMap {k K M : Type*} [CommRing k] [CommRing K]
    [AddCommGroup M] [Algebra k K] [Module K M] [Module k M] [IsScalarTower k K M]
    (hk : Function.Bijective (algebraMap k K)) : Module.finrank k M = Module.finrank K M := by
  have h := congr_arg Cardinal.toNat
    (lift_rank_eq_of_equiv_equiv (algebraMap k K) (AddEquiv.refl M) hk
      (fun r m => (algebraMap_smul K r m).symm))
  simp only [Cardinal.toNat_lift] at h
  exact h

/-- The pin's `main`: `finrank 𝓛 D ≤ finrank 𝓛 (mapDomain ρ D)`. -/
theorem main
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) :
    Module.finrank E (riemannRochSpace D) ≤
      Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) := by
  classical

  by_cases hfinD : FiniteDimensional E (riemannRochSpace D)
  swap
  · rw [Module.finrank_of_not_finite hfinD]; exact Nat.zero_le _
  obtain ⟨x₀, hx₀, hfin₀⟩ := id hfg

  have hP : Nonempty (Place E FE) := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have htop : riemannRochSpace D = ⊤ :=
      eq_top_iff.mpr fun f _ => mem_riemannRochSpace_iff.mpr fun v => (IsEmpty.false v).elim
    obtain ⟨y, hy, -⟩ := hfgE
    have hT : FiniteDimensional E (⊤ : Submodule E FE) := htop ▸ hfinD
    have : FiniteDimensional E FE := LinearEquiv.finiteDimensional (Submodule.topEquiv)
    exact hy (Algebra.IsAlgebraic.isAlgebraic (R := E) y)
  obtain ⟨P₀⟩ := hP

  have hL0 : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F
      (AlgebraicCurve.constantsAreBase_of_deg_eq_one (r P₀)
        (IsCurveOver.deg_eq_one_of_isAlgClosed (r P₀)))
  have hfinK : FiniteDimensional K (riemannRochSpace (Finsupp.mapDomain r D)) :=
    AlgebraicCurve.finiteDimensional_lSpace (Finsupp.mapDomain r D)

  obtain ⟨O, ρ, hOA, hker, hconstσ, hreg, hρF⟩ :=
    AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring
      K F E FE hfg hfgE hgen A hKA (sigma A hKA hArat) (PlaceInftyReduction.ker_sigma A hKA hArat)
      (sigma_algebraMap A hKA hArat)
  have hFO : ∀ f : F, algebraMap F FE f ∈ O := fun f => (hρF f).1
  have hρF' : ∀ (f : F) (h : algebraMap F FE f ∈ O), ρ ⟨algebraMap F FE f, h⟩ = f :=
    fun f h => by obtain ⟨h', e⟩ := hρF f; exact e
  have hsurj : Function.Surjective ρ := fun f => ⟨_, hρF' f (hFO f)⟩

  let ιK : K →+* A := (algebraMap K E).codRestrict A hKA
  let φ : K →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp ιK
  have hφσ : ∀ a : A, φ (sigma A hKA hArat a) = IsLocalRing.residue A a := fun a => by
    show IsLocalRing.residue A (ιK _) = _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← PlaceInftyReduction.ker_sigma A hKA hArat,
      RingHom.mem_ker, map_sub, sub_eq_zero]
    exact sigma_algebraMap A hKA hArat _
  have hφ : Function.Bijective φ :=
    ⟨φ.injective, fun z => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
      exact ⟨_, hφσ a⟩⟩
  let e : K ≃+* IsLocalRing.ResidueField A := RingEquiv.ofBijective φ hφ
  let iK : Algebra (IsLocalRing.ResidueField A) K := e.symm.toRingHom.toAlgebra
  let iF : Algebra (IsLocalRing.ResidueField A) F :=
    ((algebraMap K F).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower (IsLocalRing.ResidueField A) K F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkK : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) K) := e.symm.surjective
  have hkKb : Function.Bijective (algebraMap (IsLocalRing.ResidueField A) K) := e.symm.bijective
  have he_symm : ∀ a : A, e.symm (IsLocalRing.residue A a) = sigma A hKA hArat a := fun a => by
    rw [RingEquiv.symm_apply_eq]
    exact (hφσ a).symm
  have hconst : ∀ a : A, ρ ⟨algebraMap E FE a, (hOA a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) F (IsLocalRing.residue A a) := fun a => by
    obtain ⟨h, hh⟩ := hconstσ a
    rw [hh]
    show algebraMap K F _ = algebraMap K F (e.symm _)
    rw [he_symm]
  let R : RegularProlongation A FE F :=
    { integers := O, residue := ρ, algebraMap_mem_iff := hOA, residue_surjective := hsurj,
      ker_residue := hker, residue_algebraMap := hconst, exists_smul_mem := hreg }

  obtain ⟨hx₀k, hfink, hfinrk⟩ := transfer_fg hkK hx₀ hfin₀
  have hCa := AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank A R
    ⟨algebraMap F FE x₀, hFO x₀⟩
    (by rw [show R.residue ⟨algebraMap F FE x₀, hFO x₀⟩ = x₀ from hρF' x₀ _]; exact hx₀k)
    (by
      rw [show R.residue ⟨algebraMap F FE x₀, hFO x₀⟩ = x₀ from hρF' x₀ _]
      have := hfink; exact Module.finrank_pos)
    (by
      rw [show R.residue ⟨algebraMap F FE x₀, hFO x₀⟩ = x₀ from hρF' x₀ _]
      show Module.finrank (IntermediateField.adjoin E ({algebraMap F FE x₀} : Set FE)) FE = _
      rw [finrank_adjoin_algebraMap_eq hfg hfgE hgen hx₀ hfin₀, hfinrk])
    (riemannRochSpace D)

  set S : Set F :=
    {h : F | ∃ f : R.integers, (f : FE) ∈ riemannRochSpace D ∧ R.residue f = h} with hS_def
  have hS : S ⊆ (riemannRochSpace (Finsupp.mapDomain r D) : Set F) := by
    rintro _ ⟨f, hfD, rfl⟩
    by_cases hf0 : R.residue f = 0
    · rw [hf0]; exact Submodule.zero_mem _
    have hfne : (f : FE) ≠ 0 := fun h => hf0 (by
      have : f = 0 := Subtype.ext h
      rw [this, map_zero])
    obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := E) (f : FE) hfne
    have hcomp : ∀ v, Finsupp.mapDomain r Df v = v.ord (ρ f) := fun v =>
      AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction K F E FE hfg hfgE hgen
        A r hKA hArat hr O ρ hOA hker hρF f hf0 Df hDf v
    refine mem_riemannRochSpace_iff.mpr fun v => Or.inr ?_
    have hnn : ∀ P, 0 ≤ (Df + D) P := fun P => by
      rw [Finsupp.add_apply, hDf]
      have := ((mem_riemannRochSpace_iff.mp hfD) P).resolve_left hfne
      linarith
    have h := mapDomain_nonneg r hnn v
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, hcomp] at h
    change -(Finsupp.mapDomain r D v) ≤ v.ord (ρ f)
    linarith

  have hspan : Submodule.span (IsLocalRing.ResidueField A) S ≤
      (riemannRochSpace (Finsupp.mapDomain r D)).restrictScalars (IsLocalRing.ResidueField A) :=
    Submodule.span_le.mpr hS
  have : Module.Finite (IsLocalRing.ResidueField A) K :=
    Module.Finite.of_surjective (Algebra.linearMap (IsLocalRing.ResidueField A) K) hkK
  have hfk : Module.Finite (IsLocalRing.ResidueField A)
      (riemannRochSpace (Finsupp.mapDomain r D)) :=
    Module.Finite.trans K _
  have : Module.Finite (IsLocalRing.ResidueField A)
      ((riemannRochSpace (Finsupp.mapDomain r D)).restrictScalars
        (IsLocalRing.ResidueField A)) := hfk
  calc Module.finrank E (riemannRochSpace D)
      = Module.finrank (IsLocalRing.ResidueField A)
          (Submodule.span (IsLocalRing.ResidueField A) S) := hCa.symm
    _ ≤ Module.finrank (IsLocalRing.ResidueField A)
          ((riemannRochSpace (Finsupp.mapDomain r D)).restrictScalars
            (IsLocalRing.ResidueField A)) := Submodule.finrank_mono hspan
    _ = Module.finrank (IsLocalRing.ResidueField A)
          (riemannRochSpace (Finsupp.mapDomain r D)) := rfl
    _ = Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) :=
        finrank_eq_of_bijective_algebraMap hkKb

end LowerSemicontinuity

end PlaceReductionRiemannRoch

end AlgebraicCurve

/-! ## The two rows -/

theorem AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) :
    ∃ S : Finset E, (0 : E) ∉ S ∧
      ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
        (∀ k : K, algebraMap K E k ∈ A) →
        (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
        (∀ s ∈ S, A.valuation s = 1) →
        (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
          ∃ a : E, a ∈ A ∧
            P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
        Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) ≤
          Module.finrank E (riemannRochSpace D) :=
  AlgebraicCurve.PlaceReductionRiemannRoch.GenericUpperBound.main hfg hfgE hgen D

theorem AlgebraicCurve.Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) :
    Module.finrank E (riemannRochSpace D) ≤
      Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) :=
  AlgebraicCurve.PlaceReductionRiemannRoch.LowerSemicontinuity.main K F E FE hfg hfgE hgen D A r
    hKA hArat hr
