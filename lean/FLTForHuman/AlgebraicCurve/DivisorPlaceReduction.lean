/-
Divisor reduction and the valuation-subring section over a constant field extension.

Three rows of the "places over a constant field extension" calculus that SET-AF105C's
`RegularProlongationRetraction.lean` set up:

* `AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction` — under a retraction of the
  regular-prolongation map, the order at the image of a place equals the order of the pushed-forward
  divisor: `mapDomain` commutes with `placeReduction`, so the reduction of a divisor can be read place
  by place;
* `RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed` —
  the prolongation whose `integers` are a prescribed valuation subring, obtained from the adjoin
  criterion plus a finrank bookkeeping (`sum_finrank_eq`);
* `exists_valuationSubring_section_of_constantField_valuationSubring` — a **section** of the
  restriction map on valuation subrings over a constant field extension, i.e. every valuation of the
  constant field extends to one of the function field compatibly.

The engine is the place/divisor calculus (`AlgebraicCurve/{Defs/Place,Defs/PushPull,ConstantReduction}.lean`),
the constant-field-extension dictionary (`IsCurveOver/ConstantFieldExtension{,Span}.lean`,
`Genus/ConstantFieldExtension.lean`, `Differential/ConstantFieldExtension.lean`), the Deuring
norm/residue dictionary (`DeuringNormResidue.lean`), and the regular-prolongation construction
(`RegularProlongation.lean`, `RegularProlongationFinrank.lean` and SET-AF105C's
`RegularProlongationRetraction.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring.lean>

## Manager's decisions at review (SET-AF106C)

* **the local `have hformula` stays for now; the promotion it points at is registered.**  The
  hypothesis-free norm formula is the `private` `Divisor.pushforwardNormFormula_of_finiteDimensional`,
  so it is not importable and the public `Divisor.pushforwardNormFormula` is a different statement.  The
  cure is a one-word promotion in that module (`Transcendence.lean`, a hub, so its dependents
  re-elaborate) — recorded in CARRY-FORWARD and as **MD-008** in `spec/METADATA-ISSUES.md`, since a
  wired node whose declaration is `private` reads as ported while being unimportable.  Nothing in this
  module changes when it lands except the deletion of the eleven-line `have`.
* **`GST.Rebase` stays at the pin's namespace.**  It is the pin's own namespace (one pin file, four
  declarations: the transport of `adjoin`/`finrank` along an algebra equivalence), not a pipeline label
  — no digits, no `kw_` prefix — so the naming policy keeps it, as it keeps `CasCore` in the archimedean
  column.  Renaming it to a longer subject namespace is a cosmetic move for a refactor round, and the
  checker is indifferent either way (last-name matching and statement hashes are namespace-blind).

spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction.lean
spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring.lean

PORT NOTES (SET-AF106C, order C).

* **30 pin declarations, 26 declared, 4 substituted** (engine diff: 26 by hash, 0 by name only,
  0 unaccounted). The four, all already public in the port, are *imported* rather than re-proved
  (`port_advise` tier 1/2, read one name at a time — FR-0311):
  `algebraMap_polynomial_map` and `isUnit_iff_inv_mem` are **byte-identical** in
  `AlgebraicCurve/DeuringNormResidue.lean` and are used qualified there; `valuation_algebraMap_eq_one`
  is there too, in its `ValuationSubring` form (`A.valuation (algebraMap K E k)`), and is applied at
  `P.toValuationSubring` in `not_exists_lt_one_iff`; `transcendental_of_linearIndependent_pow` is
  `AlgebraicCurve.transcendental_of_linearIndependent_pow` (`Genus/Stichtenoth.lean`), same name and
  shape.
* **Names.** The pin's generated label (`P2MW.S_…`) comes off; its two content namespaces stay, so the
  629-row's 19 helper declarations live in `AlgebraicCurve.DeuringPrincipalDivisorReduction` (the
  subject namespace, as `AlgebraicCurve.DeuringNormResidue` does for its own pin) and the 196-row's four
  helpers in `GST.Rebase` at the pin's spelling. The three headline theorems keep the published names.
* **A `private` dependency, transcribed, not imported.** `sum_restrict_eq_ord_norm` needs the
  hypothesis-free norm formula, which the port holds only as the **`private`**
  `Divisor.pushforwardNormFormula_of_finiteDimensional` (`AlgebraicCurve/PrincipalDivisors/Transcendence.lean:359`)
  — a private declaration is not importable, so the pin's row is transcribed and that 12-line proof is
  carried as a local `have hformula : Divisor.PushforwardNormFormula k (RatFunc k) L` (the public
  `Divisor.pushforwardNormFormula` would need `[HasPrincipalDivisors k L]` and
  `[Algebra.IsSeparable (RatFunc k) L]`, neither of which this row's hypotheses supply).
* **Imports added** (the scaffold's list is a starting point): `P1/Dictionary` (`placeOfPoint`,
  `isRational_of_isAlgClosed`), `P1/PlaceInftyReduction` (the reduction degree formula),
  `Place/Approximation` (`Place.exists_forall_ord_eq`), `PrincipalDivisors/Transcendence`
  (`Place.ord_norm_eq_sum_fiberOver`, `Place.mem_fiberOver`), `IsCurveOver/EssFiniteType`.
* **Textual, not statement-level, deviations from the pin** (the checker's `nhash` still reads every
  declaration `ok`): the pin's tactic-mode `haveI`/`letI` are `have`/`let` (Lean 4 registers local
  instances for both; `linter.style.haveILetI` otherwise fires — 21 sites, cap never raised); the
  v4.33→v4.34 renames `if_pos`/`if_neg`/`dif_pos` → `ite_eq_left`/`ite_eq_right`/`dite_eq_left`,
  `AlgEquiv.coe_algHom` → `AlgEquiv.coe_toAlgHom`, and the now-explicit `K` of
  `IsAlgClosed.degree_eq_one_of_irreducible K _` and `minpoly.mem_range_of_degree_eq_one K x _`. The
  pin's `attribute [-instance]` / `attribute [-simp]` walls are not transcribed.
* **Heartbeat probe pair (recorded, never installed).** Edit loop at `-DmaxHeartbeats=200000`: silent.
  Downward probe: **20000 passes; 10000 fails** at `finiteDimensional_adjoin_of_transcendental'`
  (this file, l.200) and `core` (l.438) — so every declaration of the module fits in 20 k, an order of
  magnitude under the 200 k edit-loop cap. No `set_option maxHeartbeats` /
  `synthInstance.maxHeartbeats` anywhere.
* **`dedup --within`: 1 cluster, 19 lines** — `faithful_polyAlg` / `ratAlg_tower` / `ratAlg_X` share the
  pin's own three-line `letI := polyAlg …; haveI := faithful_polyAlg …; letI := ratAlg …` prelude
  (a shape match on `bv0 : F | bv1 : Transcendental K bv0`). It is the pin's shape, transcribed
  verbatim; folding it would need an extra helper the pin does not have. `move_dead --dry-run`: 0
  declarations, 0 lines.
* **`private` policy**: the pin's 30 declarations are **all public** (0 private in either the pin or the
  module), so there is no `private`-dropping measurement to report for this order.
-/
import FLTForHuman.AlgebraicCurve.ConstantReduction
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.DeuringNormResidue
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Differential.RegularDiffs
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.P1.Dictionary
import FLTForHuman.AlgebraicCurve.P1.PlaceInftyReduction
import FLTForHuman.AlgebraicCurve.Place.Approximation
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.RegularProlongation
import FLTForHuman.AlgebraicCurve.RegularProlongationFinrank
import FLTForHuman.AlgebraicCurve.RegularProlongationRetraction

noncomputable section

open AlgebraicCurve

/-! ### The Deuring principal-divisor reduction engine (the 629-row's engine)

Transcribed from the pin's `DeuringPrincipalDivisorReduction` namespace. Four of the pin's 23
engine declarations are **substituted**, not transcribed:

* `algebraMap_polynomial_map` and `isUnit_iff_inv_mem` — byte-identical in
  `AlgebraicCurve/DeuringNormResidue.lean`, imported and used qualified;
* `valuation_algebraMap_eq_one` — there in its `ValuationSubring` form
  (`A.valuation (algebraMap K E k)`), applied here at `P.toValuationSubring`;
* `transcendental_of_linearIndependent_pow` — `AlgebraicCurve/Genus/Stichtenoth.lean`, same name.

The pin's `attribute [-instance]` / `attribute [-simp]` walls are not transcribed.
-/

open scoped Polynomial

namespace AlgebraicCurve
namespace DeuringPrincipalDivisorReduction

open AlgebraicCurve.RationalFunctionField

section RatAlg

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[reducible] noncomputable def polyAlg (x : F) : Algebra K[X] F :=
  (Polynomial.aeval x).toRingHom.toAlgebra

theorem faithful_polyAlg {x : F} (hx : Transcendental K x) :
    letI := polyAlg (K := K) x
    FaithfulSMul K[X] F := by
  let := polyAlg (K := K) x
  exact (faithfulSMul_iff_algebraMap_injective K[X] F).mpr (transcendental_iff_injective.mp hx)

open scoped RatFunc in

@[reducible] noncomputable def ratAlg {x : F} (hx : Transcendental K x) : Algebra (RatFunc K) F :=
  letI := polyAlg (K := K) x
  haveI := faithful_polyAlg (K := K) hx
  inferInstance

theorem ratAlg_tower {x : F} (hx : Transcendental K x) :
    letI := ratAlg (K := K) hx
    IsScalarTower K (RatFunc K) F := by
  let := polyAlg (K := K) x
  have := faithful_polyAlg (K := K) hx
  let := ratAlg (K := K) hx
  have : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq fun k => by
    show _ = (Polynomial.aeval x).toRingHom (algebraMap K K[X] k)
    simp
  infer_instance

theorem ratAlg_X {x : F} (hx : Transcendental K x) :
    letI := ratAlg (K := K) hx
    algebraMap (RatFunc K) F RatFunc.X = x := by
  let := polyAlg (K := K) x
  have := faithful_polyAlg (K := K) hx
  let := ratAlg (K := K) hx
  have h1 : algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) Polynomial.X) =
      algebraMap K[X] F Polynomial.X :=
    (IsScalarTower.algebraMap_apply K[X] (RatFunc K) F _).symm
  rw [RatFunc.algebraMap_X] at h1
  rw [h1]
  show (Polynomial.aeval x).toRingHom Polynomial.X = x
  simp

open IntermediateField in
theorem ratAlg_finite {x : F} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    letI := ratAlg (K := K) hx
    FiniteDimensional (RatFunc K) F := by
  let := ratAlg (K := K) hx
  have := ratAlg_tower (K := K) hx
  set ψ : RatFunc K →ₐ[K] F := IsScalarTower.toAlgHom K (RatFunc K) F with hψ
  have hψX : ψ RatFunc.X = x := ratAlg_X hx
  have hrange : ψ.fieldRange = IntermediateField.adjoin K ({x} : Set F) := by
    rw [AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X, IntermediateField.adjoin_map]
    simp [hψX]
  have : FiniteDimensional ψ.fieldRange F := by rw [hrange]; exact hfin
  have hinj : Function.Injective ψ.toRingHom.rangeRestrictField :=
    RingHom.injective _
  have hsurj : Function.Surjective ψ.toRingHom.rangeRestrictField := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := (AlgHom.mem_fieldRange).mp hy
    exact ⟨a, rfl⟩
  let e : RatFunc K ≃+* ψ.fieldRange := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl F) (RingHom.ext fun a => ?_)
  obtain ⟨b, rfl⟩ := e.surjective a
  simp only [RingHom.comp_apply]
  erw [RingEquiv.symm_apply_apply]
  rfl

open IntermediateField in
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin in

theorem finiteDimensional_adjoin_of_transcendental'
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional K⟮x⟯ F)
    {x : F} (hx : Transcendental K x) : FiniteDimensional K⟮x⟯ F := by
  obtain ⟨x₀, hx₀, hfin₀⟩ := hfg
  have := hfin₀
  have : Algebra.EssFiniteType K F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx₀ hfin₀
  have halg₀ : Algebra.IsAlgebraic (Algebra.adjoin K ({x₀} : Set F)) F :=
    Algebra.IsAlgebraic.trans (R := Algebra.adjoin K ({x₀} : Set F)) (S := K⟮x₀⟯) (A := F)
  have htr : Algebra.trdeg K F ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := K) (s := ({x₀} : Set F)) (A := F)
    simpa using h
  have hind : AlgebraicIndependent K (fun _ : Fin 1 => x) := by
    rw [algebraicIndependent_unique_type_iff]; exact hx
  have hbasis : IsTranscendenceBasis K (fun _ : Fin 1 => x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite ?_
    simpa using htr
  have halg : Algebra.IsAlgebraic (adjoin K (Set.range fun _ : Fin 1 => x)) F :=
    hbasis.isAlgebraic_field
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := by
    ext y; simp [eq_comm]
  rw [hrange] at halg
  have := halg
  have : Algebra.EssFiniteType K⟮x⟯ F := Algebra.EssFiniteType.of_comp K K⟮x⟯ F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic (F := K⟮x⟯) (E := F)

end RatAlg

section RatFuncPlaces

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem X_not_mem_placeInfty [DecidableEq (RatFunc k)] :
    (RatFunc.X : RatFunc k) ∉ (placeInfty k).toValuationSubring := by
  intro h
  have h1 := (Place.mem_iff_ord_nonneg (placeInfty k) (RatFunc.X_ne_zero (K := k))).mp h
  rw [ord_placeInfty_X] at h1
  norm_num at h1

theorem X_mem_placeOfPoint (a : k) :
    (RatFunc.X : RatFunc k) ∈ (placeOfPoint k a).toValuationSubring := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum, ← RatFunc.algebraMap_X]
  exact algebraMap_mem_ofHeightOneSpectrum k _ _

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [Algebra.IsIntegral (RatFunc k) L]

theorem restrict_eq_placeInfty_iff [IsAlgClosed k] [DecidableEq (RatFunc k)] (w : Place k L) :
    w.restrict (RatFunc k) = placeInfty k ↔
      algebraMap (RatFunc k) L RatFunc.X ∉ w.toValuationSubring := by
  constructor
  · intro h hX
    have : (RatFunc.X : RatFunc k) ∈ (w.restrict (RatFunc k)).toValuationSubring :=
      (Place.mem_restrict_iff w).mpr hX
    rw [h] at this
    exact X_not_mem_placeInfty this
  · intro hX
    rcases eq_placeOfPoint_or_eq_placeInfty k (w.restrict (RatFunc k)) with ⟨a, ha⟩ | h
    · exact absurd ((Place.mem_restrict_iff w).mp (ha ▸ X_mem_placeOfPoint a)) hX
    · exact h

theorem valuation_X_sub_lt_one_of_restrict_eq_placeOfPoint (w : Place k L) (β : k)
    (h : w.restrict (RatFunc k) = placeOfPoint k β) :
    w.toValuationSubring.valuation (algebraMap (RatFunc k) L RatFunc.X - algebraMap k L β) < 1 := by

  set y : RatFunc k := algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C β) with hy
  have hy0 : (Polynomial.X - Polynomial.C β : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero β
  have hyne : y ≠ 0 := by
    rw [hy]; exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hy0
  have hord : (placeOfPoint k β).ord y = 1 := by
    rw [hy, ord_placeOfPoint_algebraMap β hy0, Polynomial.rootMultiplicity_X_sub_C_self]
    rfl
  have hymem : y ∈ (placeOfPoint k β).toValuationSubring :=
    (Place.mem_iff_ord_nonneg _ hyne).mpr (by omega)
  have hyinv : y⁻¹ ∉ (placeOfPoint k β).toValuationSubring := by
    intro hmem
    have := (Place.mem_iff_ord_nonneg _ (inv_ne_zero hyne)).mp hmem
    rw [Place.ord_inv, hord] at this
    norm_num at this

  have hwmem : algebraMap (RatFunc k) L y ∈ w.toValuationSubring :=
    (Place.mem_restrict_iff w).mp (h ▸ hymem)
  have hwinv : (algebraMap (RatFunc k) L y)⁻¹ ∉ w.toValuationSubring := by
    intro hmem
    rw [← map_inv₀] at hmem
    exact hyinv (h ▸ (Place.mem_restrict_iff w).mpr hmem)
  have himg : algebraMap (RatFunc k) L y = algebraMap (RatFunc k) L RatFunc.X - algebraMap k L β := by
    rw [hy, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply]
  rw [← himg]
  have hnu : ¬ IsUnit (⟨algebraMap (RatFunc k) L y, hwmem⟩ : w.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply hwinv
    have h1 := congrArg (fun z : w.toValuationSubring => (z : L)) u.mul_inv
    simp only [Subring.coe_one, hu] at h1
    push_cast at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  have := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  exact (ValuationSubring.valuation_lt_one_iff _ _).mp this

end RatFuncPlaces

section FibreE

variable {E FE : Type*} [Field E] [Field FE] [Algebra E FE]
  [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE] [Algebra.IsIntegral (RatFunc E) FE]

theorem not_exists_lt_one_iff [IsAlgClosed E] [DecidableEq (RatFunc E)]
    (A : ValuationSubring E) (P : Place E FE) :
    (¬ ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE a) < 1) ↔
      (P.restrict (RatFunc E) = placeInfty E ∨
        ∃ β : E, β ∉ A ∧ P.restrict (RatFunc E) = placeOfPoint E β) := by
  rcases eq_placeOfPoint_or_eq_placeInfty E (P.restrict (RatFunc E)) with ⟨β, hβ⟩ | hinf
  ·
    have hlt := valuation_X_sub_lt_one_of_restrict_eq_placeOfPoint P β hβ
    have hR : (P.restrict (RatFunc E) = placeInfty E ∨
        ∃ β' : E, β' ∉ A ∧ P.restrict (RatFunc E) = placeOfPoint E β') ↔ β ∉ A := by
      constructor
      · rintro (h | ⟨β', hβ'A, h'⟩)
        · exact absurd (hβ.symm.trans h) (placeOfPoint_ne_placeInfty E β)
        · rwa [placeOfPoint_injective E (hβ.symm.trans h')]
      · exact fun h => Or.inr ⟨β, h, hβ⟩
    rw [hR]
    constructor
    · intro hL hβA
      exact hL ⟨β, hβA, hlt⟩
    · rintro hβA ⟨a, haA, ha⟩
      have hne : β - a ≠ 0 := by
        intro h0
        rw [sub_eq_zero] at h0
        exact hβA (h0 ▸ haA)
      have h1 := AlgebraicCurve.DeuringNormResidue.valuation_algebraMap_eq_one
        P.toValuationSubring P.algebraMap_mem' hne
      have h2 : P.toValuationSubring.valuation (algebraMap E FE (β - a)) < 1 := by
        have : algebraMap E FE (β - a) =
            (algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE a) -
              (algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE β) := by
          rw [map_sub]; ring
        rw [this]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hlt)
      rw [h1] at h2
      exact lt_irrefl _ h2
  ·
    have hX := (restrict_eq_placeInfty_iff P).mp hinf
    constructor
    · exact fun _ => Or.inl hinf
    · rintro - ⟨a, -, ha⟩
      apply hX
      have hmem : algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE a ∈ P.toValuationSubring :=
        (ValuationSubring.valuation_le_one_iff _ _).mp ha.le
      have := add_mem hmem (P.algebraMap_mem' a)
      simpa using this

end FibreE

section PoleSum

open scoped Classical

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def poleSum (x : F) (D : Divisor K F) : ℤ :=
  D.sum fun w n => if x ∉ w.toValuationSubring then n else 0

theorem poleSum_eq_sum (x : F) (D : Divisor K F) :
    poleSum x D = ∑ w ∈ D.support, if x ∉ w.toValuationSubring then D w else 0 := rfl

theorem poleSum_sub (x : F) (D D' : Divisor K F) :
    poleSum x (D - D') = poleSum x D - poleSum x D' := by
  unfold poleSum
  exact Finsupp.sum_sub_index fun w b₁ b₂ => by split_ifs <;> simp

theorem poleSum_mapDomain {ι : Type*} (x : F) (r : ι → Place K F) (D : ι →₀ ℤ) :
    poleSum x (Finsupp.mapDomain r D) =
      ∑ i ∈ D.support, if x ∉ (r i).toValuationSubring then D i else 0 := by
  unfold poleSum
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  rfl

theorem sum_support_ite_eq (D : Divisor K F) (p : Place K F → Prop) [DecidablePred p]
    (U : Finset (Place K F)) (hU : D.support ⊆ U) :
    (∑ w ∈ D.support, if p w then D w else 0) = ∑ w ∈ U, if p w then D w else 0 := by
  refine Finset.sum_subset hU fun w _ hw => ?_
  rw [Finsupp.notMem_support_iff.mp hw]
  simp

end PoleSum

section Push

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [IsAlgClosed k] [CharZero k]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FiniteDimensional (RatFunc k) L]

theorem sum_restrict_eq_ord_norm [DecidableEq (Place k (RatFunc k))] {f : L} (hf : f ≠ 0)
    (D : Divisor k L) (hD : ∀ w, D w = w.ord f) (v : Place k (RatFunc k)) :
    (∑ w ∈ D.support, if w.restrict (RatFunc k) = v then D w else 0) =
      v.ord (Algebra.norm (RatFunc k) f) := by
  have hformula : Divisor.PushforwardNormFormula k (RatFunc k) L := by
    intro f hf D hD v
    classical
    rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiberOver v hf]
    calc
      ∑ w ∈ D.support,
          (if w.restrict (RatFunc k) = v then D w * (w.inertiaDeg (RatFunc k) : ℤ) else 0)
          = ∑ w ∈ D.support ∪ v.fiberOver L,
              (if w.restrict (RatFunc k) = v then D w * (w.inertiaDeg (RatFunc k) : ℤ) else 0) := by
            refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
            rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]
      _ = ∑ w ∈ v.fiberOver L,
              (if w.restrict (RatFunc k) = v then D w * (w.inertiaDeg (RatFunc k) : ℤ) else 0) := by
            refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
            rw [ite_eq_right fun h => hw ((Place.mem_fiberOver v).mpr h)]
      _ = ∑ w ∈ v.fiberOver L, (w.inertiaDeg (RatFunc k) : ℤ) * w.ord f := by
            refine Finset.sum_congr rfl fun w hw => ?_
            rw [ite_eq_left ((Place.mem_fiberOver v).mp hw), hD w, mul_comm]
  have H := hformula f hf D hD v
  rw [Divisor.pushforward_apply] at H
  rw [← H]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with h
  · rw [Place.inertiaDeg_eq_one_of_isRational w (Place.isRational_of_isAlgClosed w)
      (Place.isRational_of_isAlgClosed _)]
    simp
  · rfl

end Push

section Core

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    [FiniteDimensional (RatFunc K) F] [FiniteDimensional (RatFunc E) FE]

theorem core
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) (Dg : Divisor E FE) (hDg : ∀ P : Place E FE, Dg P = P.ord (g : FE))
    (Df : Divisor K F) (hDf : ∀ v, Df v = v.ord (ρ g)) :
    poleSum (algebraMap (RatFunc K) F RatFunc.X) (Finsupp.mapDomain r Dg) =
      poleSum (algebraMap (RatFunc K) F RatFunc.X) Df := by
  classical
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hg0 : (g : FE) ≠ 0 := by
    intro h0
    apply hg
    have : g = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hNf0 : Algebra.norm (RatFunc K) (ρ g) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg

  have hR : poleSum (algebraMap (RatFunc K) F RatFunc.X) Df =
      (placeInfty K).ord (Algebra.norm (RatFunc K) (ρ g)) := by
    rw [poleSum_eq_sum, ← sum_restrict_eq_ord_norm hg Df hDf (placeInfty K)]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [(restrict_eq_placeInfty_iff w).symm]

  set B : Place E FE → Prop := fun P => ∃ β : E, β ∉ A ∧ P.restrict (RatFunc E) = placeOfPoint E β
    with hB_def
  have hL1 : poleSum (algebraMap (RatFunc K) F RatFunc.X) (Finsupp.mapDomain r Dg) =
      (∑ P ∈ Dg.support, if P.restrict (RatFunc E) = placeInfty E then Dg P else 0) +
        ∑ P ∈ Dg.support, if B P then Dg P else 0 := by
    rw [poleSum_mapDomain, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hfib : algebraMap (RatFunc K) F RatFunc.X ∉ (r P).toValuationSubring ↔
        (P.restrict (RatFunc E) = placeInfty E ∨ B P) := by
      rw [hr P, ← not_exists_lt_one_iff A P, hX]
    have hexcl : ¬ (P.restrict (RatFunc E) = placeInfty E ∧ B P) := by
      rintro ⟨h1, β, -, h2⟩
      exact placeOfPoint_ne_placeInfty E β (h2.symm.trans h1)
    by_cases h1 : P.restrict (RatFunc E) = placeInfty E
    · have h2 : ¬ B P := fun h2 => hexcl ⟨h1, h2⟩
      rw [ite_eq_left (hfib.mpr (Or.inl h1)), ite_eq_left h1, ite_eq_right h2, add_zero]
    · by_cases h2 : B P
      · rw [ite_eq_left (hfib.mpr (Or.inr h2)), ite_eq_right h1, ite_eq_left h2, zero_add]
      · rw [ite_eq_right h1, ite_eq_right h2, add_zero, ite_eq_right]
        rw [hfib]; rintro (h | h) <;> contradiction

  have hS1 : (∑ P ∈ Dg.support, if P.restrict (RatFunc E) = placeInfty E then Dg P else 0) =
      (placeInfty E).ord (Algebra.norm (RatFunc E) (g : FE)) :=
    sum_restrict_eq_ord_norm hg0 Dg hDg (placeInfty E)

  let ptOf : Place E FE → E := fun P =>
    if h : ∃ β : E, P.restrict (RatFunc E) = placeOfPoint E β then h.choose else 0
  have ptOf_eq : ∀ (P : Place E FE) (β : E), P.restrict (RatFunc E) = placeOfPoint E β → ptOf P = β := by
    intro P β h
    have hex : ∃ β : E, P.restrict (RatFunc E) = placeOfPoint E β := ⟨β, h⟩
    have h1 : ptOf P = hex.choose := dite_eq_left hex
    rw [h1]
    exact placeOfPoint_injective E (hex.choose_spec.symm.trans h)
  set s : Finset (Place E FE) := Dg.support.filter B with hs_def
  set S : Finset E := s.image ptOf with hS_def
  have hSA : ∀ β ∈ S, β ∉ A := by
    intro β hβ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨β', hβ'A, hP'⟩ := (Finset.mem_filter.mp hP).2
    rwa [ptOf_eq P β' hP']
  have hfibre : ∀ β : E, (∑ P ∈ Dg.support, if P.restrict (RatFunc E) = placeOfPoint E β then Dg P else 0)
      = (placeOfPoint E β).ord (Algebra.norm (RatFunc E) (g : FE)) := fun β =>
    sum_restrict_eq_ord_norm hg0 Dg hDg (placeOfPoint E β)
  have hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (Algebra.norm (RatFunc E) (g : FE)) ≠ 0 → β ∈ S := by
    intro β hβA hne
    rw [← hfibre β] at hne
    obtain ⟨P, hP, hP'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hPβ : P.restrict (RatFunc E) = placeOfPoint E β := by
      by_contra h; rw [ite_eq_right h] at hP'; exact hP' rfl
    have hPs : P ∈ s := Finset.mem_filter.mpr ⟨hP, β, hβA, hPβ⟩
    exact Finset.mem_image.mpr ⟨P, hPs, ptOf_eq P β hPβ⟩
  have hS2 : (∑ P ∈ Dg.support, if B P then Dg P else 0) =
      ∑ β ∈ S, (placeOfPoint E β).ord (Algebra.norm (RatFunc E) (g : FE)) := by
    rw [hS_def, Finset.sum_image' (fun P => Dg P), Finset.sum_filter]
    intro P₀ hP₀
    obtain ⟨β₀, hβ₀A, hP₀'⟩ := (Finset.mem_filter.mp hP₀).2
    rw [ptOf_eq P₀ β₀ hP₀', ← hfibre β₀, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hiff : P.restrict (RatFunc E) = placeOfPoint E β₀ ↔ (B P ∧ ptOf P = β₀) := by
      constructor
      · intro h; exact ⟨⟨β₀, hβ₀A, h⟩, ptOf_eq P β₀ h⟩
      · rintro ⟨⟨β, -, hβ⟩, h2⟩
        rw [hβ, ← h2, ptOf_eq P β hβ]
    by_cases h : P.restrict (RatFunc E) = placeOfPoint E β₀
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h).1, ite_eq_left (hiff.mp h).2]
    · by_cases hB : B P
      · rw [ite_eq_right h, ite_eq_left hB, ite_eq_right]
        exact fun h2 => h (hiff.mpr ⟨hB, h2⟩)
      · rw [ite_eq_right h, ite_eq_right hB]

  set O' : ValuationSubring (RatFunc E) := O.comap (algebraMap (RatFunc E) FE) with hO'_def
  set ρ' : O' →+* F := ρ.comp ((algebraMap (RatFunc E) FE).restrict O'.toSubring O.toSubring
    fun z hz => (ValuationSubring.mem_comap.mp hz)) with hρ'_def
  have hO' : ∀ c : E, algebraMap E (RatFunc E) c ∈ O' ↔ c ∈ A := by
    intro c
    rw [hO'_def, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply, hO]
  have hker' : RingHom.ker ρ' = IsLocalRing.maximalIdeal O' := by
    ext z
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hzO : algebraMap (RatFunc E) FE z ∈ O := ValuationSubring.mem_comap.mp z.2
    have h1 : ρ' z = ρ ⟨algebraMap (RatFunc E) FE z, hzO⟩ := rfl
    rw [h1, ← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rcases eq_or_ne (z : RatFunc E) 0 with hz | hz
    · have hz' : z = 0 := Subtype.ext hz
      have h0 : (⟨algebraMap (RatFunc E) FE z, hzO⟩ : O) = 0 := Subtype.ext (by simp [hz])
      rw [h0, hz']
      simp
    · have hz1 : (algebraMap (RatFunc E) FE z) ≠ 0 := (map_ne_zero _).mpr hz
      rw [AlgebraicCurve.DeuringNormResidue.isUnit_iff_inv_mem O ⟨_, hzO⟩ hz1,
        AlgebraicCurve.DeuringNormResidue.isUnit_iff_inv_mem O' z hz]
      simp only [hO'_def, ValuationSubring.mem_comap, map_inv₀]
  have hρ' : ∀ p : K[X],
      ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O',
        ρ' ⟨_, h⟩ = algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p) := by
    intro p
    have key := AlgebraicCurve.DeuringNormResidue.algebraMap_polynomial_map hX p
    obtain ⟨h, hh⟩ := hρ (algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p))
    have h' : algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) (p.map (algebraMap K E))) ∈ O := by
      rw [key]; exact h
    refine ⟨ValuationSubring.mem_comap.mpr h', ?_⟩
    calc ρ' ⟨_, ValuationSubring.mem_comap.mpr h'⟩
        = ρ ⟨algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) (p.map (algebraMap K E))), h'⟩ := rfl
      _ = ρ ⟨_, h⟩ := by congr 1; exact Subtype.ext key
      _ = _ := hh

  obtain ⟨hNgO, hρNg⟩ := AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction K F E FE hfg hfgE
    hgen hX A hKA hArat O ρ hO hker hρ g hg
  have hGmem : Algebra.norm (RatFunc E) (g : FE) ∈ O' := ValuationSubring.mem_comap.mpr hNgO
  have hGN : ρ' ⟨Algebra.norm (RatFunc E) (g : FE), hGmem⟩ =
      algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g)) := hρNg
  have hXchild := AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
    K E F A hKA hArat O' ρ' hO' hker' hρ'
    ⟨Algebra.norm (RatFunc E) (g : FE), hGmem⟩ (Algebra.norm (RatFunc K) (ρ g)) hNf0 hGN S hSA hS

  rw [hR, hL1, hS1, hS2, hXchild]

end Core

end DeuringPrincipalDivisorReduction
end AlgebraicCurve

open DeuringPrincipalDivisorReduction in
theorem AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) (Dg : Divisor E FE) (hDg : ∀ P : Place E FE, Dg P = P.ord (g : FE))
    (v : Place K F) :
    Finsupp.mapDomain r Dg v = v.ord (ρ g) := by
  classical
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) (ρ g) hg
  rw [← hDf v]
  by_contra hne
  set Λ : Divisor K F := Finsupp.mapDomain r Dg - Df with hΛ_def
  have hΛv : Λ v ≠ 0 := by
    rw [hΛ_def, Finsupp.sub_apply]
    exact sub_ne_zero.mpr hne
  have hv : v ∈ Λ.support := Finsupp.mem_support_iff.mpr hΛv

  obtain ⟨x, hx0, hxord⟩ :=
    Place.exists_forall_ord_eq Λ.support (fun w => if w = v then (-1 : ℤ) else 0)
  have hxv : v.ord x = -1 := by simpa using hxord v hv
  have hx : Transcendental K x := by
    intro halg
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral))
    have h0 := Place.ord_algebraMap v c
    rw [hc, hxv] at h0
    norm_num at h0
  have hpole : poleSum x Λ = Λ v := by
    rw [poleSum_eq_sum]
    have hcongr : ∀ w ∈ Λ.support,
        (if x ∉ w.toValuationSubring then Λ w else 0) = if w = v then Λ w else 0 := by
      intro w hw
      have hordw := hxord w hw
      by_cases hwv : w = v
      · rw [ite_eq_left hwv] at hordw
        rw [ite_eq_left hwv, ite_eq_left]
        rw [Place.mem_iff_ord_nonneg _ hx0, hordw]
        norm_num
      · rw [ite_eq_right hwv] at hordw
        rw [ite_eq_right hwv, ite_eq_right]
        rw [not_not, Place.mem_iff_ord_nonneg _ hx0, hordw]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq', ite_eq_left hv]

  let iK := DeuringPrincipalDivisorReduction.ratAlg (K := K) hx
  have := DeuringPrincipalDivisorReduction.ratAlg_tower (K := K) hx
  have := DeuringPrincipalDivisorReduction.ratAlg_finite (K := K) hx
    (DeuringPrincipalDivisorReduction.finiteDimensional_adjoin_of_transcendental' hfg hx)
  have hx' : Transcendental E (algebraMap F FE x) := by
    apply AlgebraicCurve.transcendental_of_linearIndependent_pow
    have h := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen
      (AlgebraicCurve.linearIndependent_pow_of_transcendental hx)
    simpa only [map_pow] using h
  let iE := DeuringPrincipalDivisorReduction.ratAlg (K := E) hx'
  have := DeuringPrincipalDivisorReduction.ratAlg_tower (K := E) hx'
  have := DeuringPrincipalDivisorReduction.ratAlg_finite (K := E) hx'
    (DeuringPrincipalDivisorReduction.finiteDimensional_adjoin_of_transcendental' hfgE hx')
  have hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X) := by
    rw [DeuringPrincipalDivisorReduction.ratAlg_X hx, DeuringPrincipalDivisorReduction.ratAlg_X hx']
  have hcore := DeuringPrincipalDivisorReduction.core hfg hfgE hgen hX A r hKA hArat hr O ρ hO hker hρ
    g hg Dg hDg Df hDf
  rw [DeuringPrincipalDivisorReduction.ratAlg_X hx] at hcore
  have h0 : poleSum x Λ = 0 := by rw [hΛ_def, poleSum_sub, hcore, sub_self]
  exact hΛv (hpole.symm.trans h0)

open AlgebraicCurve IsLocalRing

/-! ### The rebase engine of the 196-row

The pin's `GST.Rebase` helpers: transport of `adjoin`/`finrank` along an algebra equivalence, and
the residue-field equivalence attached to two regular prolongations with the same `integers`. -/

namespace GST
namespace Rebase

section Transport

variable {k : Type*} [Field k] {B₁ : Type*} {B₂ : Type*} [Field B₁] [Field B₂]
  [Algebra k B₁] [Algebra k B₂]

theorem mem_adjoin_simple_of_algEquiv (e : B₁ ≃ₐ[k] B₂) (x : B₁) {y : B₁}
    (hy : y ∈ IntermediateField.adjoin k ({x} : Set B₁)) :
    e y ∈ IntermediateField.adjoin k ({e x} : Set B₂) := by
  have h : (IntermediateField.adjoin k ({x} : Set B₁)).map (e : B₁ →ₐ[k] B₂) =
      IntermediateField.adjoin k ({e x} : Set B₂) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, AlgEquiv.coe_toAlgHom]
  rw [← h, IntermediateField.mem_map]
  exact ⟨y, hy, rfl⟩

theorem finrank_adjoin_simple_eq_of_algEquiv (e : B₁ ≃ₐ[k] B₂) (x : B₁) :
    Module.finrank (IntermediateField.adjoin k ({x} : Set B₁)) B₁ =
      Module.finrank (IntermediateField.adjoin k ({e x} : Set B₂)) B₂ := by
  have hfwd : ∀ y ∈ IntermediateField.adjoin k ({x} : Set B₁),
      e y ∈ IntermediateField.adjoin k ({e x} : Set B₂) :=
    fun y hy => mem_adjoin_simple_of_algEquiv e x hy
  have hbwd : ∀ z ∈ IntermediateField.adjoin k ({e x} : Set B₂),
      e.symm z ∈ IntermediateField.adjoin k ({x} : Set B₁) := by
    intro z hz
    have h := mem_adjoin_simple_of_algEquiv e.symm (e x) hz
    rwa [e.symm_apply_apply] at h
  let i : IntermediateField.adjoin k ({x} : Set B₁) ≃+* IntermediateField.adjoin k ({e x} : Set B₂) :=
    { toFun := fun y => ⟨e y, hfwd y.1 y.2⟩
      invFun := fun z => ⟨e.symm z, hbwd z.1 z.2⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply (y : B₁))
      right_inv := fun z => Subtype.ext (e.apply_symm_apply (z : B₂))
      map_mul' := fun a b => Subtype.ext (map_mul e (a : B₁) (b : B₁))
      map_add' := fun a b => Subtype.ext (map_add e (a : B₁) (b : B₁)) }
  exact Algebra.finrank_eq_of_equiv_equiv i e.toRingEquiv (RingHom.ext fun y => rfl)

end Transport

section Iso

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  {Fb₁ : Type*} {Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (ResidueField A) Fb₁] [Algebra (ResidueField A) Fb₂]

theorem exists_algEquiv_forall_apply_eq (O₁ O₂ : ValuationSubring F) (h : O₁ = O₂)
    (hO₁ : ∀ x : L, algebraMap L F x ∈ O₁ ↔ x ∈ A)
    (hO₂ : ∀ x : L, algebraMap L F x ∈ O₂ ↔ x ∈ A)
    (ρ₁ : O₁ →+* Fb₁) (ρ₂ : O₂ →+* Fb₂)
    (hs₁ : Function.Surjective ρ₁) (hs₂ : Function.Surjective ρ₂)
    (hk₁ : RingHom.ker ρ₁ = maximalIdeal O₁) (hk₂ : RingHom.ker ρ₂ = maximalIdeal O₂)
    (hc₁ : ∀ a : A, ρ₁ ⟨algebraMap L F a, (hO₁ a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fb₁ (residue A a))
    (hc₂ : ∀ a : A, ρ₂ ⟨algebraMap L F a, (hO₂ a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fb₂ (residue A a)) :
    ∃ e : Fb₁ ≃ₐ[ResidueField A] Fb₂,
      ∀ (x : F) (h₁ : x ∈ O₁) (h₂ : x ∈ O₂), e (ρ₁ ⟨x, h₁⟩) = ρ₂ ⟨x, h₂⟩ := by
  subst h
  have hker : RingHom.ker ρ₁ = RingHom.ker ρ₂ := hk₁.trans hk₂.symm
  let e₀ : Fb₁ ≃+* Fb₂ :=
    (RingHom.quotientKerEquivOfSurjective hs₁).symm.trans
      ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hs₂))
  have he₀ : ∀ x : O₁, e₀ (ρ₁ x) = ρ₂ x := by
    intro x
    have h1 : RingHom.quotientKerEquivOfSurjective hs₁ (Ideal.Quotient.mk _ x) = ρ₁ x := rfl
    have h2 : RingHom.quotientKerEquivOfSurjective hs₂ (Ideal.Quotient.mk _ x) = ρ₂ x := rfl
    simp only [e₀, RingEquiv.trans_apply]
    rw [← h1, RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk, h2]
  have hke : ∀ c : ResidueField A, e₀ (algebraMap (ResidueField A) Fb₁ c) =
      algebraMap (ResidueField A) Fb₂ c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← hc₁, he₀, hc₂]
  exact ⟨AlgEquiv.ofRingEquiv (f := e₀) hke, fun x h₁ _ => he₀ ⟨x, h₁⟩⟩

end Iso

end Rebase
end GST

namespace GST
namespace Rebase

theorem exists_algEquiv_forall_residue_eq
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fb₁ : Type*} {Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (ResidueField A) Fb₁] [Algebra (ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (h : R₁.integers = R₂.integers) :
    ∃ e : Fb₁ ≃ₐ[ResidueField A] Fb₂,
      ∀ (x : F) (h₁ : x ∈ R₁.integers) (h₂ : x ∈ R₂.integers),
        e (R₁.residue ⟨x, h₁⟩) = R₂.residue ⟨x, h₂⟩ :=
  exists_algEquiv_forall_apply_eq A R₁.integers R₂.integers h R₁.algebraMap_mem_iff
    R₂.algebraMap_mem_iff R₁.residue R₂.residue R₁.residue_surjective R₂.residue_surjective
    R₁.ker_residue R₂.ker_residue R₁.residue_algebraMap R₂.residue_algebraMap

end Rebase
end GST

open GST.Rebase in
theorem AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i₀ : ι) (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ (R i₀).integers)) :
    ∃ j, V = (R j).integers := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  have : Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _

  have hreb : ∀ i, ∃ (_ : Algebra (ResidueField A) (ResidueField (R i).integers))
      (R' : RegularProlongation A F (ResidueField (R i).integers)),
      R'.integers = (R i).integers ∧ ∃ hf' : f ∈ R'.integers,
        Transcendental (ResidueField A) (R'.residue ⟨f, hf'⟩) := fun i =>
    RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic A (R i) f (hf i) (htr i)
      (R i).integers (fun _ _ => Iff.rfl)
  choose inst R' hR'int hf' htr' using hreb

  obtain ⟨instV, RV, hRVint, hfV, htrV⟩ :=
    RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic A (R i₀) f (hf i₀) (htr i₀)
      V hV

  let Fb'' : Option ι → Type _ :=
    fun | none => ResidueField V | some i => ResidueField (R i).integers
  let hFld'' : ∀ o, Field (Fb'' o) :=
    fun | none => (inferInstance : Field (ResidueField V))
        | some i => (inferInstance : Field (ResidueField (R i).integers))
  let hAlg'' : ∀ o, Algebra (ResidueField A) (Fb'' o) :=
    fun | none => instV | some i => inst i
  let R'' : ∀ o, RegularProlongation A F (Fb'' o) := fun | none => RV | some i => R' i
  have hR'' : Function.Injective fun o => (R'' o).integers := by
    intro o₁ o₂ h
    match o₁, o₂, h with
    | none, none, _ => rfl
    | none, some i, h => exact absurd (hRVint.symm.trans (h.trans (hR'int i))) (hne i)
    | some i, none, h => exact absurd (hRVint.symm.trans (h.symm.trans (hR'int i))) (hne i)
    | some i, some i', h =>
        exact congrArg some (hR ((hR'int i).symm.trans (h.trans (hR'int i'))))
  have hf'' : ∀ o, f ∈ (R'' o).integers := fun | none => hfV | some i => hf' i
  have htr'' : ∀ o, Transcendental (ResidueField A) ((R'' o).residue ⟨f, hf'' o⟩) :=
    fun | none => htrV | some i => htr' i

  obtain ⟨hFD, hle⟩ :=
    RegularProlongation.sum_finrank_adjoin_residue_le A Fb'' R'' hR'' f hf'' htr''
  rw [Fintype.sum_option] at hle

  have hterm : ∀ i, Module.finrank
        (IntermediateField.adjoin (ResidueField A)
          ({(R'' (some i)).residue ⟨f, hf'' (some i)⟩} : Set (Fb'' (some i)))) (Fb'' (some i))
      = Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
        (Fb i) := by
    intro i
    obtain ⟨e, he⟩ := exists_algEquiv_forall_residue_eq A (R i) (R' i) (hR'int i).symm
    have h := finrank_adjoin_simple_eq_of_algEquiv e ((R i).residue ⟨f, hf i⟩)
    rw [he f (hf i) (hf' i)] at h
    exact h.symm
  rw [show (∑ i, Module.finrank
        (IntermediateField.adjoin (ResidueField A)
          ({(R'' (some i)).residue ⟨f, hf'' (some i)⟩} : Set (Fb'' (some i)))) (Fb'' (some i)))
      = ∑ i, Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
        (Fb i) from Finset.sum_congr rfl fun i _ => hterm i, heq] at hle

  have hFDV : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A)
        ({(R'' none).residue ⟨f, hf'' none⟩} : Set (Fb'' none))) (Fb'' none) := hFD none
  have hpos : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A)
        ({(R'' none).residue ⟨f, hf'' none⟩} : Set (Fb'' none))) (Fb'' none) :=
    Module.finrank_pos
  omega

theorem AlgebraicCurve.exists_valuationSubring_section_of_constantField_valuationSubring
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (hker : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    ∃ (O : ValuationSubring F') (ρ : O →+* F),
      (∀ f : F, ∃ h : algebraMap F F' f ∈ O, ρ ⟨algebraMap F F' f, h⟩ = f) ∧
      RingHom.ker ρ = IsLocalRing.maximalIdeal O ∧
      (∀ f' : F', f' ≠ 0 → ∃ c : K', ∃ h : c • f' ∈ O, ρ ⟨c • f', h⟩ ≠ 0) ∧
      (∀ (c : K') (h : algebraMap K' F' c ∈ O),
        ρ ⟨algebraMap K' F' c, h⟩ ∈ Set.range (algebraMap K F)) := by
  obtain ⟨O, ρ, hmem_iff, hker_ρ, hresA, hreg, hret⟩ :=
    AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring
      K F K' F' hfg hfg' hgen A hK σ hker hsec
  refine ⟨O, ρ, hret, hker_ρ, hreg, ?_⟩
  intro c hc
  obtain ⟨h', hρ⟩ := hresA ⟨c, (hmem_iff c).mp hc⟩
  exact ⟨σ ⟨c, (hmem_iff c).mp hc⟩, hρ.symm⟩
