/-
`Pic0` under a constant field extension: the lifted correspondence is a coboundary.

`freeAlgebra_lift_correspondence_eq_zero_of_baseChange` is the `Pic0`-side form of the divisor
correspondence: for two integral extensions `φ, ψ : F →ₐ[K] F' i` and a correspondence whose divisor
is principal after the place reduction, the free-algebra lift of the correspondence vanishes in
`Pic0`. The proof is AF106C's `Divisor.mapDomain_placeReduction_eq_ord_of_retraction` plus
`Divisor.mapDomain_placeReduction_correspondence` (`ConstantReductionCorrespondence.lean`), read
through the retraction `exists_regularProlongation_retraction_of_constantField_valuationSubring`.

This is the fourth module of the `Pic0/` directory and the only one whose subject is *base change*
(`DivisorPairing`, `Torsion` and `WeilPairing` are the pairing and torsion stories). Its one premise
module of the `Pic0/` family is `ConstantReductionCorrespondence.lean`, which it imports; the module
is therefore above the correspondence and below nothing.

## The rows

* `AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_baseChange` — 532 pin `S_` lines.

## The declaration surface

The pin's `S_` file is a **surface of 24 declarations**: the headline (`solution`, pinned by the
`Theorems/` wrapper as the name above) plus a 23-declaration helper block in the pin's generated
namespace `AlgebraicCurve.BaseChangeDescentAux`. That generated label is dropped and the block moves
to the subject namespace `AlgebraicCurve.Pic0.BaseChange` (the module's own subject), so the block's
declarations keep the pin's last names, binder-for-binder statements and `public` visibility. The
engine diff against the pin is therefore total: 24 pin declarations, 24 module declarations, none
missing, none extra (`public`/`private` as in the pin — the pin has no `private` helper here).

The block splits by subject, not by accident:

* `lift_equivariant` — `FreeAlgebra.lift` commutes with an additive map intertwining the families of
  endomorphisms. This is the pin's only genuinely new engine; the port had no copy of it
  (`rg lift_equivariant FLTForHuman` was empty at the substitution pass).
* `degree_eq_sum`, `mk_eq_zero_iff`, `mkHom`, `mkHom_apply`, `degree_mapDomain` — the `Pic`-side
  bookkeeping the `Pic0` lift descends through. The port holds alpha-equivalent copies of
  `degree_eq_sum` (`AlgebraicCurve.W7XH.CFE.degree_eq_sum`) and of `mk_eq_zero_iff`
  (`AlgebraicCurve.Pic0.mk_eq_zero_iff`, `ModularCurve.XH.JHDescent.mk_eq_zero_iff`); they are
  **transcribed, not imported**, following the port's existing habit for these one-line `Pic0`
  bridges — a second copy is what keeps this module free of a `Genus/ConstantFieldExtension` or
  `WeilExchange/Transport` import, and the pin's own file duplicates them too.
* the valuation block (`valuation_algebraMap_eq_one` … `valuation_inv_sub_inv_lt_one`), the
  composite/reduced valuation subring `compositeRing`/`reducedRing` with its two structural lemmas,
  and `exists_placeReduction` — the existence of the place reduction as a *function of places*,
  proved from `Place.exists_of_valuationSubring` on the reduced subring. AF106C's
  `PlaceReductionCorrespondence.exists_reduction` is the pin's `exists_placeReduction` (same
  conclusion, same data, different route: it goes through
  `Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension`). The pin's `S_` file carries
  its own copy, and this port keeps it: the two disagree on the `IsCurveOver E FE` hypothesis and on
  the constant-field-extension inputs they take, so one is not the other.
* `exists_sub_algebraMap_mem_maximalIdeal`, `placeReduction_eq_of_comap_eq` — the two facts the
  headline needs about a place reduction *at a prescribed place* (`r` is computed from a comap), used
  to build the section `ℓ` of the reduction on `Divisor.degZero`.

No helper is `private`: the pin's block is public, and the set-level surface gate is the manager's.

## Linters

One linter is silenced, **point-wise** (never module-wide), on the two declarations that carry the pin's
instance walls: `exists_placeReduction` and `exists_sub_algebraMap_mem_maximalIdeal` are written
`set_option linter.style.haveILetI false in`. The `haveI`s in them (`haveI := hfin`, the
`FiniteDimensional` instance `Place.exists_of_valuationSubring` consumes, and
`haveI : Module.Finite E P.ResidueField`) are **instance bindings consumed by instance search**, so the
linter's suggested `have` does not elaborate: the name becomes a plain hypothesis and the very next
`exact` fails. The port's own treatment of the same pin device is identical
(`RegularProlongationRetraction.lean`'s `set_option linter.style.haveILetI false in` before its
retraction theorem; `ConstantReductionCorrespondence.lean`'s module-wide line). No other linter is
silenced, no `set_option maxHeartbeats` is installed, and `autoImplicit` is off.

## Gates (measured, pin `aa2d8b3`)

* `check_port --force`: **24 ok, 0 mismatch, 0 missing, 0 own, 0 kw** — every one of the 23 helpers
  matched by statement hash on the checker's first run, and the headline still matches the wrapper.
* engine diff (`tmp/af107/review.py`): pin sources 2, pin decls **25** (the `S_` file's 24 + the
  `Theorems/` wrapper's headline), module decls **24**; **24 by hash, 0 by name, 0 unaccounted** —
  nothing missing, nothing extra.
* edit loop `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000`: **silent**, 14 s.
* `lake build FLTForHuman.AlgebraicCurve.Pic0.BaseChange` under `flock`: **built (52 s)**, 0 warning
  lines from this file (the cascade's warnings belong to other modules).
* `#print axioms` on all 24 public declarations: every one is a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* `dedup.py --within`: 24 declarations, **0 duplicate clusters**. `move_dead.py --dry-run`:
  **0 declarations, 0 lines**.
* heartbeat probe pair (recorded, **not installed**): 200 k silent; **40 000 silent**; **20 000 fails**
  (`timeout at whnf` at the headline's `mapDomain_placeReduction_correspondence` call). The headline
  is the module's only declaration above 20 k and 40 k clears the whole module, so the 200 k edit-loop
  cap carries ≥ 5× headroom. Nothing is installed.
* set-level `tmp/af107/collision-probe.lean`: **silent** after this module's `.olean` landed.

## Substitutions

`port_advise` on this row: the only *measured* substitution is the headline itself (the scaffold's
statement, byte-identical). Two names read as "already in the port under a different statement"
(`degree_eq_sum`, `valuation_algebraMap_eq_one`) — both are alpha-equivalent copies elsewhere in the
port (`AlgebraicCurve.W7XH.CFE.degree_eq_sum`,
`AlgebraicCurve.RegularProlongation.PlaceMapOrd.valuation_algebraMap_eq_one`) and both are transcribed
here rather than imported — the pin's own `S_` file duplicates its neighbours in the same way. Nothing
is imported as a substitute, and nothing in the pin's 24 declarations is absent from the module.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_baseChange.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_baseChange.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_baseChange.lean
-/

import FLTForHuman.AlgebraicCurve.ConstantReductionCorrespondence
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.DivisorPlaceReduction
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.RegularProlongationRetraction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

open AlgebraicCurve

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace Pic0

/- The pin's `BaseChangeDescentAux` block: the `freeAlgebra`-lift descent and the place reduction
it descends through.  The pin's generated label is dropped for the module's subject namespace. -/
namespace BaseChange

open IsLocalRing

universe uK uF uE uFE

/-- `FreeAlgebra.lift` commutes with an additive map intertwining the two families of
endomorphisms. -/
theorem lift_equivariant {ι A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (T : ι → A →+ A) (S : ι → B →+ B) (h : ∀ i a, f (T i a) = S i (f a))
    (q : FreeAlgebra ℤ ι) (a : A) :
    f (FreeAlgebra.lift ℤ (fun i => (T i).toIntLinearMap) q a) =
      FreeAlgebra.lift ℤ (fun i => (S i).toIntLinearMap) q (f a) := by
  induction q using FreeAlgebra.induction generalizing a with
  | grade0 r => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_zsmul]
  | grade1 i => simp only [FreeAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap, h]
  | mul x y hx hy => simp only [map_mul, Module.End.mul_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

section Degree

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem degree_eq_sum [IsAlgClosed k] [IsCurveOver k L] (D : Divisor k L) :
    D.degree = D.sum fun _ n => n := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D hv hn ih =>
    rw [map_add, Divisor.degree_single, IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := k) v,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl, ih]
    simp

theorem mk_eq_zero_iff (D : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = 0 ↔ (D : Divisor k L).IsPrincipal := by
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

noncomputable def mkHom : Divisor.degZero (K := k) (F := L) →+ Pic0 k L :=
  QuotientAddGroup.mk' _

@[scoped simp] theorem mkHom_apply (D : Divisor.degZero (K := k) (F := L)) : mkHom D = Pic0.mk D := rfl

end Degree

theorem degree_mapDomain {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E]
    [Field FE] [Algebra E FE] [IsAlgClosed K] [IsCurveOver K F] [IsAlgClosed E] [IsCurveOver E FE]
    (r : Place E FE → Place K F) (D : Divisor E FE) :
    Divisor.degree (Finsupp.mapDomain r D) = D.degree := by
  rw [degree_eq_sum, degree_eq_sum, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

section Reduction

variable {E : Type uE} {FE : Type uFE} [Field E] [Field FE] [Algebra E FE]

theorem valuation_algebraMap_eq_one (P : Place E FE) {e : E} (he : e ≠ 0) :
    P.toValuationSubring.valuation (algebraMap E FE e) = 1 := by
  have hu : IsUnit (⟨algebraMap E FE e, P.algebraMap_mem' e⟩ : P.toValuationSubring) := by
    refine IsUnit.of_mul_eq_one ⟨algebraMap E FE e⁻¹, P.algebraMap_mem' e⁻¹⟩ ?_
    ext
    simp [he]
  exact (ValuationSubring.valuation_eq_one_iff _ _).1 hu

theorem valuation_algebraMap_le_one (P : Place E FE) (e : E) :
    P.toValuationSubring.valuation (algebraMap E FE e) ≤ 1 :=
  (P.toValuationSubring.valuation_le_one_iff _).2 (P.algebraMap_mem' e)

theorem algebraMap_eq_of_valuation_sub_lt_one (P : Place E FE) {a b : E}
    (h : P.toValuationSubring.valuation (algebraMap E FE a - algebraMap E FE b) < 1) : a = b := by
  by_contra hab
  rw [← map_sub, valuation_algebraMap_eq_one P (sub_ne_zero.2 hab)] at h
  exact lt_irrefl _ h

theorem const_unique (P : Place E FE) {g : FE} {a b : E}
    (ha : P.toValuationSubring.valuation (g - algebraMap E FE a) < 1)
    (hb : P.toValuationSubring.valuation (g - algebraMap E FE b) < 1) : a = b := by
  refine algebraMap_eq_of_valuation_sub_lt_one P ?_
  have : algebraMap E FE a - algebraMap E FE b = (g - algebraMap E FE b) - (g - algebraMap E FE a) := by
    ring
  rw [this]
  exact Valuation.map_sub_lt _ hb ha

theorem mem_of_valuation_sub_lt_one (P : Place E FE) {g : FE} {a : E}
    (h : P.toValuationSubring.valuation (g - algebraMap E FE a) < 1) :
    g ∈ P.toValuationSubring := by
  rw [← ValuationSubring.valuation_le_one_iff]
  have : g = (g - algebraMap E FE a) + algebraMap E FE a := by ring
  rw [this]
  exact Valuation.map_add_le _ h.le (valuation_algebraMap_le_one P a)

theorem exists_valuation_sub_lt_one [IsAlgClosed E] (P : Place E FE)
    [Module.Finite E P.ResidueField] {g : FE} (hg : g ∈ P.toValuationSubring) :
    ∃ e : E, P.toValuationSubring.valuation (g - algebraMap E FE e) < 1 := by
  have : Algebra.IsIntegral E P.ResidueField := Algebra.IsIntegral.of_finite E _
  obtain ⟨e, he⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := E)
    (K := P.ResidueField)).2 (residue _ ⟨g, hg⟩)
  refine ⟨e, ?_⟩
  have hmem : (⟨g, hg⟩ : P.toValuationSubring) - algebraMap E P.toValuationSubring e ∈
      maximalIdeal P.toValuationSubring := by
    rw [← Ideal.Quotient.eq]
    exact he.symm
  have := (ValuationSubring.valuation_lt_one_iff _ _).1 hmem
  simpa using this

theorem valuation_eq_one_of_sub_lt_one (P : Place E FE) {g : FE} {e : E} (he0 : e ≠ 0)
    (h : P.toValuationSubring.valuation (g - algebraMap E FE e) < 1) :
    P.toValuationSubring.valuation g = 1 := by
  have h1 := valuation_algebraMap_eq_one P he0
  have : g = algebraMap E FE e + (g - algebraMap E FE e) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [h1]), h1]

theorem valuation_inv_sub_inv_lt_one (P : Place E FE) {g : FE} {e : E} (he0 : e ≠ 0)
    (h : P.toValuationSubring.valuation (g - algebraMap E FE e) < 1) :
    P.toValuationSubring.valuation (g⁻¹ - algebraMap E FE e⁻¹) < 1 := by
  have hvg := valuation_eq_one_of_sub_lt_one P he0 h
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [Valuation.map_zero] at hvg; exact zero_ne_one hvg
  have he' : algebraMap E FE e ≠ 0 := (map_ne_zero (algebraMap E FE)).2 he0
  have : g⁻¹ - algebraMap E FE e⁻¹ = -(g - algebraMap E FE e) * (g⁻¹ * (algebraMap E FE e)⁻¹) := by
    rw [map_inv₀]
    field_simp
    ring
  rw [this, Valuation.map_mul, Valuation.map_neg, Valuation.map_mul, Valuation.map_inv,
    Valuation.map_inv, hvg, valuation_algebraMap_eq_one P he0]
  simpa using h

variable (A : ValuationSubring E)

/-- The composite valuation subring of `FE` cut out by `A` and a place `P`: the elements that are
`P`-adically close to a constant in `A`. -/
def compositeRing [IsAlgClosed E] (P : Place E FE) [Module.Finite E P.ResidueField] :
    ValuationSubring FE where
  carrier := {g | ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (g - algebraMap E FE a) < 1}
  mul_mem' := by
    rintro g h ⟨a, haA, ha⟩ ⟨b, hbA, hb⟩
    refine ⟨a * b, mul_mem haA hbA, ?_⟩
    have hg1 : P.toValuationSubring.valuation g ≤ 1 :=
      (P.toValuationSubring.valuation_le_one_iff _).2 (mem_of_valuation_sub_lt_one P ha)
    have : g * h - algebraMap E FE (a * b) =
        g * (h - algebraMap E FE b) + algebraMap E FE b * (g - algebraMap E FE a) := by
      rw [map_mul]; ring
    rw [this]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      calc P.toValuationSubring.valuation g * P.toValuationSubring.valuation (h - algebraMap E FE b)
          ≤ 1 * P.toValuationSubring.valuation (h - algebraMap E FE b) :=
            mul_le_mul_left hg1 _
        _ < 1 := by rw [one_mul]; exact hb
    · rw [map_mul]
      calc P.toValuationSubring.valuation (algebraMap E FE b) *
            P.toValuationSubring.valuation (g - algebraMap E FE a)
          ≤ 1 * P.toValuationSubring.valuation (g - algebraMap E FE a) :=
            mul_le_mul_left (valuation_algebraMap_le_one P b) _
        _ < 1 := by rw [one_mul]; exact ha
  one_mem' := ⟨1, one_mem A, by simp⟩
  add_mem' := by
    rintro g h ⟨a, haA, ha⟩ ⟨b, hbA, hb⟩
    refine ⟨a + b, add_mem haA hbA, ?_⟩
    have : g + h - algebraMap E FE (a + b) = (g - algebraMap E FE a) + (h - algebraMap E FE b) := by
      rw [map_add]; ring
    rw [this]
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := ⟨0, zero_mem A, by simp⟩
  neg_mem' := by
    rintro g ⟨a, haA, ha⟩
    refine ⟨-a, neg_mem haA, ?_⟩
    have : -g - algebraMap E FE (-a) = -(g - algebraMap E FE a) := by rw [map_neg]; ring
    rw [this, Valuation.map_neg]
    exact ha
  mem_or_inv_mem' := by
    intro g
    simp only [Set.mem_ofPred_eq]
    by_cases hg : g ∈ P.toValuationSubring
    · obtain ⟨e, he⟩ := exists_valuation_sub_lt_one P hg
      by_cases heA : e ∈ A
      · exact Or.inl ⟨e, heA, he⟩
      · right
        have he0 : e ≠ 0 := by rintro rfl; exact heA (zero_mem A)
        have heinv : e⁻¹ ∈ A := (A.mem_or_inv_mem e).resolve_left heA
        exact ⟨e⁻¹, heinv, valuation_inv_sub_inv_lt_one P he0 he⟩
    · right
      refine ⟨0, zero_mem A, ?_⟩
      have hg' : g⁻¹ ∈ P.toValuationSubring := (P.toValuationSubring.mem_or_inv_mem g).resolve_left hg
      have hg0 : g ≠ 0 := by rintro rfl; exact hg (zero_mem _)
      rcases P.toValuationSubring.valuation_lt_one_or_eq_one ⟨g⁻¹, hg'⟩ with hlt | heq
      · simpa using hlt
      · exfalso
        apply hg
        rw [← ValuationSubring.valuation_le_one_iff]
        have : P.toValuationSubring.valuation g⁻¹ = 1 := heq
        rw [Valuation.map_inv, inv_eq_one] at this
        exact this.le

variable [IsAlgClosed E]

variable {K : Type uK} {F : Type uF} [Field K] [Field F] [Algebra K F] [Algebra K E] [Algebra F FE]
  [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]

/-- The reduced valuation subring of `F`: the constants of `A` seen inside `F` through `FE`. -/
def reducedRing (P : Place E FE) [Module.Finite E P.ResidueField] : ValuationSubring F :=
  (compositeRing A P).comap (algebraMap F FE)

theorem mem_reducedRing_iff (P : Place E FE) [Module.Finite E P.ResidueField] (f : F) :
    f ∈ reducedRing (F := F) A P ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1 :=
  Iff.rfl

omit [IsAlgClosed E] in
theorem algebraMap_algebraMap_eq (k : K) :
    algebraMap F FE (algebraMap K F k) = algebraMap E FE (algebraMap K E k) :=
  (IsScalarTower.algebraMap_apply K F FE k).symm.trans (IsScalarTower.algebraMap_apply K E FE k)

theorem algebraMap_mem_reducedRing (hK : ∀ k : K, algebraMap K E k ∈ A) (P : Place E FE)
    [Module.Finite E P.ResidueField] (k : K) : algebraMap K F k ∈ reducedRing (F := F) A P :=
  ⟨algebraMap K E k, hK k, by
    rw [algebraMap_algebraMap_eq (E := E), sub_self, Valuation.map_zero]; exact zero_lt_one⟩

theorem reducedRing_ne_top (hK : ∀ k : K, algebraMap K E k ∈ A)
    (hrat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (P : Place E FE) [Module.Finite E P.ResidueField] {x : F} (hx : Transcendental K x) :
    reducedRing (F := F) A P ≠ ⊤ := by
  intro htop
  have hall : ∀ f : F, f ∈ reducedRing (F := F) A P := fun f => htop ▸ trivial
  obtain ⟨a, haA, ha⟩ := hall x
  obtain ⟨k, hk⟩ := hrat a haA
  set y : F := x - algebraMap K F k with hy_def
  set b : E := a - algebraMap K E k with hb_def
  have hy0 : y ≠ 0 := by
    intro h0
    apply hx
    rw [sub_eq_zero.1 h0]
    exact isAlgebraic_algebraMap k
  have hyb : P.toValuationSubring.valuation (algebraMap F FE y - algebraMap E FE b) < 1 := by
    have : algebraMap F FE y - algebraMap E FE b = algebraMap F FE x - algebraMap E FE a := by
      simp only [hy_def, hb_def, map_sub, algebraMap_algebraMap_eq (E := E)]
      ring
    rwa [this]
  have hbA : b ∈ A := sub_mem haA (hK k)
  have hb1 : A.valuation b < 1 := hk
  obtain ⟨c, hcA, hc⟩ := hall y⁻¹
  rw [map_inv₀] at hc
  have hyFE0 : algebraMap F FE y ≠ 0 := (map_ne_zero _).2 hy0
  by_cases hb0 : b = 0
  · rw [hb0, map_zero, sub_zero] at hyb
    have hinv : P.toValuationSubring.valuation (algebraMap F FE y)⁻¹ ≤ 1 :=
      (P.toValuationSubring.valuation_le_one_iff _).2 (mem_of_valuation_sub_lt_one P hc)
    have h1 : (1 : _) = P.toValuationSubring.valuation (algebraMap F FE y) *
        P.toValuationSubring.valuation (algebraMap F FE y)⁻¹ := by
      rw [← Valuation.map_mul, mul_inv_cancel₀ hyFE0, Valuation.map_one]
    have : (1 : _) ≤ P.toValuationSubring.valuation (algebraMap F FE y) := by
      calc (1 : _) = _ := h1
        _ ≤ P.toValuationSubring.valuation (algebraMap F FE y) * 1 := mul_le_mul_right hinv _
        _ = _ := mul_one _
    exact absurd hyb (not_lt.2 this)
  · have hc' := valuation_inv_sub_inv_lt_one P hb0 hyb
    have hcb : c = b⁻¹ := const_unique P hc hc'
    have hunit : IsUnit (⟨b, hbA⟩ : A) := by
      refine IsUnit.of_mul_eq_one ⟨b⁻¹, hcb ▸ hcA⟩ ?_
      ext
      simp [hb0]
    have := (ValuationSubring.valuation_eq_one_iff _ _).1 hunit
    rw [show ((⟨b, hbA⟩ : A) : E) = b from rfl] at this
    rw [this] at hb1
    exact lt_irrefl _ hb1

set_option linter.style.haveILetI false in
/-- The place reduction `r`, as a function of places: the reduced place is the one cut out by the
reduced valuation subring. -/
theorem exists_placeReduction [CharZero K] [IsCurveOver E FE]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hK : ∀ k : K, algebraMap K E k ∈ A)
    (hrat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) :
    ∃ r : Place E FE → Place K F, ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1 := by
  obtain ⟨x, hx, hfin⟩ := hfg
  haveI := hfin
  have hex : ∀ P : Place E FE, ∃ v : Place K F,
      v.toValuationSubring = @reducedRing E FE _ _ _ A _ F _ _ P (IsCurveOver.finiteResidue P) := by
    intro P
    haveI : Module.Finite E P.ResidueField := IsCurveOver.finiteResidue P
    exact Place.exists_of_valuationSubring x (reducedRing (F := F) A P)
      (algebraMap_mem_reducedRing A hK P) (reducedRing_ne_top A hK hrat P hx)
  choose r hr using hex
  refine ⟨r, fun P f => ?_⟩
  rw [hr P]
  exact @mem_reducedRing_iff E FE _ _ _ A _ F _ _ P (IsCurveOver.finiteResidue P) f

end Reduction

section Lift

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
  [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]

set_option linter.style.haveILetI false in
theorem exists_sub_algebraMap_mem_maximalIdeal [IsAlgClosed K] [IsCurveOver K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) :
    ∃ k : K, (⟨f, hf⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring k ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
  obtain ⟨k, hk⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := v.ResidueField)).2 (IsLocalRing.residue _ ⟨f, hf⟩)
  exact ⟨k, by rw [← Ideal.Quotient.eq]; exact hk.symm⟩

theorem placeReduction_eq_of_comap_eq [IsAlgClosed K] [IsCurveOver K F]
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (P : Place E FE) (v : Place K F)
    (hPv : P.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring) :
    r P = v := by
  apply Place.ext
  ext f
  rw [hr P f]
  constructor
  · rintro ⟨a, -, ha⟩

    have hfP : algebraMap F FE f ∈ P.toValuationSubring := by
      rw [← ValuationSubring.valuation_le_one_iff]
      have : algebraMap F FE f = (algebraMap F FE f - algebraMap E FE a) + algebraMap E FE a := by
        ring
      rw [this]
      exact Valuation.map_add_le _ ha.le
        ((P.toValuationSubring.valuation_le_one_iff _).2 (P.algebraMap_mem' a))
    have : f ∈ P.toValuationSubring.comap (algebraMap F FE) := hfP
    rwa [hPv] at this
  · intro hf
    obtain ⟨k, hk⟩ := exists_sub_algebraMap_mem_maximalIdeal v hf
    refine ⟨algebraMap K E k, hKA k, ?_⟩

    have hmemv : f - algebraMap K F k ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' k)
    have hlt : v.toValuationSubring.valuation (f - algebraMap K F k) < 1 := by
      have := (ValuationSubring.valuation_lt_one_iff v.toValuationSubring
        (⟨f, hf⟩ - algebraMap K v.toValuationSubring k)).1 hk
      simpa using this

    have hmemP : algebraMap F FE (f - algebraMap K F k) ∈ P.toValuationSubring := by
      have : f - algebraMap K F k ∈ P.toValuationSubring.comap (algebraMap F FE) := by
        rw [hPv]; exact hmemv
      exact this
    have hcomm : algebraMap F FE (f - algebraMap K F k) =
        algebraMap F FE f - algebraMap E FE (algebraMap K E k) := by
      rw [map_sub, (IsScalarTower.algebraMap_apply K F FE k).symm,
        IsScalarTower.algebraMap_apply K E FE k]
    rw [← hcomm]

    set g : F := f - algebraMap K F k with hg
    rcases P.toValuationSubring.valuation_lt_one_or_eq_one ⟨_, hmemP⟩ with h | h
    · exact h
    · exfalso
      have h' : P.toValuationSubring.valuation (algebraMap F FE g) = 1 := h
      have hg0 : g ≠ 0 := by
        intro h0
        rw [h0, map_zero, Valuation.map_zero] at h'
        exact zero_ne_one h'
      have hinvP : (algebraMap F FE g)⁻¹ ∈ P.toValuationSubring := by
        rw [← ValuationSubring.valuation_le_one_iff, Valuation.map_inv]
        rw [h', inv_one]
      have hinvv : g⁻¹ ∈ v.toValuationSubring := by
        have : g⁻¹ ∈ P.toValuationSubring.comap (algebraMap F FE) := by
          show algebraMap F FE g⁻¹ ∈ P.toValuationSubring
          rwa [map_inv₀]
        rwa [hPv] at this
      have hunit : IsUnit (⟨g, hmemv⟩ : v.toValuationSubring) :=
        IsUnit.of_mul_eq_one ⟨g⁻¹, hinvv⟩ (by ext; simp [hg0])
      have h1 := (ValuationSubring.valuation_eq_one_iff _ _).1 hunit
      have h1' : v.toValuationSubring.valuation g = 1 := h1
      rw [h1'] at hlt
      exact lt_irrefl _ hlt

end Lift

end BaseChange

end Pic0

end AlgebraicCurve

open AlgebraicCurve.Pic0.BaseChange in
/-- **The `Pic0` lift of a correspondence is a coboundary after the base change.** A correspondence
whose divisor is principal after the place reduction, lifted along the free algebra on the family
`F' i`, vanishes in `Pic0` as soon as its base-changed form `F'E i` does. -/
theorem AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_baseChange
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : ι → Type*) [∀ i, Field (F'E i)] [∀ i, Algebra E (F'E i)] [∀ i, Algebra (F' i) (F'E i)]
    [∀ i, Algebra K (F'E i)] [∀ i, IsScalarTower K E (F'E i)] [∀ i, IsScalarTower K (F' i) (F'E i)]
    [∀ i, IsCurveOver E (F'E i)]
    (hfgE' : ∀ i, ∃ x' : F'E i, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set (F'E i))) (F'E i))
    (hgen' : ∀ i, IntermediateField.adjoin E (Set.range (algebraMap (F' i) (F'E i))) = ⊤)
    (φE ψE : ∀ i, FE →ₐ[E] F'E i)
    (hφcomm : ∀ i (f : F), φE i (algebraMap F FE f) = algebraMap (F' i) (F'E i) (φ i f))
    (hψcomm : ∀ i (f : F), ψE i (algebraMap F FE f) = algebraMap (F' i) (F'E i) (ψ i f))
    (hφE : ∀ i, (φE i).toRingHom.IsIntegral) (hψE : ∀ i, (ψE i).toRingHom.IsIntegral)
    (hFIE : ∀ i, FundamentalIdentityAlong E (φE i) (hφE i))
    (hfinE : ∀ i, FiniteAlong E (ψE i)) (hNE : ∀ i, NormFormulaAlong E (ψE i) (hfinE i))
    (hpE : FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) (hfinE i) (hNE i)).toIntLinearMap)
        p = 0) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0 := by
  classical

  set TPE : ι → Pic0 E FE →+ Pic0 E FE := fun i =>
    Pic0.correspondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) (hfinE i) (hNE i) with hTPE
  let TZE : ι → Divisor.degZero (K := E) (F := FE) →+ Divisor.degZero (K := E) (F := FE) :=
    fun i => Pic0.degZeroCorrespondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i)
  let TDE : ι → Divisor E FE →+ Divisor E FE :=
    fun i => Divisor.correspondence (φE i) (ψE i) (hφE i) (hψE i)
  let TPK : ι → Pic0 K F →+ Pic0 K F := fun i =>
    Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)
  let TZK : ι → Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
    fun i => Pic0.degZeroCorrespondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i)
  let TDK : ι → Divisor K F →+ Divisor K F :=
    fun i => Divisor.correspondence (φ i) (ψ i) (hφ i) (hψ i)

  apply LinearMap.ext
  intro c
  obtain ⟨D₀, rfl⟩ := Pic0.mk_surjective c
  rw [LinearMap.zero_apply]
  have h1 : FreeAlgebra.lift ℤ (fun i => (TPK i).toIntLinearMap) p (Pic0.mk D₀) =
      Pic0.mk (FreeAlgebra.lift ℤ (fun i => (TZK i).toIntLinearMap) p D₀) := by
    have := lift_equivariant (mkHom (k := K) (L := F)) TZK TPK (fun i a => rfl) p D₀
    simpa only [mkHom_apply] using this.symm
  have h2 : ((FreeAlgebra.lift ℤ (fun i => (TZK i).toIntLinearMap) p D₀ :
      Divisor.degZero (K := K) (F := F)) : Divisor K F) =
      FreeAlgebra.lift ℤ (fun i => (TDK i).toIntLinearMap) p (D₀ : Divisor K F) :=
    lift_equivariant (Divisor.degZero (K := K) (F := F)).subtype TZK TDK (fun i a => rfl) p D₀
  rw [h1, mk_eq_zero_iff, h2]

  obtain ⟨A, hKA, σ, hkerσ, hsec, -⟩ :=
    IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one K E ∅
      (Finset.notMem_empty _)
  have hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1 := by
    intro a ha
    refine ⟨σ ⟨a, ha⟩, ?_⟩
    have hmem : (⟨a, ha⟩ : A) - ⟨algebraMap K E (σ ⟨a, ha⟩), hKA _⟩ ∈ RingHom.ker σ := by
      rw [RingHom.mem_ker, map_sub, hsec, sub_self]
    rw [hkerσ] at hmem
    exact (ValuationSubring.valuation_lt_one_iff _ _).1 hmem

  obtain ⟨r, hr⟩ := exists_placeReduction (F := F) (FE := FE) A hfg hKA hArat
  obtain ⟨O, ρ, hO, hkerρ, -, hunit, hρF⟩ :=
    AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring
      K F E FE hfg hfgE hgen A hKA σ hkerσ hsec

  have hex : ∀ v : Place K F, ∃ P : Place E FE,
      P.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring := fun v => by
    obtain ⟨P, hP, -, -⟩ :=
      AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE
        hgen v
    exact ⟨P, hP⟩
  choose ℓ hℓ using hex
  have hrℓ : ∀ v, r (ℓ v) = v := fun v =>
    placeReduction_eq_of_comap_eq A hKA r hr (ℓ v) v (hℓ v)
  set D' : Divisor E FE := Finsupp.mapDomain ℓ (D₀ : Divisor K F) with hD'
  have hrD' : Finsupp.mapDomain r D' = (D₀ : Divisor K F) := by
    rw [hD', ← Finsupp.mapDomain_comp]
    have : r ∘ ℓ = id := funext hrℓ
    rw [this, Finsupp.mapDomain_id]
  have hD'deg : D' ∈ Divisor.degZero (K := E) (F := FE) := by
    rw [Divisor.mem_degZero, hD', degree_eq_sum, Finsupp.sum_mapDomain_index (fun _ => rfl)
      (fun _ _ _ => rfl), ← degree_eq_sum]
    exact D₀.2
  set DZ' : Divisor.degZero (K := E) (F := FE) := ⟨D', hD'deg⟩ with hDZ'

  have h4 : FreeAlgebra.lift ℤ (fun i => (TPE i).toIntLinearMap) p (Pic0.mk DZ') =
      Pic0.mk (FreeAlgebra.lift ℤ (fun i => (TZE i).toIntLinearMap) p DZ') := by
    have := lift_equivariant (mkHom (k := E) (L := FE)) TZE TPE (fun i a => rfl) p DZ'
    simpa only [mkHom_apply] using this.symm
  have h5 : ((FreeAlgebra.lift ℤ (fun i => (TZE i).toIntLinearMap) p DZ' :
      Divisor.degZero (K := E) (F := FE)) : Divisor E FE) =
      FreeAlgebra.lift ℤ (fun i => (TDE i).toIntLinearMap) p D' :=
    lift_equivariant (Divisor.degZero (K := E) (F := FE)).subtype TZE TDE (fun i a => rfl) p DZ'
  have h6 : FreeAlgebra.lift ℤ (fun i => (TPE i).toIntLinearMap) p (Pic0.mk DZ') = 0 := by
    rw [hpE, LinearMap.zero_apply]
  rw [h4, mk_eq_zero_iff, h5] at h6
  obtain ⟨g, hg0, hg⟩ := h6

  obtain ⟨c, hcg, hρcg⟩ := hunit g hg0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hρcg
    have : (⟨(0 : E) • g, hcg⟩ : O) = 0 := by ext; simp
    rw [this, map_zero]
  set Dg : Divisor E FE := FreeAlgebra.lift ℤ (fun i => (TDE i).toIntLinearMap) p D' with hDg_def
  have hDg : ∀ P : Place E FE, Dg P = P.ord ((⟨c • g, hcg⟩ : O) : FE) := fun P => by
    rw [hg P]
    exact (AlgebraicCurve.Place.ord_smul_of_ne_zero P hc0 g).symm

  have hprin : Divisor.IsPrincipal (K := K) (F := F) (Finsupp.mapDomain r Dg) := by
    refine ⟨ρ ⟨c • g, hcg⟩, hρcg, fun v => ?_⟩
    exact AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction K F E FE hfg hfgE
      hgen A r hKA hArat hr O ρ hO hkerρ hρF ⟨c • g, hcg⟩ hρcg Dg hDg v

  have h3 : Finsupp.mapDomain r Dg =
      FreeAlgebra.lift ℤ (fun i => (TDK i).toIntLinearMap) p (Finsupp.mapDomain r D') := by
    have := lift_equivariant (Finsupp.mapDomain.addMonoidHom r) TDE TDK (fun i D'' => ?_) p D'
    · simpa only [Finsupp.mapDomain.addMonoidHom_apply] using this
    · simp only [Finsupp.mapDomain.addMonoidHom_apply]
      exact AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence K F hfg (F' i)
        (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i) E FE hfgE hgen (F'E i) (hfgE' i)
        (hgen' i) (φE i) (ψE i) (hφcomm i) (hψcomm i) (hφE i) (hψE i) (hFIE i) (hfinE i)
        (hNE i) A hKA hArat r hr D''
  rw [h3, hrD'] at hprin
  exact hprin
