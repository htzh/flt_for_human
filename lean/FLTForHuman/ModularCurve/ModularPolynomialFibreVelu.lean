/-
The fibre polynomial is the product of the Vélu quotients' `j`-invariants.

`ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j` (544 pin lines): for a
`ModularPolynomialData ℓ` with `ℓ ≠ 2`, an elliptic curve `W/K` over an algebraically closed field and an
`ℓ`-torsion basis `Q : ι → W.Point` (`card ι = ℓ + 1`), the fibre polynomial's value in `j` is
`∏ i, j (W / ⟨Q i⟩)` — the **counting** half of the modular polynomial, whose datum half SET-AF106E
landed (`ModularPolynomialHasseDescent.lean`, `ModularPolynomialData.eq_all`).

Its six premise modules are the arithmetic machinery of the last five sets
(`Automorphism/NormalForm`, `ModularPolynomialVelu`, `Reduction/ReduceHomSurjective`,
`Velu/{Discriminant,Reduction}`, `RingTheory/WittVector/Lift`). The existing
`ModularCurve/ModularPolynomialFibreTwo.lean` is about the `ℓ = 2` fibre and is **below four of the six**
(measured), so it cannot host this row; this module sits above all of them.

## The row

* `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j` — 544 pin `S_` lines.

## The assembly, and what was substituted

The pin proof is an assembly: a base-change prelude, a special fibre over a valuation subring, a
characteristic-zero case, and a Witt-vector lift for characteristic `p`.  Its own `S_` file **re-states**
the base-change prelude this port already carries in `ModularCurve/ModularPolynomialVelu.lean`'s
`TDescent` block, so those rows are imported rather than re-proved.  `port_advise` reads **21 of the 30
pin rows** (29 `S_` + the wrapper) as already in the port — 19 byte-identical, 2 up to binder spelling:
the 17 `TDescent` engine rows below, the pin's `solution` and the wrapper's headline (both are this
module's scaffolded declaration), the pin's `main` (the *same statement* as `solution`, so the published
name serves both and there is no separate `solution` row here), and `lift_dispatch`.

Imported from `TDescent` (`ModularPolynomialVelu.lean`; 17 rows, all used):
`nonsingular_map`, `mapFun`, `mapFun_zero`, `mapFun_some`, `mapFun_add`, `mapPoint`, `mapPoint_some`,
`mapPoint_injective`, `coordsOrZero_mapPoint`, `addOrderOf_mapPoint`, `oddOrderSummingSet_mapPoint`,
`map_veluT`, `map_veluW`, `map_veluTSum`, `map_veluWSum`, `veluQuotient_map`, `j_congr`.  One more
`TDescent` row is used as an engine, under a pin name that shifted: `TDescent.fibrePoly_map_ringHom` states
the pin's `fibrePoly_map` (`S_:207`), not the pin's own `CommRing`-flavoured `fibrePoly_map_ringHom`
(`S_:197`), and this module restates it at the pin's name in one line because the pin's own
`prodFormula_of_map` invokes `fibrePoly_map`.

Other substitutions, all one-liners in the pin:

* `lift_dispatch` — the pin's wrapper around
  `WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero`
  (`Reduction/ReduceHomSurjective.lean`, same binders).  Kept because `prodFormula_specialFibre` takes the
  lifted form as a hypothesis; its body is the imported lemma, not a re-proof.
* `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed`
  (`ModularPolynomialVelu.lean`, SET-AF107) is the transcendental-`j` premise of
  `prodFormula_specialFibre`.
* `exists_valuationSubring_with_transcendental_of_charZero`, `transcendental_j_perturb`
  (`Automorphism/NormalForm.lean`), `WittVector.exists_valuationSubring_lift_with_transcendental`
  (`RingTheory/WittVector/Lift.lean`) and
  `exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` (`Velu/Reduction.lean`) are
  imported verbatim; no body needed a different hypothesis strength.  The only adaptation inside those
  proofs is `IsAlgClosed.perfectRing`, which is an **instance** in this mathlib (`inferInstance`), not the
  term the pin applies.
* The pin's `S_` file also carries two helpers this row does not use (`isRoot_map_iff` and the
  `CommRing`-flavoured `fibrePoly_map_ringHom`); they are the proof search's duplicates of rows homed
  elsewhere, so they are not restated.

Names: the pin's generated wrapper (`P2MW.S_…`) and section labels (`A1Skeleton`, `Transport`) are
replaced by the subject namespace `ModularCurve.ModularPolynomialData`; the pin's declaration names are
kept.  `private` in the pin: none, and none added.

Two naming frictions, both handled without touching the pin's statement text (the checker hashes the
*source* statement, so a qualified spelling would be a `MISMATCH`):

* the pin's proof prelude is `open … WeierstrassCurve.Affine`, and in this port `mapPoint` and `reduceHom`
  are two **different** constants in scopes the pin did not separate: `WeierstrassCurve.mapPoint` (the
  function-field point, `Velu/Engine.lean`) and `TDescent.mapPoint` (the base-change point this row uses),
  plus `WeierstrassCurve.reduceHom`, which the pin's `lift_dispatch` and `prodFormula_specialFibre` write
  bare.  The module opens `TDescent` **before** `WeierstrassCurve` (Lean resolves a bare name to the first
  `open` that has it — measured), so the pin's `mapPoint ιh W (Q i)` is the `TDescent` engine row and
  `reduceHom` is the `WeierstrassCurve` one.  `WeierstrassCurve.Affine` is not opened: nothing in this
  module's statements needs it.
* five declarations carry `set_option linter.style.haveILetI false in` (declaration-scoped, order 107C's
  precedent): `prodFormula_of_map`, `prodFormula_specialFibre`, `main_charZero`, `main_charP`, `main`.
  All **12** flagged locals are instances fed to typeclass search (4 `IsElliptic`, 4 `DecidableEq`,
  `PerfectRing`, 2 `CharZero`, `Fact.mk`), so the linter's `have`/`let` rewrite would break the proofs; the
  suppression is the measured reason, not a preference.  The headline needs none.

## The gates (measured, `aa2d8b3`)

| gate | result |
|---|---|
| `check_port --force` | **10 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |
| engine diff (2 pin sources, 30 pin decls, 10 module decls) | **10 by hash, 0 by name (hash differs), 0 unaccounted** |
| edit loop (`-DmaxHeartbeats=200000`) | **silent** |
| `lake build` (locked) | **0 warning lines from this file** |
| `#print axioms`, all 10 public declarations | `[propext, Classical.choice, Quot.sound]`, no `sorryAx` |
| `dedup --within` | 1 cluster — **the pin's own `main` ↔ `solution` pair**: the pin declares both at the same statement (`solution := A1Skeleton.main …`); the published name is the headline and `main` keeps its pin name, so the two rows coincide. 13 removable lines, kept on purpose. |
| `move_dead --dry-run` | **0 declarations, 0 lines** |
| heartbeat probe (see below) | silent at **20000**, fails at **10000**; not installed |
| collision probe | silent over the **15** modules whose `.olean` exist (`ModularCurve/X1/RegularDifferentialsCuspForm` has no `.olean` yet — order D in flight); rerun the set-level probe after that order lands |

Heartbeat probe pair (downward ladder, one run per cap, `lake env lean -DautoImplicit=false
-DmaxHeartbeats=<cap>`): **40000 pass (33 s), 20000 pass (25 s), 10000 fail (11 s)** — 7 deterministic
timeouts, the first inside `prodFormula_specialFibre`'s `simp` at the `hPAmap` step and the rest in the two
`main_char*` proofs.  So the module's floor is `10000 < x ≤ 20000`: the default cap is 10× what the proofs
need and **no `maxHeartbeats` bump is installed** (the pin's `S_` file sets none either).  The pin floor
run (all proofs `sorry`) was not needed once a passing cap was measured: the failures are tactic lines,
not the statement types.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j.lean>

spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j.lean
-/

import FLTForHuman.ModularCurve.ModularPolynomialVelu
import FLTForHuman.RingTheory.WittVector.Lift
import FLTForHuman.WeierstrassCurve.Automorphism.NormalForm
import FLTForHuman.WeierstrassCurve.Reduction.ReduceHomSurjective
import FLTForHuman.WeierstrassCurve.Velu.Discriminant
import FLTForHuman.WeierstrassCurve.Velu.Reduction
import Mathlib.Tactic

open Polynomial ModularCurve IsLocalRing TDescent WeierstrassCurve

set_option autoImplicit false

noncomputable section

universe u

namespace ModularCurve.ModularPolynomialData

/-- The `j`-invariant of the odd Vélu quotient `W/⟨Q⟩`, as a function of the point rather than of the
quotient curve. -/
noncomputable abbrev jQuot {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (ℓ : ℕ) (Q : W.toAffine.Point)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2))).Δ ≠ 0) : F :=
  @WeierstrassCurve.j F _ (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2)))
    ⟨isUnit_iff_ne_zero.mpr hΔ⟩

/-- The fibre product formula: the fibre of `Φ` at `j(W)` is the product of `X - C (j (W/⟨Q i⟩))`. -/
def ProdFormula {F : Type*} [Field F] [DecidableEq F] {ℓ : ℕ} [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → W.toAffine.Point)
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) : Prop :=
  fibrePoly data.Φ W.j = ∏ i : ι, (X - C (jQuot W ℓ (Q i) (hΔ i)))

/-- The fibre of `Φ` at `ι a` is the image of the fibre at `a`. -/
theorem fibrePoly_map {K : Type*} [Field K] {κ : Type*} [Field κ] (ι : K →+* κ)
    (Φ : Polynomial (Polynomial ℤ)) (a : K) :
    fibrePoly Φ (ι a) = (fibrePoly Φ a).map ι :=
  TDescent.fibrePoly_map_ringHom ι Φ a

set_option linter.style.haveILetI false in
/-- **The product formula transports along an injective ring hom.**  If it holds for `W.map ιh` at the
image family `mapPoint ιh W ∘ Q`, it holds for `W` at `Q`. -/
theorem prodFormula_of_map
    {K : Type*} [Field K] [DecidableEq K] {κ : Type*} [Field κ] [DecidableEq κ]
    (ιh : K →+* κ) {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → W.toAffine.Point)
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0)
    (hΔ' : ∀ i, ((W.map ιh).veluQuotient
      ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2))).Δ ≠ 0)
    (h : ProdFormula data (W.map ιh) (fun i => mapPoint ιh W (Q i)) hΔ') :
    ProdFormula data W Q hΔ := by
  classical
  unfold ProdFormula at h ⊢
  apply Polynomial.map_injective ιh ιh.injective
  have hcurve : ∀ i, (W.map ιh).veluQuotient
      ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2)) =
      (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).map ιh := fun i => by
    rw [oddOrderSummingSet_mapPoint ιh W (Q i) (ℓ / 2),
      veluQuotient_map ιh W _ (Function.Injective.prodMap ιh.injective ιh.injective).injOn]
  have hj : ∀ i, jQuot (W.map ιh) ℓ (mapPoint ιh W (Q i)) (hΔ' i) = ιh (jQuot W ℓ (Q i) (hΔ i)) := by
    intro i
    unfold jQuot
    haveI : (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩
    rw [j_congr (hcurve i) ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩ inferInstance, WeierstrassCurve.map_j]
  rw [← fibrePoly_map, ← WeierstrassCurve.map_j, h, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hj]

/-- **Surjectivity of reduction on the prime-to-`p` torsion**, in the shape the special-fibre descent
consumes. -/
theorem lift_dispatch
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (WA : WeierstrassCurve A) (hΔA : (WA.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (WA.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (WA.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔA Q = Q₀ := by
  exact _root_.WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero A WA hΔA hℓ Q₀ hQ₀

set_option linter.style.haveILetI false in
/-- **The special fibre.**  If a Weierstrass model `WA` over a valuation subring `A ≤ L` reduces smoothly,
every `ℓ`-torsion point of the residue curve lifts to an `ℓ`-torsion point of `WA` over `A`, and the
generic `j` is transcendental, then the product formula holds over the residue field: pull the `ℓ + 1`
points back to the fraction field (where the transcendental hypothesis applies), compare the two sides in
`A`, and reduce. -/
theorem prodFormula_specialFibre
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (WA : WeierstrassCurve A) (hΔA : (WA.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ : (ℓ : ResidueField A) ≠ 0)
    (hlift : ∀ Q₀ : (WA.map (residue A)).toAffine.Point, ℓ • Q₀ = 0 →
      ∃ Q : (WA.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔA Q = Q₀)
    (data : ModularPolynomialData ℓ)
    (htr : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype) ⟨isUnit_iff_ne_zero.mpr hΔL⟩))
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q' : ι → (WA.map (residue A)).toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = ℓ)
    (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
    [hE : (WA.map (residue A)).IsElliptic]
    (hΔ' : ∀ i, ((WA.map (residue A)).veluQuotient
      ((WA.map (residue A)).oddOrderSummingSet (Q' i) (ℓ / 2))).Δ ≠ 0) :
    ProdFormula data (WA.map (residue A)) Q' hΔ' := by
  classical
  have hℓP : ℓ.Prime := Fact.out

  have hresΔ : residue A WA.Δ ≠ 0 := by rwa [← WeierstrassCurve.map_Δ]
  have hΔunit : IsUnit WA.Δ := by
    by_contra h
    exact hresΔ ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
  haveI hWA : WA.IsElliptic := ⟨hΔunit⟩
  have hΔL : (WA.map A.subtype).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    intro h
    exact hΔunit.ne_zero (Subtype.val_injective (by simpa using h))
  haveI : (WA.map A.subtype).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔL⟩

  have hlift' : ∀ i, ∃ Qt : (WA.map A.subtype).toAffine.Point,
      ℓ • Qt = 0 ∧ reduceHom hΔA Qt = Q' i := fun i =>
    hlift (Q' i) (by rw [← hQ' i]; exact addOrderOf_nsmul_eq_zero (Q' i))
  choose Qt hQt using hlift'

  have hQt_ne : ∀ i, Qt i ≠ 0 := by
    intro i h
    have h1 : Q' i = 0 := by rw [← (hQt i).2, h, map_zero]
    have h2' : addOrderOf (Q' i) = 1 := by rw [h1, addOrderOf_zero]
    rw [hQ' i] at h2'
    exact hℓP.one_lt.ne' h2'
  have hQt_ord : ∀ i, addOrderOf (Qt i) = ℓ := fun i =>
    addOrderOf_eq_prime (hQt i).1 (hQt_ne i)
  have hQt_inj : Function.Injective fun i => AddSubgroup.zmultiples (Qt i) := by
    intro i i' h
    apply hQ'inj
    simp only at h ⊢
    have := congrArg (AddSubgroup.map (reduceHom hΔA)) h
    rwa [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples, (hQt i).2, (hQt i').2] at this

  have hodd : 2 * (ℓ / 2) + 1 = ℓ := by
    rcases hℓP.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact Nat.two_mul_div_two_add_one_of_odd h
  have hΔt : ∀ i, ((WA.map A.subtype).veluQuotient
      ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2))).Δ ≠ 0 := fun i =>
    _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
      (WA.map A.subtype) (ℓ / 2) (Qt i) (by rw [hodd]; exact hQt_ord i)

  have hT := _root_.ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed (K := L) hℓ2 data (WA.map A.subtype) (htr hΔL) hι Qt hQt_ord hQt_inj hΔt

  have hS : ∀ i, ∃ V : WeierstrassCurve A,
      V.map A.subtype = (WA.map A.subtype).veluQuotient ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2)) ∧
      V.map (residue A) = (WA.map (residue A)).veluQuotient
        ((WA.map (residue A)).oddOrderSummingSet (reduceHom hΔA (Qt i)) (ℓ / 2)) := fun i =>
    _root_.WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom A WA hΔA hℓ (Qt i) (hQt_ord i) (Nat.div_lt_self hℓP.pos one_lt_two)
  choose V hV using hS

  have hVres : ∀ i, (V i).map (residue A) =
      (WA.map (residue A)).veluQuotient ((WA.map (residue A)).oddOrderSummingSet (Q' i) (ℓ / 2)) := by
    intro i; rw [(hV i).2, (hQt i).2]
  have hVunit : ∀ i, IsUnit (V i).Δ := by
    intro i
    by_contra h
    apply hΔ' i
    rw [← hVres i, WeierstrassCurve.map_Δ]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h)
  haveI hVell : ∀ i, (V i).IsElliptic := fun i => ⟨hVunit i⟩

  have hjgen : ∀ i, @WeierstrassCurve.j L _ ((WA.map A.subtype).veluQuotient
      ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔt i)⟩
        = A.subtype (V i).j := by
    intro i
    have e := (hV i).1
    have : ∀ (V' : WeierstrassCurve L) (hV' : V' = (V i).map A.subtype) (h' : V'.IsElliptic),
        @WeierstrassCurve.j L _ V' h' = A.subtype (V i).j := by
      rintro V' rfl h'; exact WeierstrassCurve.map_j (V i) A.subtype
    exact this _ e.symm _
  have hjres : ∀ i, jQuot (WA.map (residue A)) ℓ (Q' i) (hΔ' i) = residue A (V i).j := by
    intro i
    have e := hVres i
    have : ∀ (V' : WeierstrassCurve (ResidueField A)) (hV' : V' = (V i).map (residue A))
        (h' : V'.IsElliptic), @WeierstrassCurve.j _ _ V' h' = residue A (V i).j := by
      rintro V' rfl h'; exact WeierstrassCurve.map_j (V i) (residue A)
    exact this _ e.symm _

  set PA : Polynomial A := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) WA.j) with hPA
  set QA : Polynomial A := ∏ i, (X - C (V i).j) with hQA

  have hPAmap : ∀ {S : Type _} [CommRing S] (g : A →+* S),
      PA.map g = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (g WA.j)) := by
    intro S _ g
    rw [hPA, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext n; simp
    · simp
  have hPAgen : PA.map A.subtype = fibrePoly data.Φ (WA.map A.subtype).j := by
    rw [hPAmap, WeierstrassCurve.map_j]; rfl
  have hPAres : PA.map (residue A) = fibrePoly data.Φ (WA.map (residue A)).j := by
    rw [hPAmap]
    have : (WA.map (residue A)).j = residue A WA.j := WeierstrassCurve.map_j WA (residue A)
    rw [this]; rfl

  have hQAgen : QA.map A.subtype = ∏ i, (X - C (@WeierstrassCurve.j L _ ((WA.map A.subtype).veluQuotient
      ((WA.map A.subtype).oddOrderSummingSet (Qt i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔt i)⟩)) := by
    rw [hQA, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjgen i]
  have hQAres : QA.map (residue A) = ∏ i, (X - C (jQuot (WA.map (residue A)) ℓ (Q' i) (hΔ' i))) := by
    rw [hQA, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjres i]

  have hPQ : PA = QA := by
    apply Polynomial.map_injective A.subtype Subtype.val_injective
    rw [hPAgen, hQAgen]
    exact hT

  show fibrePoly data.Φ (WA.map (residue A)).j = ∏ i, (X - C (jQuot (WA.map (residue A)) ℓ (Q' i) (hΔ' i)))
  rw [← hPAres, ← hQAres, hPQ]

set_option linter.style.haveILetI false in
/-- **Characteristic zero.**  Embed `K` in a valued field `L/A` whose residue field is `K` again and
whose `j` is transcendental, then read the special-fibre formula back along the residue map. -/
theorem main_charZero
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    ProdFormula data W Q hΔ := by
  classical

  obtain ⟨L, _, _, _, A, φ, hφ, ιh, hι_res, t, htA, htm, htr⟩ := _root_.WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero K
  letI : DecidableEq L := Classical.decEq _
  letI : DecidableEq (ResidueField A) := Classical.decEq _

  let tA : A := ⟨t, htA⟩
  let WA : WeierstrassCurve A :=
    ⟨⟨φ W.a₁, hφ _⟩, ⟨φ W.a₂, hφ _⟩, ⟨φ W.a₃, hφ _⟩, ⟨φ W.a₄, hφ _⟩ + tA, ⟨φ W.a₆, hφ _⟩ + tA ^ 2⟩
  have htres : residue A tA = 0 := (residue_eq_zero_iff (R := A) tA).mpr htm
  have hWA_res : WA.map (residue A) = W.map ιh := by
    ext <;> simp [WA, WeierstrassCurve.map, hι_res, htres]
  have hWA_gen : WA.map A.subtype = ⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ := by
    ext <;> rfl

  obtain ⟨hΔgen, _⟩ := _root_.WeierstrassCurve.transcendental_j_perturb (R := K) φ t htr W
  have htrWA : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype) ⟨isUnit_iff_ne_zero.mpr hΔL⟩) := by
    intro hΔL
    rwa [j_congr hWA_gen ⟨isUnit_iff_ne_zero.mpr hΔL⟩ ⟨isUnit_iff_ne_zero.mpr hΔgen⟩]

  have hΔA : (WA.map (residue A)).Δ ≠ 0 := by
    rw [hWA_res, WeierstrassCurve.map_Δ]; exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero
  have hℓκ : (ℓ : ResidueField A) ≠ 0 := by
    rw [← map_natCast ιh, _root_.map_ne_zero]; exact Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero

  have key : ∀ (X : WeierstrassCurve (ResidueField A)) (hX : WA.map (residue A) = X)
      [X.IsElliptic] (Q' : ι → X.toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = ℓ)
      (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
      (hΔ' : ∀ i, (X.veluQuotient (X.oddOrderSummingSet (Q' i) (ℓ / 2))).Δ ≠ 0),
      ProdFormula data X Q' hΔ' := by
    rintro X rfl _ Q' hQ' hQ'inj hΔ'
    exact prodFormula_specialFibre A WA hΔA hℓ2 hℓκ (lift_dispatch A WA hΔA hℓκ) data htrWA hι
      Q' hQ' hQ'inj hΔ'

  have hQ' : ∀ i, addOrderOf (mapPoint ιh W (Q i)) = ℓ := fun i => by rw [addOrderOf_mapPoint, hQ i]
  have hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ιh W (Q i)) := by
    intro i j hij
    apply hQinj
    have h1 : ∀ k, AddSubgroup.zmultiples (mapPoint ιh W (Q k))
        = (AddSubgroup.zmultiples (Q k)).map (mapPoint ιh W) := fun k =>
      (AddMonoidHom.map_zmultiples (mapPoint ιh W) (Q k)).symm
    simp only [h1] at hij
    exact AddSubgroup.map_injective (mapPoint_injective ιh W) hij
  have hΔ' : ∀ i, ((W.map ιh).veluQuotient
      ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2))).Δ ≠ 0 := fun i => by
    have hodd : ℓ = 2 * (ℓ / 2) + 1 := by
      have := (Fact.out : ℓ.Prime).eq_two_or_odd'.resolve_left hℓ2
      obtain ⟨m, hm⟩ := this; omega
    exact _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq (W.map ιh) (ℓ / 2) (mapPoint ιh W (Q i)) (by rw [hQ' i]; exact hodd)
  exact prodFormula_of_map ιh data W Q hΔ hΔ' (key (W.map ιh) hWA_res _ hQ' hQ'inj hΔ')

set_option linter.style.haveILetI false in
/-- **Characteristic `p`.**  Lift `K` to the Witt vectors of `K`, embed them in a valued field with
transcendental `j`, and run the same special-fibre read-back; `K` perfect is automatic over an
algebraically closed field. -/
theorem main_charP
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    ProdFormula data W Q hΔ := by
  classical
  haveI : PerfectRing K q := inferInstance
  obtain ⟨L, _, _, _, A, φ, hφ, ιh, hι_res, t, htA, htm, htr⟩ := _root_.WittVector.exists_valuationSubring_lift_with_transcendental q K
  letI : DecidableEq L := Classical.decEq _
  letI : DecidableEq (ResidueField A) := Classical.decEq _

  haveI : CharZero (WittVector q K) := φ.charZero

  let τ : K → WittVector q K := WittVector.teichmuller q
  let W𝕎 : WeierstrassCurve (WittVector q K) := ⟨τ W.a₁, τ W.a₂, τ W.a₃, τ W.a₄, τ W.a₆⟩
  let tA : A := ⟨t, htA⟩
  let WA : WeierstrassCurve A :=
    ⟨⟨φ (τ W.a₁), hφ _⟩, ⟨φ (τ W.a₂), hφ _⟩, ⟨φ (τ W.a₃), hφ _⟩,
     ⟨φ (τ W.a₄), hφ _⟩ + tA, ⟨φ (τ W.a₆), hφ _⟩ + tA ^ 2⟩
  have htres : residue A tA = 0 := (residue_eq_zero_iff (R := A) tA).mpr htm
  have hWA_res : WA.map (residue A) = W.map ιh := by
    ext <;> simp [WA, τ, WeierstrassCurve.map, hι_res, htres]
  have hWA_gen : WA.map A.subtype =
      ⟨φ W𝕎.a₁, φ W𝕎.a₂, φ W𝕎.a₃, φ W𝕎.a₄ + t, φ W𝕎.a₆ + t ^ 2⟩ := by
    ext <;> rfl

  obtain ⟨hΔgen, _⟩ := _root_.WeierstrassCurve.transcendental_j_perturb (R := WittVector q K) φ t htr W𝕎
  have htrWA : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype) ⟨isUnit_iff_ne_zero.mpr hΔL⟩) := by
    intro hΔL
    rwa [j_congr hWA_gen ⟨isUnit_iff_ne_zero.mpr hΔL⟩ ⟨isUnit_iff_ne_zero.mpr hΔgen⟩]

  have hΔA : (WA.map (residue A)).Δ ≠ 0 := by
    rw [hWA_res, WeierstrassCurve.map_Δ]; exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero
  have hℓκ : (ℓ : ResidueField A) ≠ 0 := by
    rw [← map_natCast ιh, _root_.map_ne_zero]; exact hℓK

  have key : ∀ (X : WeierstrassCurve (ResidueField A)) (hX : WA.map (residue A) = X)
      [X.IsElliptic] (Q' : ι → X.toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = ℓ)
      (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
      (hΔ' : ∀ i, (X.veluQuotient (X.oddOrderSummingSet (Q' i) (ℓ / 2))).Δ ≠ 0),
      ProdFormula data X Q' hΔ' := by
    rintro X rfl _ Q' hQ' hQ'inj hΔ'
    exact prodFormula_specialFibre A WA hΔA hℓ2 hℓκ (lift_dispatch A WA hΔA hℓκ) data htrWA hι
      Q' hQ' hQ'inj hΔ'

  have hQ' : ∀ i, addOrderOf (mapPoint ιh W (Q i)) = ℓ := fun i => by rw [addOrderOf_mapPoint, hQ i]
  have hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ιh W (Q i)) := by
    intro i j hij
    apply hQinj
    have h1 : ∀ k, AddSubgroup.zmultiples (mapPoint ιh W (Q k))
        = (AddSubgroup.zmultiples (Q k)).map (mapPoint ιh W) := fun k =>
      (AddMonoidHom.map_zmultiples (mapPoint ιh W) (Q k)).symm
    simp only [h1] at hij
    exact AddSubgroup.map_injective (mapPoint_injective ιh W) hij
  have hΔ' : ∀ i, ((W.map ιh).veluQuotient
      ((W.map ιh).oddOrderSummingSet (mapPoint ιh W (Q i)) (ℓ / 2))).Δ ≠ 0 := fun i => by
    have hodd : ℓ = 2 * (ℓ / 2) + 1 := by
      have := (Fact.out : ℓ.Prime).eq_two_or_odd'.resolve_left hℓ2
      obtain ⟨m, hm⟩ := this; omega
    exact _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq (W.map ιh) (ℓ / 2) (mapPoint ιh W (Q i)) (by rw [hQ' i]; exact hodd)
  exact prodFormula_of_map ιh data W Q hΔ hΔ' (key (W.map ιh) hWA_res _ hQ' hQ'inj hΔ')

set_option linter.style.haveILetI false in
/-- **The product formula at an algebraically closed field** (`ProdFormula` form), split by the
characteristic.  The pin's `main`. -/
theorem main
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  obtain ⟨p, _⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · haveI := Fact.mk hprime
    exact main_charP p hℓ2 hℓK data W hι Q hQ hQinj hΔ
  · haveI : CharZero K := CharP.charP_to_charZero K
    exact main_charZero hℓ2 data W hι Q hQ hQinj hΔ

end ModularCurve.ModularPolynomialData

/-- **The fibre polynomial is the Vélu product**: for a `ModularPolynomialData ℓ` with `ℓ ≠ 2` and an
`ℓ`-torsion basis of an elliptic curve over an algebraically closed field, the fibre of `Φ` at `j(W)` is
`∏ i, (X - C (j (W/⟨Q i⟩)))`. -/
theorem ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) :=
  ModularCurve.ModularPolynomialData.main hℓ2 hℓK data W hι Q hQ hQinj hΔ
