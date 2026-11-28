/-
`q`-th roots of residues lift, at Krull dimension one.

`AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one`
(249 pin lines, 10 public declarations): if the residue field's genus equals `F`'s, the prolongation is
unramified in the `genusFF` sense, `q` is a prime invertible in the residue field and `w ^ q = residue f`
with `f`'s order divisible by `q` everywhere, then `f` is a `q`-th power in `F`.

The consumer of SET-AF110D's genus bound (`Genus/GenusFFKrullDim`) and of the Kummer/RR-space layer
(`RegularProlongationKummer`, `Genus/SplittingFieldGenus`, `WeierstrassCurve/Place/RRSpace`); no existing
module is above all four, so the home is new.

## The rows

* `AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one` — 249 pin `S_` lines.

## The declaration surface — 2 of the 10 pin rows are imported, not re-proved

The pin's `S_` file is a surface of **10 declarations**, all public:

| pin line | row | here |
|---:|---|---|
| 34 | `mem_of_isRoot_monic` | imported: `AlgebraicCurve.RegularProlongation.ResidueIntegralClosure.mem_of_isRoot_monic` |
| 42 | `isAlgClosed_residueField` | imported: same block, `…ResidueIntegralClosure.isAlgClosed_residueField` |
| 63 | `exists_isPrimitiveRoot_algebraMap` | declared |
| 69 | `exists_finset_roots` | declared |
| 82 | `exists_transcendental_of_finiteDimensional` | declared |
| 111 | `finrank_adjoin_algebraMap_mul` | declared |
| 128 | `finiteDimensional_adjoin_algebraMap` | declared |
| 136 | `transcendental_of_finrank_pos` | declared |
| 151 | `main` | declared |
| 228 | `solution` | folded into the row's own name |

`mem_of_isRoot_monic` and `isAlgClosed_residueField` are **byte-identical** copies, already public in
`RegularProlongationResidueIntegralClosure.lean` (the pin repeats them from the Kummer/residue prelude);
this module imports them and re-proves neither (`port_advise` tier 1, hash match, 0 suspect).

## Naming and provenance

The pin's generated label `W10C1` is dropped: its helpers live in `AlgebraicCurve.RegularProlongation`,
the headline's namespace. The pin's premise `AlgebraicCurve.KummerCover.finrank_eq` is **not ported as a
declaration**; its pin proof is one line of mathlib
(`finrank_of_isSplittingField_X_pow_sub_C hζ (X_pow_sub_C_irreducible_of_prime hp.out hf) L`), which is
inlined at its single use site here, so nothing below the home is needed.

`dedup --within` reports exactly one cluster, `main` ↔ the headline: the pin states them with the *same
signature and the same conclusion* (`main` is `solution`'s worker; the pin writes `[hqp : Fact q.Prime]`
on one and `[Fact q.Prime]` on the other), so this is the pin's own engine↔headline pair, kept because
the pin's declaration surface is the wire.

## What the transcription measured

* `check_port --force`: **8 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.
* `port_omissions` (the engine diff): **11 pin public declarations — 8 declared, 2 imported by hash
  (0 alpha only), 1 folded (`solution`), 0 MISSING**. `main` is *declared*, not credited to the headline.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` on every public declaration; no `sorryAx`.
* `dedup.py --within`: **1 cluster, 21 lines** — `main` ↔ the headline, the pin's own engine↔headline pair
  (same statement, kept because the pin's declaration surface is the wire).
* `move_dead.py --dry-run`: **0 declarations, 0 lines**.
* Linters: nothing silenced module-wide; `linter.style.haveILetI` fires on the `haveI`/`letI` instance
  transports whose surrounding goal is a proposition, so it is silenced **declaration-scoped** with
  `set_option linter.style.haveILetI false in` on `exists_isPrimitiveRoot_algebraMap`,
  `exists_transcendental_of_finiteDimensional`, `transcendental_of_finrank_pos` and `main` only. No
  `maxHeartbeats` is installed.
* **The heartbeat probe** (recorded, never installed). Downward ladder, one run per value:

  | cap | 40000 | 20000 | 10000 | 5000 | 1000 |
  |---|---|---|---|---|---|
  | module | **pass** | fail | fail | fail | fail |
  | first failure | — | `whnf` in `main`'s statement (`:179`) | same | `whnf` in `finrank_adjoin_algebraMap_mul`'s statement (`:106`) | `whnf` in `exists_transcendental_of_finiteDimensional`'s statement (`:112`) |

  **Module floor** (every theorem proof `sorry`, one run): passes at **20000**, the first cap at which the
  real module fails — so the cost is in the proofs, not in the types. No cap is installed.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one.lean
-/
import FLTForHuman.AlgebraicCurve.Genus.GenusFFKrullDim
import FLTForHuman.AlgebraicCurve.Genus.SplittingFieldGenus
import FLTForHuman.AlgebraicCurve.RegularProlongation
import FLTForHuman.AlgebraicCurve.RegularProlongationKummer
import FLTForHuman.WeierstrassCurve.Place.RRSpace
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing Polynomial

namespace AlgebraicCurve
namespace RegularProlongation

/-! ## The residue and Kummer prelude

The pin's `W10C1` block, minus the two rows imported above. -/

set_option linter.style.haveILetI false in
theorem exists_isPrimitiveRoot_algebraMap {K E : Type*} [Field K] [IsAlgClosed K] [Field E]
    [Algebra K E] {q : ℕ} (hq : (q : K) ≠ 0) : ∃ ξ : E, IsPrimitiveRoot ξ q := by
  haveI : NeZero (q : K) := ⟨hq⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K q
  exact ⟨algebraMap K E ζ, hζ.map_of_injective (algebraMap K E).injective⟩

theorem exists_finset_roots {E : Type*} [Field E] {q : ℕ} {ξ : E}
    (hξ : IsPrimitiveRoot ξ q) {w : E} (hw : w ≠ 0) :
    ∃ S : Finset E, S.card = q ∧ ∀ s ∈ S, s ^ q = w ^ q := by
  classical
  refine ⟨(Finset.range q).image fun i => ξ ^ i * w, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hij' : ξ ^ i = ξ ^ j := mul_right_cancel₀ hw hij
    exact hξ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij'
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    rw [mul_pow, ← pow_mul, mul_comm i q, pow_mul, hξ.pow_eq_one, one_pow, one_mul]

set_option linter.style.haveILetI false in
theorem exists_transcendental_of_finiteDimensional {L F F' : Type*} [Field L] [Field F] [Field F']
    [Algebra L F] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F'] [FiniteDimensional F F']
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F) :
    ∃ y : F', Transcendental L y ∧
      FiniteDimensional (IntermediateField.adjoin L ({y} : Set F')) F' := by
  obtain ⟨x, hx, hfin⟩ := hF
  set φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F' with hφ
  refine ⟨φ x, (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx, ?_⟩
  set E : IntermediateField L F := IntermediateField.adjoin L ({x} : Set F) with hE
  set E' : IntermediateField L F' := IntermediateField.adjoin L ({φ x} : Set F') with hE'
  have hmap : E.map φ = E' := by
    rw [hE, IntermediateField.adjoin_map, Set.image_singleton]
  have hle : ∀ e : E, φ (e : F) ∈ E' := fun e => by
    rw [← hmap]
    exact ⟨e, e.2, rfl⟩
  let ψ : E →+* E' :=
    { toFun := fun e => ⟨φ e, hle e⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI : Algebra E E' := ψ.toAlgebra
  haveI : IsScalarTower E E' F' := IsScalarTower.of_algebraMap_eq (fun e => by
    rw [IsScalarTower.algebraMap_apply E F F' e]
    rfl)
  haveI : Module.Finite E F' := Module.Finite.trans F F'
  exact Module.Finite.of_restrictScalars_finite E E' F'

theorem finrank_adjoin_algebraMap_mul {L F F' : Type*} [Field L] [Field F] [Field F']
    [Algebra L F] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F'] (x : F) :
    Module.finrank (IntermediateField.adjoin L ({algebraMap F F' x} : Set F')) F' =
      Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F * Module.finrank F F' := by
  set φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F' with hφ
  set E : IntermediateField L F := IntermediateField.adjoin L ({x} : Set F) with hE
  set E' : IntermediateField L F' := IntermediateField.adjoin L ({algebraMap F F' x} : Set F')
    with hE'
  have hmap : E.map φ = E' := by
    rw [hE, IntermediateField.adjoin_map, Set.image_singleton]; rfl
  let e : E ≃ₐ[L] E' := (IntermediateField.equivMap E φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ y : E, ((e y : E') : F') = algebraMap F F' (y : F) := fun y => rfl
  have h1 : Module.finrank E F' = Module.finrank E' F' :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F')
      (RingHom.ext fun y => (he y).symm)
  rw [← h1, Module.finrank_mul_finrank]

theorem finiteDimensional_adjoin_algebraMap {L F F' : Type*} [Field L] [Field F] [Field F']
    [Algebra L F] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F'] [FiniteDimensional F F']
    (x : F) (h : 0 < Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F) :
    FiniteDimensional (IntermediateField.adjoin L ({algebraMap F F' x} : Set F')) F' := by
  apply Module.finite_of_finrank_pos
  rw [finrank_adjoin_algebraMap_mul]
  exact Nat.mul_pos h Module.finrank_pos

set_option linter.style.haveILetI false in
theorem transcendental_of_finrank_pos {L F : Type*} [Field L] [Field F] [Algebra L F]
    (hF : ∃ y : F, Transcendental L y ∧
      FiniteDimensional (IntermediateField.adjoin L ({y} : Set F)) F)
    (x : F) (h : 0 < Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F) :
    Transcendental L x := by
  intro hx
  obtain ⟨y, hy, -⟩ := hF
  haveI : FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F :=
    Module.finite_of_finrank_pos h
  haveI : FiniteDimensional L (IntermediateField.adjoin L ({x} : Set F)) :=
    IntermediateField.adjoin.finiteDimensional hx.isIntegral
  haveI : FiniteDimensional L F :=
    FiniteDimensional.trans L (IntermediateField.adjoin L ({x} : Set F)) F
  exact hy (Algebra.IsAlgebraic.isAlgebraic y)

namespace ResiduePower

set_option linter.style.haveILetI false in
/-- The pin's `W10C1.main`, the worker of the row.  It sits in the subject namespace
`ResiduePower` rather than at `AlgebraicCurve.RegularProlongation` because SET-AF110D's
`Genus/GenusFFKrullDim.lean` already declares `AlgebraicCurve.RegularProlongation.main` (the
`sum_genusFF_le` engine): a second `main` there would be a FR-0274 full-name collision. -/
theorem main {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (hreg : ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {q : ℕ} [hqp : Fact q.Prime] (hq : (q : IsLocalRing.ResidueField A) ≠ 0)
    (f : R.integers) (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F))
    (w : Fbar) (hw0 : w ≠ 0) (hw : w ^ q = R.residue f) :
    ∃ h : F, h ^ q = (f : F) := by
  classical
  have hq0 : q ≠ 0 := hqp.out.ne_zero
  have hqpos : 0 < q := hqp.out.pos
  by_contra hpow
  have hf' : ∀ h : F, h ^ q ≠ (f : F) := fun h hh => hpow ⟨h, hh⟩

  let F' := (X ^ q - C (f : F)).SplittingField

  obtain ⟨ξF, hξF⟩ := exists_isPrimitiveRoot_algebraMap (K := L) (E := F) (q := q)
    (Nat.cast_ne_zero.mpr hq0)
  have hζ : (primitiveRoots q F).Nonempty := ⟨ξF, (mem_primitiveRoots hqpos).mpr hξF⟩
  have hirr : Irreducible (X ^ q - C (f : F)) := X_pow_sub_C_irreducible_of_prime hqp.out hf'
  have hdeg : Module.finrank F F' = q := finrank_of_isSplittingField_X_pow_sub_C hζ hirr F'
  haveI : FiniteDimensional F F' :=
    Polynomial.IsSplittingField.finiteDimensional F' (X ^ q - C (f : F))

  have hRH := genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord hF hf' hdvd F'

  haveI : IsAlgClosed (ResidueField A) := ResidueIntegralClosure.isAlgClosed_residueField (A := A)
  obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_algebraMap (K := ResidueField A) (E := Fbar) hq
  obtain ⟨S, hS, hSw⟩ := exists_finset_roots hξ hw0
  have hSf : ∀ s ∈ S, s ^ q = R.residue f := fun s hs => by rw [hSw s hs, hw]
  obtain ⟨R', hinj, hR'⟩ :=
    exists_prolongation_of_card_roots_eq A R f S hS hSf F' hdeg

  obtain ⟨x, hxk, hpos, hfinrk⟩ := hreg
  have hposL : 0 < Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F := by
    rw [hfinrk]; exact hpos
  have hxL : Transcendental L (x : F) := transcendental_of_finrank_pos hF (x : F) hposL
  have hxO : ∀ i, algebraMap F F' (x : F) ∈ (R' i).integers := fun i => by
    rw [← ValuationSubring.mem_comap, (hR' i).1]; exact x.2
  have hres : ∀ i, (R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩ = R.residue x := fun i =>
    (hR' i).2 ⟨algebraMap F F' (x : F), hxO i⟩ x rfl
  have htrL : Transcendental L (algebraMap F F' (x : F)) :=
    (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hxL
  have hfd : FiniteDimensional
      (IntermediateField.adjoin L ({algebraMap F F' (x : F)} : Set F')) F' :=
    finiteDimensional_adjoin_algebraMap (x : F) hposL
  have htr : ∀ i, Transcendental (ResidueField A)
      ((R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩) := fun i => by
    rw [hres i]; exact hxk
  have hfi : ∀ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({R.residue x} : Set Fbar)) Fbar := fun i => by rw [hres i]
  have heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin L ({algebraMap F F' (x : F)} : Set F')) F' := by
    rw [Finset.sum_congr rfl fun i _ => hfi i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, finrank_adjoin_algebraMap_mul, hdeg, hfinrk, mul_comm]
  have hsum := sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one A (fun _ : Fin q => Fbar) R'
    hinj (algebraMap F F' (x : F)) hxO htrL hfd htr heq
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hgood] at hsum

  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hqp.out.two_le
  have hsum' : (q : ℤ) * (genusFF L F : ℤ) ≤ (genusFF L F' : ℤ) := by exact_mod_cast hsum
  nlinarith [hsum', hRH, h2, (Int.natCast_nonneg (genusFF L F))]

end ResiduePower

end RegularProlongation
end AlgebraicCurve

open AlgebraicCurve.RegularProlongation in
theorem AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (hreg : ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {q : ℕ} [Fact q.Prime] (hq : (q : IsLocalRing.ResidueField A) ≠ 0)
    (f : R.integers) (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F))
    (w : Fbar) (hw0 : w ≠ 0) (hw : w ^ q = R.residue f) :
    ∃ h : F, h ^ q = (f : F) :=
  RegularProlongation.ResiduePower.main A hF R hgood hreg hq f hdvd w hw0 hw
