/-
  A uniformiser at a place of a function field is a separating element.

  Let `K` be a perfect field and `F` a function field over `K` in the sense fixed
  here — `F` is algebraic over `K(x)` for some `x` — and let `v` be a place of `F`
  over `K`. If `t` has order one at `v` (a uniformiser), then `F` is separable over
  the simple adjoin `K(t)`; more generally, an element of nonzero *tame* order at `v`
  separates: `ord t ≠ 0` together with `natAbs (ord t)` nonzero in `K` suffices.
  These are the two headlines.

  The proof has a generic half and a place half. Generically
  (`Algebra/IsSeparableFrobenius.lean`) a finite extension of characteristic `p` is
  separable when the `p`-th-power Frobenius subfield has index `p` and the element is
  not a `p`-th power; the index `p` is the Frobenius-subfield degree of `M/K(t)`,
  which `IsCurveOver/FrobeniusSubfield.lean` computes for a transcendental simple
  adjoin and transports across a finite extension. At the place, `ord t = 1` rules
  out `t = a ^ p` for every `p ≥ 2` (taking orders would give `p * ord a = 1`), and
  `ord t ≠ 0` makes `t` transcendental (`Place.transcendental_of_ord_ne_zero`). The
  tame hypothesis of the second headline plays the same role: `p * ord a = ord t`
  is impossible when `natAbs (ord t)` is nonzero in characteristic `p`.

  **Twin heads, one body.** The pin writes this development twice, as
  `S_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one.lean` (455 lines) and
  `S_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero.lean`
  (460); the two files differ only in the `not_pow_*` helper and in one hypothesis
  of `solution`, so the port homes the body once
  (`separable_of_transcendental_of_forall_not_pow`) and derives both headlines, each
  supplying its own "no `p`-th power" lemma. `D_pow_eq_zero` and
  `isSeparable_of_not_pow_mem_range` are **not** ported: the latter is the same
  theorem as the port's `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`,
  which is called with `frobeniusSubfield` substituted by its definition.

  spec-pin: Theorems/Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one.lean
  spec-pin: Theorems/Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one.lean   -- comparable copy
  spec-pin: P2M/Sol/S_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero.lean   -- comparable copy
-/
import FLTForHuman.Algebra.IsSeparableFrobenius
import FLTForHuman.AlgebraicCurve.IsCurveOver.FrobeniusSubfield
import FLTForHuman.AlgebraicCurve.Place.DegreeOne
import FLTForHuman.AlgebraicCurve.Place.TranscendentalOfOrdNeZero
import Mathlib.FieldTheory.Perfect

set_option autoImplicit false

noncomputable section

open IntermediateField

open scoped IntermediateField

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open AlgebraicCurve.PthPowerIndex

/-! ### The place side: the order excludes `p`-th powers -/

private theorem not_pow_of_ord_eq_one (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1) {p : ℕ} (hp : 2 ≤ p) (a : F) : a ^ p ≠ t := by
  intro h
  have h2 : (p : ℤ) * v.ord a = 1 := by
    rw [← v.ord_zpow, zpow_natCast, h, ht]
  have := Int.eq_one_of_mul_eq_one_right (by positivity) h2
  omega

-- `hchar` is a *term* here (the caller is outside the characteristic split), and it must
-- become the instance that `CharP.cast_eq_zero` consumes: the one `haveI` of the module.
set_option linter.style.haveILetI false in
private theorem not_pow_of_cast_natAbs_ord_ne_zero (v : AlgebraicCurve.Place K F) {t : F} {p : ℕ}
    (hchar : CharP K p) (htame : (((v.ord t).natAbs : ℕ) : K) ≠ 0) (a : F) : a ^ p ≠ t := by
  haveI := hchar
  intro h
  have h2 : (p : ℤ) * v.ord a = v.ord t := by
    rw [← v.ord_zpow, zpow_natCast, h]
  apply htame
  rw [← h2, Int.natAbs_mul, Int.natAbs_natCast, Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul]

/-! ### The generic body: transcendental and never a `p`-th power ⟹ separable -/

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false in
private theorem separable_of_transcendental_of_forall_not_pow [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] {t : F}
    (htr : Transcendental K t)
    (htp : ∀ (p : ℕ), p.Prime → CharP K p → ∀ a : F, a ^ p ≠ t) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  haveI halg : Algebra.IsAlgebraic (↥K⟮t⟯) F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x htr
  obtain ⟨q, hq⟩ := ExpChar.exists K
  haveI := hq
  cases hq with
  | zero =>
    haveI : CharZero (↥K⟮t⟯) := charZero_of_injective_algebraMap (algebraMap K _).injective
    infer_instance
  | prime hqp =>
    haveI : Fact q.Prime := ⟨hqp⟩
    have hq' : ∀ a : F, a ^ q ≠ t := fun a ↦ htp q hqp inferInstance a
    haveI hEq : ExpChar (↥K⟮t⟯) q :=
      expChar_of_injective_algebraMap (algebraMap K _).injective q
    haveI hEqC : CharP (↥K⟮t⟯) q :=
      charP_of_injective_algebraMap (algebraMap K _).injective q
    have hEfr : Module.finrank (frobeniusSubfield (↥K⟮t⟯) q) (↥K⟮t⟯) = q :=
      finrank_frobeniusSubfield_adjoin_transcendental q htr
    haveI hEfd : FiniteDimensional (frobeniusSubfield (↥K⟮t⟯) q) (↥K⟮t⟯) :=
      .of_finrank_pos (by rw [hEfr]; exact hqp.pos)
    refine ⟨fun y ↦ ?_⟩
    haveI hMfd : FiniteDimensional (↥K⟮t⟯) (↥(↥K⟮t⟯)⟮y⟯) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    suffices hMsep : Algebra.IsSeparable (↥K⟮t⟯) (↥(↥K⟮t⟯)⟮y⟯) from
      isSeparable_of_mem_isSeparable _ F (mem_adjoin_simple_self (↥K⟮t⟯) y)
    haveI hMq : CharP (↥(↥K⟮t⟯)⟮y⟯) q :=
      charP_of_injective_algebraMap (algebraMap (↥K⟮t⟯) _).injective q
    have hMfr : Module.finrank (frobeniusSubfield (↥(↥K⟮t⟯)⟮y⟯) q) (↥(↥K⟮t⟯)⟮y⟯) = q := by
      rw [finrank_frobeniusSubfield_eq (E := ↥K⟮t⟯) q]
      exact hEfr
    refine Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq q hMfr
      ⟨t, mem_adjoin_simple_self K t⟩ ?_
    rintro ⟨b, hb⟩
    refine hq' b ?_
    have h := congrArg (fun z : ↥(↥K⟮t⟯)⟮y⟯ ↦ (z : F)) hb
    simpa [frobenius_def] using h

/-! ### The two headlines -/

theorem isSeparable_adjoin_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  exact separable_of_transcendental_of_forall_not_pow x
    (v.transcendental_of_ord_ne_zero ht0)
    (fun p hp _ a ↦ not_pow_of_ord_eq_one v ht hp.two_le a)

theorem isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t ≠ 0) (htame : (((v.ord t).natAbs : ℕ) : K) ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
  separable_of_transcendental_of_forall_not_pow x (v.transcendental_of_ord_ne_zero ht)
    (fun p _hp hchar a ↦ not_pow_of_cast_natAbs_ord_ne_zero (K := K) (p := p) v hchar htame a)

end Place

end AlgebraicCurve
