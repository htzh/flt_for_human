/-
  The cyclotomic conjugates of the `j`-series. Write `j = jqModC K`. For a prime `p`
  and a primitive `p`-th root of unity `ζ`, the `p` twists `qTwist (ζ ^ b) (j(q))`
  (`b < p`) are the conjugates of `j(q)` over `K(j(q))`: they are the `p` distinct
  roots of any `P` with `P(j(q)) = j(q^p)`, and their sum is `-P`'s `q ^ (p-1)`
  coefficient, the trace. Reading the `q ^ (-p m)` coefficient of that trace in
  characteristic `p` refutes the equation — `j(q^p)` is not a polynomial in `j(q)`.

  The module is the conjugates' structure, not a lemma shelf: the pole of `j` and of
  `P(j(q))` at the cusp, the degree and monicity the conjugates force on `P`, the
  `qTwist` action that carries one solution to all `p` of them, the modular relation
  `Φ_p(j(q), j(q^p)) = 0` at a general coefficient ring, and the trace identity with
  its coefficient obstruction.

  ## What the block is

  Five layers, in dependency order:

  * **the pole at the cusp** — `aeval (jqModC K) P` has no coefficients below
    `-natDegree P` and its leading one is `P`'s (`coeff_algebraMap_mul`,
    `coeff_aeval_jqModC_of_lt`, `coeff_aeval_jqModC_neg_natDegree`);
  * **forcing** — a `P` with `aeval (jqModC K) P = jqNModC K p` is nonzero, has
    degree `p` and is monic, because `jqNModC K p` has leading coefficient `1`
    at `q ^ (-p)` and none below it (`coeff_jqNModC_self`,
    `coeff_jqNModC_of_lt`, `ne_zero_of_aeval_eq`, `natDegree_eq_of_aeval_eq`,
    `monic_of_aeval_eq`, `jqNModC_congr`);
  * **transfer** — `qTwist` fixes the constants and sends a solution to the
    equation to the `p` conjugate solutions at `qTwist (ζ ^ b) (jqModC K)`
    (`units_pow_eq_one_of_isPrimitiveRoot`, `qTwist_algebraMap`,
    `qTwist_comp_algebraMap`, `aeval_qTwist_jqModC_eq_of_aeval_eq`,
    `qTwist_pow_jqModC_injective`);
  * **the modular relation at a general coefficient ring** — the modular
    polynomial relation `Φ_p` for `jqNModC`, at `j(q ^ d)` and after
    `qExpand` (`phiAtSeed_jqNModC_eval`, `phiAtSeed_jqNModC_eval_symm`,
    `phiAtSeed_TS_eval`, `phiAtSeed_TS_eval_symm`);
  * **the conjugate sum and its coefficient** — Vieta over the `p` distinct
    twists gives `Σ_b qTwist (ζ ^ b) (jqModC K) = -P.coeff (p - 1)` as a
    constant, whose `q ^ (-p m)` coefficient is `-P.coeff (p-1)` on one side and
    `p · (jqModC K).coeff (-p m)` on the other; over a field of characteristic
    `p` that is a contradiction (`sum_qTwist_jqModC_eq_of_aeval_eq`,
    `coeff_sum_qTwist_jqModC`, `coeffMap_algebraMap'`,
    `coeffMap_aeval_jqModC`, `aeval_jqModC_ne_jqNModC_of_isPrimitiveRoot`,
    `aeval_jqModC_ne_jqNModC`).

  ## One home for a block the pin writes twice

  The pin's `P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean`
  and `…_of_forall_aeval_ne.lean` are 593 lines each and **574 byte-identical**;
  every statement below appears in both, byte for byte, under the pin's local
  `namespace W1`. The block is written **once** here, at the pin's names and
  binders, so the two façades (`Degree/PrimeNonAdjoin.lean`) and
  `ModularPolynomialStarBank.lean` import it instead of re-deriving it.

  ## Reuse

  `Defs/JqCoeff.lean`'s `jqModC`/`jqNModC`/`jqNModC_one` and the pole trio
  (`jqModC_pow`, `coeff_jqModC_pow_self`, `coeff_jqModC_pow_of_lt`,
  `coeff_jqModC_neg_one`, `order_jqModC`); `Defs/Laurent.lean`'s `qExpand`,
  `qExpand_coeff_mul`, `qExpand_coeff_of_not_dvd`, `qExpand_qExpand`,
  `algebraMap_laurentSeries_eq_single`, `coeffMap`, `coeffMap_coeff`,
  `coeffMap_single`, `coeffMap_qExpand`, `coeffEmb`; `Defs/Twist.lean`'s
  `qTwist`, `qTwist_coeff`, `qTwist_single`, `qTwist_one_apply`,
  `qTwist_qExpand`; `Defs/KatzLevelPCusps.lean`'s
  `qTwist_qExpand_of_pow_eq_one`; `Defs/PhiAtSlot.lean`'s `phiAtSeed`,
  `phiAtSeed_monic`, `phiAtSeed_eval_map`; `Defs/PhiGen.lean`'s `EvalSymm`;
  `Degree/PhiData.lean`'s `ModularPolynomialData.eval_jqNModC_mul_eq_zero` /
  `eval_jqNModC_of_mul_eq_zero`. The pin's `TS` series (`TS`, `TS_coeff_*`,
  `TS_injective`, `qExpand_TS`, `qTwist_TS`, `TS_congr`, `jqModC_eq_TS`,
  `jqNModC_eq_TS`, `qExpand_jqNModC`, `qExpand_jqModC_eq_TS`,
  `qTwist_qExpand_of_pow_eq_one`) and its `qTwistEquiv`/`coeffMap_TS`
  transport block are public in `Defs/TS.lean`, `Defs/Twist.lean` and
  `Defs/KatzLevelPCusps.lean` and are **not** restated.

  ## Drift from the pin

  `coeff_jqNModC_self`, `coeff_jqNModC_of_lt` and
  `qTwist_pow_jqModC_injective` are proved through `qExpand`'s coefficient API
  rather than through `TS`, as they were landed. That was forced when the port's
  `TS` was `qExpand K e (qTwist u (coeffEmb K jq))` and carried an `[Algebra ℚ K]`
  binder the pin's per-file `TS` does not; since 2026-10-25 `Defs/TS.lean` states
  `TS K e u = qExpand K e (qTwist u (jqModC K))` over `[Field K]`, so the `TS` route
  is now available and these proofs may take it on the next touch — they are not
  re-proved now, because nothing about their statements changes.

  The two `phiAtSeed_TS_eval*` statements *did* change: they are now at the pin's
  general `[Field K]` binders and pinned against the char-`p` source (the two
  `own:` rows they used are gone).

  ## Residue (recorded, not open)

  `jqNModC_congr` and `coeff_algebraMap_mul` gain their public home here; the
  `private` copies in `Degree/PhiData.lean`, `Degree/Roof.lean` and
  `Defs/QExpValuationReduction.lean` remain, because those are frozen-registry
  modules and replacing their copies is a separate pass.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean#L267-L503
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean#L267-L503

  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean
  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean
  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.Defs.KatzLevelPCusps
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Degree.PhiData
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Algebraic.Basic

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries Finset

namespace ModularCurve

/-! ## The pole at the cusp, seen through `aeval`

`aeval (jqModC K) P` is a finite `K`-linear combination of powers of `j`, each
of which has its own pole of order `-b`. The three lemmas below read the
coefficient at `-natDegree P` (the polynomial's own leading coefficient) and
the vanishing below it. -/

section PoleOrder

variable {K : Type*} [Field K]

/-- Multiplication by a constant is the `q ^ 0` single-term product. -/
theorem coeff_algebraMap_mul (c : K) (x : LaurentSeries K) (k : ℤ) :
    (algebraMap K (LaurentSeries K) c * x).coeff k = c * x.coeff k := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

/-- `aeval (jqModC K) P` has no coefficients below `-natDegree P`. -/
theorem coeff_aeval_jqModC_of_lt (P : Polynomial K) {m : ℤ}
    (hm : m < -(P.natDegree : ℤ)) :
    (Polynomial.aeval (jqModC K) P).coeff m = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_algebraMap_mul, coeff_jqModC_pow_of_lt K (b := i) (m := m) (by omega),
    mul_zero]

/-- The leading coefficient of `aeval (jqModC K) P` is `P`'s. -/
theorem coeff_aeval_jqModC_neg_natDegree (P : Polynomial K) :
    (Polynomial.aeval (jqModC K) P).coeff (-(P.natDegree : ℤ)) = P.coeff P.natDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single P.natDegree]
  · rw [coeff_algebraMap_mul, coeff_jqModC_pow_self K P.natDegree, mul_one]
  · intro i hi hin
    have hilt : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    rw [coeff_algebraMap_mul,
      coeff_jqModC_pow_of_lt K (b := i) (m := -(P.natDegree : ℤ)) (by omega),
      mul_zero]
  · intro hn
    exact absurd (Finset.self_mem_range_succ P.natDegree) hn

end PoleOrder

section IndexCongr

variable {K : Type*} [Field K]

/-- `jqNModC` is natural in its index: the `q`-substitution index is a
congruence, not a structure. -/
theorem jqNModC_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    jqNModC K n = jqNModC K m := by
  subst h; rfl

end IndexCongr

/-! ## Forcing: degree and monicity of a solution

`jqNModC K p = aeval (jqModC K) P` has leading coefficient `1` at `q ^ (-p)`
and vanishes below it, so `P` must be nonzero, of degree `p`, and monic. -/

section Forcing

variable {K : Type*} [Field K]

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The `q ^ (-p)` coefficient of `jqNModC K p` is `1`. -/
theorem coeff_jqNModC_self : (jqNModC K p).coeff (-(p : ℤ)) = 1 := by
  have h : ((p : ℤ) * (-1) : ℤ) = -(p : ℤ) := by ring
  rw [jqNModC, ← h, qExpand_coeff_mul, coeff_jqModC_neg_one]

/-- `jqNModC K p` has no coefficients below `q ^ (-p)`. -/
theorem coeff_jqNModC_of_lt {m : ℤ} (hm : m < -(p : ℤ)) : (jqNModC K p).coeff m = 0 := by
  by_cases hd : (p : ℤ) ∣ m
  · obtain ⟨n, rfl⟩ := hd
    rw [jqNModC, qExpand_coeff_mul]
    have hn : n < -1 := by
      have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.out.pos
      nlinarith
    have h := coeff_jqModC_pow_of_lt K (b := 1) (m := n) (by simpa using hn)
    simpa using h
  · exact qExpand_coeff_of_not_dvd (R := K) (N := p) _ hd

variable {p} {P : Polynomial K}

/-- A polynomial whose `aeval` at `jqModC K` is `jqNModC K p` is nonzero. -/
theorem ne_zero_of_aeval_eq (h : Polynomial.aeval (jqModC K) P = jqNModC K p) : P ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  have h1 := coeff_jqNModC_self (K := K) p
  rw [← h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

/-- Such a polynomial has degree exactly `p`. -/
theorem natDegree_eq_of_aeval_eq (h : Polynomial.aeval (jqModC K) P = jqNModC K p) :
    P.natDegree = p := by
  have hP0 : P ≠ 0 := ne_zero_of_aeval_eq h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (Polynomial.aeval (jqModC K) P).coeff (-(p : ℤ)) = 0 :=
      coeff_aeval_jqModC_of_lt P (by omega)
    rw [h, coeff_jqNModC_self] at h1
    exact one_ne_zero h1
  · have h1 := coeff_aeval_jqModC_neg_natDegree P
    rw [h, coeff_jqNModC_of_lt p (m := -(P.natDegree : ℤ)) (by omega)] at h1
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp h1.symm)

/-- Such a polynomial is monic. -/
theorem monic_of_aeval_eq (h : Polynomial.aeval (jqModC K) P = jqNModC K p) : P.Monic := by
  have hd := natDegree_eq_of_aeval_eq h
  have h1 := coeff_aeval_jqModC_neg_natDegree P
  rw [h, hd, coeff_jqNModC_self] at h1
  show P.coeff P.natDegree = 1
  rw [hd]; exact h1.symm

end Forcing

/-! ## Transfer along the cyclotomic twist

`qTwist v` is a ring endomorphism fixing the constants, and it commutes with
`qExpand` when `v ^ p = 1`; hence it carries a solution of the equation to the
`p` conjugate solutions. -/

section Transfer

variable {K : Type*} [Field K]

/-- A unit of `K` that is a primitive `N`-th root has `ζ ^ N = 1`. -/
theorem units_pow_eq_one_of_isPrimitiveRoot {N : ℕ} {ζ : Kˣ}
    (hζ : IsPrimitiveRoot (ζ : K) N) : ζ ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one])

/-- `qTwist` fixes the constants. -/
theorem qTwist_algebraMap (v : Kˣ) (c : K) :
    qTwist v (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c := by
  rw [algebraMap_laurentSeries_eq_single, qTwist_single, zpow_zero, Units.val_one, one_mul]

/-- The ring-hom form of `qTwist_algebraMap`. -/
theorem qTwist_comp_algebraMap (v : Kˣ) :
    (qTwist v).comp (algebraMap K (LaurentSeries K)) = algebraMap K (LaurentSeries K) :=
  RingHom.ext fun c => qTwist_algebraMap v c

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {ζ : Kˣ} {P : Polynomial K}

/-- The `b`-th twist of `jqModC K` is again a root of `P`. -/
theorem aeval_qTwist_jqModC_eq_of_aeval_eq (hζ : IsPrimitiveRoot (ζ : K) p)
    (h : Polynomial.aeval (jqModC K) P = jqNModC K p) (b : ℕ) :
    Polynomial.aeval (qTwist (ζ ^ b) (jqModC K)) P = jqNModC K p := by
  have hζp : ζ ^ p = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hvb : (ζ ^ b) ^ p = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hζp, one_pow]
  have h2 := congrArg (qTwist (ζ ^ b)) h
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, qTwist_comp_algebraMap, jqNModC,
    qTwist_qExpand_of_pow_eq_one p (ζ ^ b) hvb (jqModC K)] at h2
  rw [Polynomial.aeval_def]
  exact h2

omit hp in
/-- The `p` twists are distinct, by their `q ^ (-1)` coefficients. -/
theorem qTwist_pow_jqModC_injective (hζ : IsPrimitiveRoot (ζ : K) p) :
    Function.Injective (fun b : Fin p => qTwist (ζ ^ (b : ℕ)) (jqModC K)) := by
  intro b b' h
  have hcoeff : ∀ v : Kˣ, (qTwist v (jqModC K)).coeff (-1 : ℤ) = ((v⁻¹ : Kˣ) : K) := by
    intro v
    rw [qTwist_coeff, coeff_jqModC_neg_one, mul_one, zpow_neg_one]
  have h1 := congrArg (fun x => x.coeff (-1 : ℤ)) h
  simp only [hcoeff] at h1
  have h2 : ζ ^ (b : ℕ) = ζ ^ (b' : ℕ) := inv_injective (Units.val_injective h1)
  have h3 : ((ζ : Kˣ) : K) ^ (b : ℕ) = ((ζ : Kˣ) : K) ^ (b' : ℕ) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2]
  exact Fin.ext (hζ.pow_inj b.isLt b'.isLt h3)

end Transfer

/-! ## The modular relation for `jqNModC`

`Φ_p` evaluated at the seed `j(q ^ d)` vanishes at `j(q ^ (d n))` and, when `Φ`
is symmetric, at the mirror pair; `qExpand` carries both to the dilated slot. -/

section PhiAtSeedJqNModC

/-- `phiAtSeed` vanishes at `(jqNModC R d, jqNModC R (d * n))`. -/
theorem phiAtSeed_jqNModC_eval {R : Type*} [CommRing R] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n) (d : ℕ) [NeZero d] :
    (phiAtSeed data (jqNModC R d)).eval (jqNModC R (d * n)) = 0 := by
  have hhom : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries R)) (jqNModC R d)
      = (Polynomial.aeval (R := ℤ) (jqNModC R d)).toRingHom :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  rw [phiAtSeed, hhom, Polynomial.eval_map]
  exact data.eval_jqNModC_mul_eq_zero R d

/-- The symmetric direction: `phiAtSeed` vanishes at `(jqNModC R (d * n), jqNModC R d)`. -/
theorem phiAtSeed_jqNModC_eval_symm {R : Type*} [CommRing R] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n) (hsymm : EvalSymm data.Φ) (d : ℕ) [NeZero d] :
    (phiAtSeed data (jqNModC R (d * n))).eval (jqNModC R d) = 0 := by
  have hhom : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries R)) (jqNModC R (d * n))
      = (Polynomial.aeval (R := ℤ) (jqNModC R (d * n))).toRingHom :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  rw [phiAtSeed, hhom, Polynomial.eval_map]
  exact data.eval_jqNModC_of_mul_eq_zero hsymm R d

end PhiAtSeedJqNModC

/-! ## The modular relation at a dilated slot

These two statements mention `TS` itself and carry the `[Algebra ℚ K]` binder of
the port's `TS` (`Defs/TS.lean`); they are recorded as `own:` rows in
`spec/decl_markers.tsv`, the pin stating them over an arbitrary field. -/

section PhiAtSeedTS

/-- `phiAtSeed` vanishes at the `A`-dilated slot `(j(q^d), j(q^(d n)))`. -/
theorem phiAtSeed_TS_eval {K : Type*} [Field K] (A : ℕ) [NeZero A]
    (n : ℕ) [NeZero n] (data : ModularPolynomialData n) (d : ℕ) [NeZero d] :
    (phiAtSeed data (TS K (A * d) 1)).eval (TS K (A * (d * n)) 1) = 0 := by
  have h1 : TS K (A * d) 1 = qExpand K A (jqNModC K d) := by
    rw [TS, qTwist_one_apply, jqNModC, qExpand_qExpand]
  have h2 : TS K (A * (d * n)) 1 = qExpand K A (jqNModC K (d * n)) := by
    rw [TS, qTwist_one_apply, jqNModC, qExpand_qExpand]
  rw [h1, h2]
  exact phiAtSeed_eval_map data _ _ (qExpand K A) (phiAtSeed_jqNModC_eval (R := K) n data d)

/-- The symmetric direction at the dilated slot. -/
theorem phiAtSeed_TS_eval_symm {K : Type*} [Field K] (A : ℕ) [NeZero A]
    (n : ℕ) [NeZero n] (data : ModularPolynomialData n) (hsymm : EvalSymm data.Φ)
    (d : ℕ) [NeZero d] :
    (phiAtSeed data (TS K (A * (d * n)) 1)).eval (TS K (A * d) 1) = 0 := by
  have h1 : TS K (A * (d * n)) 1 = qExpand K A (jqNModC K (d * n)) := by
    rw [TS, qTwist_one_apply, jqNModC, qExpand_qExpand]
  have h2 : TS K (A * d) 1 = qExpand K A (jqNModC K d) := by
    rw [TS, qTwist_one_apply, jqNModC, qExpand_qExpand]
  rw [h1, h2]
  exact phiAtSeed_eval_map data _ _ (qExpand K A)
    (phiAtSeed_jqNModC_eval_symm (R := K) n data hsymm d)

end PhiAtSeedTS

/-! ## Vieta over the `p` conjugate twists

The two monic polynomials `A = P.map (algebraMap K _)` and
`B = ∏_b (X - qTwist (ζ^b) (jqModC K))` have degree `p` and agree at `p`
distinct arguments, so `A - B` is the constant `jqNModC K p`; reading the
`q^(p-1)` coefficient gives the conjugate sum. -/

section Vieta

variable {K : Type*} [Field K]

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {ζ : Kˣ} {P : Polynomial K}

/-- `Σ_b qTwist (ζ ^ b) (jqModC K) = -P.coeff (p - 1)`, as a constant. -/
theorem sum_qTwist_jqModC_eq_of_aeval_eq (hζ : IsPrimitiveRoot (ζ : K) p)
    (h : Polynomial.aeval (jqModC K) P = jqNModC K p) :
    ∑ b : Fin p, qTwist (ζ ^ (b : ℕ)) (jqModC K) = algebraMap K (LaurentSeries K) (-P.coeff (p - 1)) := by
  have hPdeg : P.natDegree = p := natDegree_eq_of_aeval_eq h
  have hPmonic : P.Monic := monic_of_aeval_eq h
  set A : Polynomial (LaurentSeries K) := P.map (algebraMap K (LaurentSeries K)) with hA
  set B : Polynomial (LaurentSeries K) :=
    ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K))) with hB
  have hAmonic : A.Monic := hPmonic.map _
  have hAdeg : A.natDegree = p := by rw [hA, hPmonic.natDegree_map, hPdeg]
  have hBmonic : B.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hBdeg : B.natDegree = p := by
    rw [hB, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have key : A - B = Polynomial.C (jqNModC K p) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (qTwist_pow_jqModC_injective hζ) (fun b => ?_) ?_
    · have hAev : A.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = jqNModC K p := by
        rw [hA, Polynomial.eval_map_algebraMap]
        exact aeval_qTwist_jqModC_eq_of_aeval_eq hζ h b
      have hBev : B.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = 0 := by
        rw [hB, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_C, hAev, hBev, sub_zero]
    · rw [Fintype.card_fin]
      refine max_lt ?_ (by rw [Polynomial.natDegree_C]; exact hp.out.pos)
      by_cases hAB : A = B
      · rw [hAB, sub_self, Polynomial.natDegree_zero]
        exact hp.out.pos
      · refine lt_of_lt_of_eq (Polynomial.natDegree_lt_natDegree (sub_ne_zero.mpr hAB) ?_) hAdeg
        exact Polynomial.degree_sub_lt_left
          (by rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero, Polynomial.degree_eq_natDegree hBmonic.ne_zero,
            hAdeg, hBdeg])
          hAmonic.ne_zero (by rw [hAmonic.leadingCoeff, hBmonic.leadingCoeff])
  have hcoeff := congrArg (fun Q : Polynomial (LaurentSeries K) => Q.coeff (p - 1)) key
  have hp2 : 2 ≤ p := hp.out.two_le
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_right (by omega : ¬(p - 1 = 0))] at hcoeff
  have hBcoeff : B.coeff (p - 1) = -∑ b : Fin p, qTwist (ζ ^ (b : ℕ)) (jqModC K) := by
    have hv := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin p))
      (fun b => qTwist (ζ ^ (b : ℕ)) (jqModC K)) (by simp [hp.out.pos])
    simpa using hv
  have hAcoeff : A.coeff (p - 1) = algebraMap K (LaurentSeries K) (P.coeff (p - 1)) := Polynomial.coeff_map _ _
  rw [hAcoeff, hBcoeff, sub_neg_eq_add, add_comm] at hcoeff
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left hcoeff

end Vieta

/-! ## The coefficient obstruction

The conjugate sum is a constant, so its `q ^ (-p m)` coefficient is that
constant's; but each summand contributes the same `(jqModC K).coeff (-p m)`, `p`
times. Over characteristic `p` the two readings cannot both hold when the
coefficient is nonzero. -/

section Collapse

variable {K : Type*} [Field K]

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {ζ : Kˣ}

omit hp in
/-- The `q ^ (-p m)` coefficient of the conjugate sum is `p` times the
coefficient of `jqModC K`. -/
theorem coeff_sum_qTwist_jqModC (hζ : IsPrimitiveRoot (ζ : K) p) (m : ℕ) :
    (∑ b : Fin p, qTwist (ζ ^ (b : ℕ)) (jqModC K)).coeff ((p * m : ℕ) : ℤ)
      = (p : K) * (jqModC K).coeff ((p * m : ℕ) : ℤ) := by
  have hζp : ζ ^ p = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  rw [HahnSeries.coeff_sum]
  have hterm : ∀ b : Fin p,
      (qTwist (ζ ^ (b : ℕ)) (jqModC K)).coeff ((p * m : ℕ) : ℤ) = (jqModC K).coeff ((p * m : ℕ) : ℤ) := by
    intro b
    rw [qTwist_coeff, zpow_natCast, ← pow_mul, Nat.mul_comm (b : ℕ), Nat.mul_assoc, pow_mul, hζp, one_pow,
      Units.val_one, one_mul]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A primitive root in the field refutes the equation when `p ≠ 0` in `K` and
some `q ^ (-p m)` coefficient of `jqModC K` is nonzero. -/
theorem aeval_jqModC_ne_jqNModC_of_isPrimitiveRoot (hpK : (p : K) ≠ 0) (hζ : IsPrimitiveRoot (ζ : K) p) {m : ℕ}
    (hm : 0 < m) (hw : (jqModC K).coeff ((p * m : ℕ) : ℤ) ≠ 0) (P : Polynomial K) :
    Polynomial.aeval (jqModC K) P ≠ jqNModC K p := by
  intro h
  have h1 := sum_qTwist_jqModC_eq_of_aeval_eq hζ h
  have h2 := coeff_sum_qTwist_jqModC hζ m
  have hne : ((p * m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hp.out.ne_zero hm.ne'
  rw [h1, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne hne] at h2
  exact mul_ne_zero hpK hw h2.symm

end Collapse

/-! ## Ascent to the algebraic closure

`coeffMap` is natural for `aeval` at `jqModC`, so a primitive `p`-th root taken
in an algebraic closure supplies the hypothesis above. -/

section Ascent

variable {K : Type*} [Field K]

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- `coeffMap` sends the constant `c` to the constant `σ c`. -/
private theorem coeffMap_algebraMap' {K' : Type*} [Field K'] (σ : K →+* K') (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

/-- `coeffMap` is natural for `aeval` at `jqModC`. -/
theorem coeffMap_aeval_jqModC {K' : Type*} [Field K'] (σ : K →+* K') (P : Polynomial K) :
    coeffMap σ (Polynomial.aeval (jqModC K) P) = Polynomial.aeval (jqModC K') (P.map σ) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  have hcomp : (coeffMap σ).comp (algebraMap K (LaurentSeries K)) = (algebraMap K' (LaurentSeries K')).comp σ :=
    RingHom.ext fun c => coeffMap_algebraMap' σ c
  rw [hcomp]
  congr 1
  exact map_jqModC σ

/-- The equation has no solution over a field of characteristic `p`: pass to the
algebraic closure, take a primitive `p`-th root there, and apply the coefficient
obstruction. -/
theorem aeval_jqModC_ne_jqNModC (hpK : (p : K) ≠ 0) {m : ℕ} (hm : 0 < m) (hw : (jqModC K).coeff ((p * m : ℕ) : ℤ) ≠ 0)
    (P : Polynomial K) : Polynomial.aeval (jqModC K) P ≠ jqNModC K p := by
  intro h
  have : NeZero ((p : ℕ) : K) := ⟨hpK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  set σ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hσ
  have hzu : IsUnit z := hz.isUnit hp.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) p := by
    rw [IsUnit.unit_spec]
    exact hz
  have hpK' : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast σ]
    exact (map_ne_zero σ).mpr hpK
  have hw' : (jqModC (AlgebraicClosure K)).coeff ((p * m : ℕ) : ℤ) ≠ 0 := by
    rw [← map_jqModC σ]
    exact (map_ne_zero σ).mpr hw
  have h' : Polynomial.aeval (jqModC (AlgebraicClosure K)) (P.map σ) = jqNModC (AlgebraicClosure K) p := by
    rw [← coeffMap_aeval_jqModC, h, jqNModC, jqNModC, ModularCurve.coeffMap_qExpand]
    congr 1
    exact map_jqModC σ
  exact aeval_jqModC_ne_jqNModC_of_isPrimitiveRoot hpK' hζ hm hw' (P.map σ) h'

end Ascent

end ModularCurve

end
