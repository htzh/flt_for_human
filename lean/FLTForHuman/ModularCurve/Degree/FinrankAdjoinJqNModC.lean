/-
  Layer CL4-P2 — the transport that descends the socket's degree formula to the
  base field, and the two degree headlines that consume it.

  `ModularCurve.package_of_socket` (`FunctionFieldGeneration/PrimeStepAnyField.lean`)
  wants a primitive `d`-th root of unity, which an arbitrary field `K` need not
  contain. The pin therefore proves the degree statement over `AlgebraicClosure K`
  — where `ζ` exists and the socket applies — and descends along
  `algebraMap K (AlgebraicClosure K)`. The descent is the whole content of this
  module: `finrank_adjoin_jqNModC_eq_of_map σ` takes the statement over `K'` to
  the statement over `K`.

  Two headlines:

  * `finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket` — `[K⟮j(q)⟯⟮j(q ^ d)⟯ :
    K⟮j(q)⟯] = ψ(d)`, given that no prime `p ∣ d` already has `j(q ^ p)` in the
    base field `K⟮j(q)⟯`.
  * `finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero` — the same, with the
    base non-membership discharged by `CharZero K` (`j(q ^ p)` is transcendental
    over `K⟮j(q)⟯` there), so the statement carries no hypothesis beyond
    `[CharZero K]`.

  ## Why the descent is downward only

  `finrank_adjoin_jqNModC_eq_of_map σ` needs a map `K →+* K'`; for `[CharZero K]`
  there is none into `ℚ` (`ℚ` has no `K`-algebra structure unless `K = ℚ`), and
  the proof genuinely needs a bigger field: the socket's `hall` requires a
  primitive `d`-th root of unity `ζ`, which `K` need not have. So the ported
  ℚ-twin (`ModularPolynomialUniqueness.lean`, `finrank_adjoin_jqN_eq_of_prime`)
  cannot be pushed up to an arbitrary `[Field K]`; the socket is the only route,
  and this is the layer that pays for it. (Recorded in the topic's §10.3.)

  ## How the descent works

  Work over `K' = AlgebraicClosure K`, where `hall` holds and `data :
  ModularPolynomialData d` is irreducible at the seed. The polynomial
  `phiAtSeed data (jA K)` over `K⟮j(q)⟯` is the `minpoly` of `j(q ^ d)` over
  `K'⟮j(q)⟯`; mapping it along `tauAdjoin σ : K⟮j(q)⟯ →+* K'⟮j(q)⟯` gives the
  `K'`-polynomial, which is irreducible, so the `K`-polynomial is irreducible too
  (`Polynomial.Monic.irreducible_of_irreducible_map`); being monic and
  annihilating `j(q ^ d)`, it *is* the `K`-side `minpoly`, whose degree is
  `phiAtSeed_natDegree = ψ(d)`.

  ## Layering

  Imported, not restated:

  * `jqModC`, `jqNModC`, `modularFunctionFieldC`, `map_jqModC`,
    `coeffMap_qExpand`, `coeffMap_injective`, `algebraMap_laurentSeries_eq_single`
    — `Defs/JqCoeff.lean`, `Defs/Laurent.lean`;
  * `coeff_jqModC_pow_self`, `coeff_jqModC_pow_of_lt` — `Defs/JqCoeff.lean`;
  * `phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic`, `phiAtSeed_natDegree`,
    `phiAtSeed_jqNModC_eval` — `Defs/PhiAtSlot.lean`, `Degree/JqCyclotomicConjugates.lean`;
  * the pole-order block (`coeff_algebraMap_mul`, `coeff_aeval_jqModC_neg_natDegree`) —
    already public in `Degree/JqCyclotomicConjugates.lean`, not restated;
  * `isIntegral_jqNModC_of_modularPolynomialData` — `X1/IntegralityJqNModC.lean`;
  * `jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne`,
    `jqNModC_prime_not_mem_adjoin_of_charZero` — `Degree/PrimeNonAdjoin.lean`;
  * `package_of_socket` — `FunctionFieldGeneration/PrimePowerStepAnyField.lean`;
  * `exists_phiIrreducible` — `FunctionFieldGeneration/Capstone.lean` (the pin's
    `Theorems/Thm_ModularCurve_exists_phiIrreducible`; the port homes it in the
    non-`C` capstone, which is upstream of this layer);
  * `qExpand_jqModC_eq_pow_unconditional` — `Defs/QExpandCharP.lean`.

  `coeffMap_jqModC_eq` is the port's `map_jqModC` read through `coeffMap`; it is
  not re-proved.

  ## Statement provenance

  Both headlines are the `Theorems/` wrappers' binder blocks verbatim, and the
  pin also states them (as `private` copies) in both `S_` files, which differ by
  32 lines of namespace plumbing only — so they are ported once, here, and the
  two wrappers are wired to this one module. `jA` and the transport lemmas are the
  `S_` file's own public text.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket.lean`
  (518 lines; the transport is 277–518) and its byte-level twin
  `P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero.lean`.
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket.lean#L277-L518>

  spec-pin: P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket.lean
  spec-pin: Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero.lean
  spec-pin: Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero.lean
-/
import FLTForHuman.ModularCurve.Defs.QExpandCharP
import FLTForHuman.ModularCurve.Degree.PrimeNonAdjoin
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.FunctionFieldGeneration.PrimePowerStepAnyField
import FLTForHuman.ModularCurve.X1.IntegralityJqNModC
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false
-- The pin installs the `Fact (Nat.Prime (ringChar K))` and `NeZero ((d : ℕ) : K)`
-- instances of the two headlines with `haveI`; both are consumed by typeclass
-- search (`CharP.char_prime_of_ne_zero`, `HasEnoughRootsOfUnity`), so the style
-- linter's `have` preference does not apply. Same local disable as
-- `PrimePowerStepAnyField.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type*} [Field K]

/-- The generator `j(q)` read in the base field `K⟮j(q)⟯`: the pin's `jA`, the
seed every `phiAtSeed` in this layer is evaluated at. -/
def jA (F : Type*) [Field F] : IntermediateField.adjoin F ({jqModC F} : Set (LaurentSeries F)) :=
  ⟨jqModC F, IntermediateField.subset_adjoin F _ rfl⟩

/-- `Φ_d` at the seed `j(q)` annihilates `j(q ^ d)` — the modular relation in the
one-variable form the descent transports. Verbatim from
`S_…_of_socket.lean:281`. -/
theorem aeval_jqNModC_phiAtSeed_jA (F : Type*) [Field F] (d : ℕ) [NeZero d]
    (data : ModularPolynomialData d) :
    Polynomial.aeval (jqNModC F d) (phiAtSeed data (jA F)) = 0 := by
  rw [← Polynomial.eval_map_algebraMap, phiAtSeed_map]
  have h := phiAtSeed_jqNModC_eval (R := F) d data 1
  simpa [jA] using h

/-! ## The transport

`coeffMap σ : LaurentSeries K →+* LaurentSeries K'` carries the whole
`K⟮j(q)⟯`-side statement to the `K'` side: it fixes `j(q)`, hence `j(q ^ n)`,
hence every polynomial in `j(q)`, and it maps the base field into the base field
(`coeffMap_mem_adjoin`). `exists_map_eq_of_aeval_eq_coeffMap` is the converse
direction the non-membership lemma needs: a `K'`-polynomial that is a
`coeffMap`-image has a `K`-preimage, by induction on the degree, using the
leading-coefficient identity above. -/

section Transport

variable {K' : Type*} [Field K'] (σ : K →+* K')

/-- `coeffMap σ` fixes the constants. -/
theorem coeffMap_algebraMap_eq (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

/-- `coeffMap σ` fixes `j(q)`. The pin states this as its own `coeffMap_jqModC_eq`;
it is the port's `map_jqModC` read through `coeffMap`. -/
theorem coeffMap_jqModC_eq : coeffMap σ (jqModC K) = jqModC K' := map_jqModC σ

/-- `coeffMap σ` fixes every `j(q ^ n)`. -/
theorem coeffMap_jqNModC_eq (n : ℕ) [NeZero n] : coeffMap σ (jqNModC K n) = jqNModC K' n := by
  rw [jqNModC, jqNModC, ModularCurve.coeffMap_qExpand, coeffMap_jqModC_eq]

/-- `coeffMap σ` commutes with evaluating a `K`-polynomial at `j(q)`. -/
theorem coeffMap_aeval_jqModC_eq (P : Polynomial K) :
    coeffMap σ (Polynomial.aeval (jqModC K) P) = Polynomial.aeval (jqModC K') (P.map σ) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  have hcomp : (coeffMap σ).comp (algebraMap K (LaurentSeries K)) =
      (algebraMap K' (LaurentSeries K')).comp σ :=
    RingHom.ext fun c => coeffMap_algebraMap_eq σ c
  rw [hcomp, coeffMap_jqModC_eq]

/-- **Descent of polynomials**: a `K'`-polynomial that lies in the `coeffMap`
image of the Laurent series is the image of a `K`-polynomial. Induction on the
degree, peeling the leading coefficient with
`coeff_aeval_jqModC_neg_natDegree`. -/
theorem exists_map_eq_of_aeval_eq_coeffMap (P : Polynomial K')
    (hP : ∃ y : LaurentSeries K, coeffMap σ y = Polynomial.aeval (jqModC K') P) :
    ∃ Q : Polynomial K, Q.map σ = P := by
  generalize hn : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    obtain ⟨y, hy⟩ := hP
    have hlead : P.leadingCoeff = σ (y.coeff (-(P.natDegree : ℤ))) := by
      have h1 := coeff_aeval_jqModC_neg_natDegree (K := K') P
      rw [← hy, coeffMap_coeff] at h1
      exact h1.symm
    have hP' : ∃ y' : LaurentSeries K, coeffMap σ y' = Polynomial.aeval (jqModC K') P.eraseLead := by
      refine ⟨y - algebraMap K (LaurentSeries K) (y.coeff (-(P.natDegree : ℤ))) * jqModC K ^ P.natDegree, ?_⟩
      have h2 := congrArg (Polynomial.aeval (jqModC K')) (Polynomial.eraseLead_add_C_mul_X_pow P)
      rw [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X] at h2
      rw [map_sub, map_mul, map_pow, coeffMap_algebraMap_eq, coeffMap_jqModC_eq, hy, ← hlead, ← h2,
        add_sub_cancel_right]
    have hQ' : ∃ Q' : Polynomial K, Q'.map σ = P.eraseLead := by
      rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero P with hlt | h0
      · exact ih _ (hn ▸ hlt) P.eraseLead hP' rfl
      · exact ⟨0, by rw [Polynomial.map_zero, h0]⟩
    obtain ⟨Q', hQ'⟩ := hQ'
    refine ⟨Q' + Polynomial.C (y.coeff (-(P.natDegree : ℤ))) * Polynomial.X ^ P.natDegree, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hQ', ← hlead,
      Polynomial.eraseLead_add_C_mul_X_pow]

include σ in

/-- **Prime non-membership descends**: if `j(q ^ p)` is outside the base field
over `K`, it is outside the base field over any field `K'` mapping from `K`. -/
theorem jqNModC_not_mem_adjoin_of_not_mem_adjoin (p : ℕ) [hp : Fact (Nat.Prime p)]
    (h : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    jqNModC K' p ∉ IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K')) := by
  intro hmem
  have hpoly : ∃ P : Polynomial K', Polynomial.aeval (jqModC K') P = jqNModC K' p := by
    by_contra hcon
    exact ModularCurve.jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne p (fun P hP => hcon ⟨P, hP⟩) hmem
  obtain ⟨P, hP⟩ := hpoly
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_aeval_eq_coeffMap σ P ⟨jqNModC K p, by rw [coeffMap_jqNModC_eq, hP]⟩
  apply h
  have hinj : Function.Injective (coeffMap σ) := ModularCurve.coeffMap_injective σ.injective
  have hval : Polynomial.aeval (jqModC K) Q = jqNModC K p := by
    apply hinj
    rw [coeffMap_aeval_jqModC_eq, hQ, hP, coeffMap_jqNModC_eq]
  have h3 : Polynomial.aeval (jqModC K) Q
      = algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K)
          (Polynomial.aeval (jA K) Q) :=
    Polynomial.aeval_algebraMap_apply (LaurentSeries K) (jA K) Q
  rw [← hval, h3]
  exact (Polynomial.aeval (jA K) Q).2

/-- `coeffMap σ` maps the base field into the base field. -/
theorem coeffMap_mem_adjoin {x : LaurentSeries K}
    (hx : x ∈ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    coeffMap σ x ∈ IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K')) := by
  let E : IntermediateField K (LaurentSeries K) :=
    { (IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K'))).toSubfield.comap (coeffMap σ) with
      algebraMap_mem' := fun c => by
        show coeffMap σ (algebraMap K (LaurentSeries K) c)
          ∈ IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K'))
        rw [coeffMap_algebraMap_eq]
        exact (IntermediateField.adjoin K' _).algebraMap_mem (σ c) }
  have hle : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    show coeffMap σ (jqModC K) ∈ IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K'))
    rw [coeffMap_jqModC_eq]
    exact IntermediateField.subset_adjoin K' _ rfl
  exact hle hx

/-- The base-field map `K⟮j(q)⟯ →+* K'⟮j(q)⟯` induced by `σ`. -/
def tauAdjoin : (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
    →+* (IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K'))) where
  toFun x := ⟨coeffMap σ (x : LaurentSeries K), coeffMap_mem_adjoin σ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- `tauAdjoin σ` fixes the seed `j(q)`. -/
theorem tauAdjoin_jA : tauAdjoin σ (jA K) = jA K' :=
  Subtype.ext (coeffMap_jqModC_eq σ)

include σ in

/-- **The descent**: the `K'`-side degree statement implies the `K`-side one.
The `K'`-side `minpoly` is `phiAtSeed data (jA K')`; mapping along `tauAdjoin σ`
shows the `K`-side `phiAtSeed` is irreducible, hence it *is* the `K`-side
`minpoly`, and its degree is `ψ(d)`. -/
theorem finrank_adjoin_jqNModC_eq_of_map (d : ℕ) [NeZero d] (data : ModularPolynomialData d)
    (htight : Module.finrank (IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K')))
        (IntermediateField.adjoin (IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K')))
          ({jqNModC K' d} : Set (LaurentSeries K'))) = dedekindPsi d) :
    Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d := by
  have hint' : IsIntegral (IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K')))
      (jqNModC K' d) :=
    ModularCurve.isIntegral_jqNModC_of_modularPolynomialData K' data
  have hmin' : (minpoly (IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K')))
      (jqNModC K' d)).natDegree = dedekindPsi d := by
    rw [← IntermediateField.adjoin.finrank hint']
    exact htight
  have hΦ' : phiAtSeed data (jA K')
      = minpoly (IntermediateField.adjoin K' ({jqModC K'} : Set (LaurentSeries K'))) (jqNModC K' d) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint') (phiAtSeed_monic data _)
      (minpoly.dvd _ _ (aeval_jqNModC_phiAtSeed_jA K' d data))
      (le_of_eq ((phiAtSeed_natDegree data _).trans hmin'.symm))
  have hirr' : Irreducible (phiAtSeed data (jA K')) := by
    rw [hΦ']
    exact minpoly.irreducible hint'
  have hmapΦ : (phiAtSeed data (jA K)).map (tauAdjoin σ) = phiAtSeed data (jA K') := by
    rw [phiAtSeed_map, tauAdjoin_jA]
  have hirr : Irreducible (phiAtSeed data (jA K)) := by
    refine Polynomial.Monic.irreducible_of_irreducible_map (tauAdjoin σ) _ (phiAtSeed_monic data _) ?_
    rw [hmapΦ]
    exact hirr'
  have hint : IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K d) :=
    ModularCurve.isIntegral_jqNModC_of_modularPolynomialData K data
  have hmin : phiAtSeed data (jA K)
      = minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K d) :=
    minpoly.eq_of_irreducible_of_monic hirr (aeval_jqNModC_phiAtSeed_jA K d data) (phiAtSeed_monic data _)
  rw [IntermediateField.adjoin.finrank hint, ← hmin, phiAtSeed_natDegree]

end Transport

/-! ## The base non-membership, and the two headlines

In characteristic `p` the socket's hypothesis can fail: if `p ∣ d` then `(d : K) = 0`
and `qExpand K p` is the `p`-th power map (`qExpand_jqModC_eq_pow_unconditional`), so
`j(q ^ p) = j(q) ^ p` *is* in the base field. `natCast_ne_zero_of_socket` is the
contrapositive: the socket's `hbase` forces `(d : K) ≠ 0`, which is exactly the
hypothesis that lets `AlgebraicClosure K` supply a primitive `d`-th root of unity. -/

/-- **`d` is a unit in `K` when no prime divisor's Frobenius lands in the base
field.** Verbatim from `S_…_of_socket.lean:466`. -/
theorem natCast_ne_zero_of_socket (d : ℕ) [NeZero d]
    (hbase : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ d →
      jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    (d : K) ≠ 0 := by
  intro hd
  have hdvd : ringChar K ∣ d := ringChar.dvd hd
  have h0 : ringChar K ≠ 0 := fun h => NeZero.ne d (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_prime_of_ne_zero K h0⟩
  have hfrob : jqNModC K (ringChar K) = jqModC K ^ ringChar K :=
    ModularCurve.qExpand_jqModC_eq_pow_unconditional K

  have hmem : jqModC K ^ ringChar K ∈ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
    (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).pow_mem (IntermediateField.subset_adjoin K _ rfl)
      (ringChar K)
  rw [← hfrob] at hmem
  exact hbase (ringChar K) hdvd hmem

/-- The `S_` file's `private` re-export of the descent: `jqNModC_prime_not_mem_adjoin_of_ringHom`.
Kept `private`, as in the pin, and used by the headline below. -/
private theorem jqNModC_prime_not_mem_adjoin_of_ringHom {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₀ →+* K₁) (p : ℕ) [hp : Fact (Nat.Prime p)]
    (h : jqNModC K₀ p ∉ IntermediateField.adjoin K₀ ({jqModC K₀} : Set (LaurentSeries K₀))) :
    jqNModC K₁ p ∉ IntermediateField.adjoin K₁ ({jqModC K₁} : Set (LaurentSeries K₁)) :=
  jqNModC_not_mem_adjoin_of_not_mem_adjoin σ p h

/-- **The socket's degree formula.** `[K⟮j(q)⟯⟮j(q ^ d)⟯ : K⟮j(q)⟯] = ψ(d)`,
given that no prime `p ∣ d` already has `j(q ^ p)` in the base field. Verbatim
from `Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket.lean:8`
(the pin also states it as a `private` copy at `S_:483`, byte-identical). -/
theorem finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket {K : Type*} [Field K] (d : ℕ) [NeZero d]
    (hbase : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ d →
      jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d := by
  have hd : (d : K) ≠ 0 := natCast_ne_zero_of_socket d hbase
  haveI : NeZero ((d : ℕ) : K) := ⟨hd⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) d
  have hzu : IsUnit z := hz.isUnit (NeZero.ne d)
  have hζ : IsPrimitiveRoot ((hzu.unit : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) d := by
    rw [IsUnit.unit_spec]
    exact hz
  have hbase' : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ d → jqNModC (AlgebraicClosure K) p ∉
      IntermediateField.adjoin (AlgebraicClosure K)
        ({jqModC (AlgebraicClosure K)} : Set (LaurentSeries (AlgebraicClosure K))) :=
    fun (p : ℕ) [Fact (Nat.Prime p)] hp =>
      jqNModC_prime_not_mem_adjoin_of_ringHom (algebraMap K (AlgebraicClosure K)) p (hbase p hp)
  have htight' := (ModularCurve.package_of_socket d _ hζ hbase' d dvd_rfl).1
  obtain ⟨data, -⟩ := ModularCurve.exists_phiIrreducible d
  exact finrank_adjoin_jqNModC_eq_of_map (algebraMap K (AlgebraicClosure K)) d data htight'

/-- **The socket's degree formula, unconditionally in characteristic zero**:
`[K⟮j(q)⟯⟮j(q ^ d)⟯ : K⟮j(q)⟯] = ψ(d)`. Verbatim from
`Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero.lean:8`. -/
theorem finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero {K : Type*} [Field K] [CharZero K]
    (d : ℕ) [NeZero d] :
    Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d :=
  finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket d
    fun (p : ℕ) [Fact (Nat.Prime p)] _ => ModularCurve.jqNModC_prime_not_mem_adjoin_of_charZero p

end ModularCurve

end
