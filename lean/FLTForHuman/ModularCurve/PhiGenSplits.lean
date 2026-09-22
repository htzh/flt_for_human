/-
  T13 — the consequence, part 2: the splitting of the modular polynomial.

  `PhiGen.splits_of_prime` is the cone's content: the level-`p` datum, read at the
  level-`p` nome, is the conjugate product `∏_i (Y - conj_i)`. The proof joins the
  whole cone — T11's descent (a), T9's integrality (b), T8's membership (c), T11's
  assembly (d), this topic's `eq_of_prime` for uniqueness, and T11's
  `splits_of_coeff_evalAtJ_eq` for the read-off — first over `CyclotomicField p ℚ`,
  then transported to an arbitrary `ℚ`-algebra `K` along an embedding sending the
  chosen primitive root to `ζ`.

  `PhiGen.splits_prime_at_slot` is the cone's exported statement, math/010 §3's
  formula with the general level datum `(e, u)`:
  `Φ_p(j(u^p q^{pe}), Y) = (Y - j(u^{p^2} q^{p^2e})) ∏_b (Y - j(u ζ^b q^e))`,
  obtained from `splits_of_prime` at the primitive `p`-th root `ζ ^ (N / p)` and
  pushed through `qExpand K e ∘ qTwist u`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_splits_of_prime.lean` (353 lines) and
  `P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean` (288 lines). Both
  public statements are the `Theorems/` wrappers verbatim.

  ## Dedup

  The `TS` prelude both pin files repeat is `Defs/TS.lean` (`TS` and its ten
  coefficient lemmas) plus `Defs/Laurent.lean`'s `coeffEmb_qExpand`; the port
  writes only the three live bridges (`iota_jq`, `conj_zero_eq`, `conj_succ_eq`).
  The pin's ~200 lines of prelude that neither exported theorem uses
  (`phiAtSeed*`, `qTwistEquiv*`, `qTwist_TS_one_cycle`, `phiProd_conj_eq`,
  `roots_phiProd_conj*`, `iota_jqN`, `qTwist_iota_of_pow_eq_one`, and the at-slot
  roots API `prod_form_ne_zero`/`roots_prime_at_slot*`/`isRoot_prime_at_slot_iff`)
  exist for the char-`p` `*_of_isPrimitiveRoot` variants, which are outside the
  44-node cone and are not ported here.

  ## Assumptions

  `Defs/TS`, `Defs/Laurent` (`coeffEmb_qExpand`), `Defs/Twist`, `Defs/Jq`,
  `Defs/PhiGen` (`conj`, `phiProd`), `Defs/Polynomial`; T8's
  `mem_adjoin_jq_of_phiGenDescends`; T9's `PhiGenDescends.intCoeffs`; T11's
  `exists_phiGenDescends`, `exists_modularPolynomialData_coeff_eq`,
  `splits_of_coeff_evalAtJ_eq`; this topic's `ModularPolynomialData.eq_of_prime`.
-/
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

set_option autoImplicit false
-- The pin's proofs install `IsCyclotomicExtension`/`IsGalois`/`FiniteDimensional`
-- instances with `haveI`; the style linter prefers `have`, but the instances are
-- consumed by instance search and `haveI` is the faithful spelling (T12's
-- `ModularPolynomialProperties` disables the same linter locally).
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve
namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## The live bridges from `conj` to `TS`

`iota_jq`, `conj_zero_eq` and `conj_succ_eq` were this module's `private`
copies; T14 promoted the canonical copies to `Defs/PhiAtSlot.lean` (public), which
this module imports, so the twins are gone. -/

/-! ## A primitive `p`-th root in `CyclotomicField p ℚ`

`exists_isPrimitiveRoot_cyclotomicField`, `cycUnit`, `cycUnit_spec`,
`cycUnit_pow` and `isPrimitiveRoot_pow_div` are public in
`Defs/Cyclotomic.lean` (promoted there from the FFG spine's private copies, which
the pin repeats in both `splits_*` files). They are imported, not re-declared. -/

/-! ## Transport of the identity along a `ℚ`-algebra embedding -/

section Transport

variable {K₀ : Type*} [Field K₀] [Algebra ℚ K₀]

/-! `coeffMap_qTwist`, `coeffMap_coeffEmb_algHom` and `coeffMap_TS` were this
module's `private` transport copies; T16 promoted the canonical copies to
`Defs/Twist.lean`, `Defs/Laurent.lean` and `Defs/TS.lean` (all imported here), so
the twins are gone. `coeffMap_conj` below now uses the public `coeffMap_TS`. -/

private theorem coeffMap_conj (σ : K₀ →ₐ[ℚ] K) (p : ℕ) [Fact p.Prime] (ζ : K₀ˣ)
    (i : Fin (p + 1)) :
    coeffMap (σ : K₀ →+* K) (conj p ζ i) =
      conj p (Units.map (σ : K₀ →+* K).toMonoidHom ζ) i := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [conj_zero_eq, conj_zero_eq, coeffMap_TS, map_one]
  · rw [conj_succ_eq, conj_succ_eq, coeffMap_TS, map_pow]

private theorem map_coeffMap_phiProd (σ : K₀ →ₐ[ℚ] K) (p : ℕ) [Fact p.Prime] (ζ : K₀ˣ) :
    (phiProd p (conj p ζ)).map (coeffMap (σ : K₀ →+* K)) =
      phiProd p (conj p (Units.map (σ : K₀ →+* K).toMonoidHom ζ)) := by
  rw [phiProd, phiProd, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, coeffMap_conj]

end Transport

/-! ## The splitting at a prime -/

/-- The identity at `CyclotomicField p ℚ`, with the chosen primitive root
`cycUnit p`: assemble the datum from the descended family and identify it with the
input by `eq_of_prime`. -/
private theorem splits_of_prime_cyclotomicField (p : ℕ) [hp : Fact p.Prime]
    (data : ModularPolynomialData p) :
    data.Φ.map (((coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)).comp evalAtJ) =
      phiProd p (conj p (cycUnit p)) := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  haveI : IsGalois ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.isGalois {p} ℚ (CyclotomicField p ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ (CyclotomicField p ℚ)
  have hζ := cycUnit_spec p
  obtain ⟨c, hc⟩ := exists_phiGenDescends p (cycUnit p) hζ
  have hint : ∀ k, IntCoeffs (c k) := fun k => hc.intCoeffs (cycUnit_pow p) k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => mem_adjoin_jq_of_phiGenDescends p (cycUnit p) hζ c hc k
  obtain ⟨data₀, hdata₀⟩ := exists_modularPolynomialData_coeff_eq hc hint hmem
  rw [ModularPolynomialData.eq_of_prime p data data₀]
  exact splits_of_coeff_evalAtJ_eq (cycUnit p) hc data₀ hdata₀

/-- The modular polynomial splits into its `p + 1` conjugates. Verbatim from the
pin wrapper `Theorems/Thm_ModularCurve_PhiGen_splits_of_prime.lean`. -/
theorem splits_of_prime {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) = phiProd p (conj p ζ) := by

  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hζ₀ := cycUnit_spec p
  have hirr := Polynomial.cyclotomic.irreducible_rat hp.out.pos
  obtain ⟨σ, hσ⟩ : ∃ σ : CyclotomicField p ℚ →ₐ[ℚ] K, σ (cycUnit p : CyclotomicField p ℚ) = ζ :=
    ⟨(hζ₀.embeddingsEquivPrimitiveRoots K hirr).symm
        ⟨ζ, (mem_primitiveRoots hp.out.pos).mpr hζ⟩, by
      rw [← hζ₀.embeddingsEquivPrimitiveRoots_apply_coe K hirr, Equiv.apply_symm_apply]⟩
  have hσu : Units.map (σ : CyclotomicField p ℚ →+* K).toMonoidHom (cycUnit p) = ζ :=
    Units.ext (by rw [Units.coe_map]; exact hσ)

  have h := congrArg (Polynomial.map (coeffMap (σ : CyclotomicField p ℚ →+* K)))
    (splits_of_prime_cyclotomicField p data)
  rw [map_coeffMap_phiProd, hσu, Polynomial.map_map] at h
  convert h using 2
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.comp_apply, evalAtJ_X]
  rw [coeffMap_coeffEmb_algHom]

/-! ## The splitting at a general slot

`qExpand_qTwist_TS`, this module's former `private` bridge, is now public in
`Defs/TS.lean` beside `TS` (T14), and `Defs/TS` is imported above. -/

/-- The cone's headline: the twisted, dilated slot splitting. Verbatim from the
pin wrapper `Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean`. -/
theorem splits_prime_at_slot {K : Type*} [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) N) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))) =
      (Polynomial.X - Polynomial.C (qExpand K (p * (p * e))
        (qTwist (u ^ (p * p)) (coeffEmb K jq)))) *
        ∏ b ∈ Finset.range p,
          (Polynomial.X - Polynomial.C (qExpand K e
            (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))) := by

  have hζp : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p :=
    isPrimitiveRoot_pow_div hζ hpN
  have h0 := splits_of_prime p (ζ ^ (N / p)) hζp data

  have hhom : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))
      = ((qExpand K e).comp (qTwist u)).comp (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply, evalAtJ_X]
    rw [iota_jq, qExpand_qTwist_TS, mul_one, zpow_natCast]
    exact (TS_congr (Nat.mul_comm e p) (u ^ p)).symm

  have h₀ : ((qExpand K e).comp (qTwist u)) (conj p (ζ ^ (N / p)) (0 : Fin (p + 1)))
      = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)) := by
    rw [RingHom.comp_apply, conj_zero_eq, qExpand_qTwist_TS, mul_one, zpow_natCast]
    exact TS_congr (by ring) (u ^ (p * p))

  have h₁ : ∀ b : Fin p,
      ((qExpand K e).comp (qTwist u)) (conj p (ζ ^ (N / p)) b.succ)
      = qExpand K e (qTwist (u * ζ ^ ((b : ℕ) * (N / p))) (coeffEmb K jq)) := by
    intro b
    rw [RingHom.comp_apply, conj_succ_eq, qExpand_qTwist_TS,
      Nat.cast_one, zpow_one, ← pow_mul, Nat.mul_comm (N / p) (b : ℕ)]
    exact TS_congr (mul_one e) (u * ζ ^ ((b : ℕ) * (N / p)))

  rw [hhom, ← Polynomial.map_map, h0,
    show phiProd p (conj p (ζ ^ (N / p)))
        = ∏ i : Fin (p + 1), (Polynomial.X - Polynomial.C (conj p (ζ ^ (N / p)) i)) from rfl,
    Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  simp only [Fin.prod_univ_succ]
  congr 1
  · rw [h₀]
  · rw [Finset.prod_range
      (fun b => Polynomial.X - Polynomial.C (qExpand K e
        (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq))))]
    exact Finset.prod_congr rfl fun i _ => by rw [h₁ i]

end PhiGen
end ModularCurve

end

#print axioms ModularCurve.PhiGen.splits_of_prime
#print axioms ModularCurve.PhiGen.splits_prime_at_slot
