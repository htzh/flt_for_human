/-
  The prime-level uniqueness of the modular equation, and its splitting.

  Two facts about the datum at a prime `p`, and the root family they make explicit:

  * uniqueness — any two data at `p` are equal, because each `toAdjoin` is the minimal polynomial
    of `j(q ^ p)` and the relative degree is `p + 1`;
  * the splitting — `Φ_p(j(u ^ p q ^ (p * e)), Y) = (Y - j(u ^ (p * p) q ^ (p * p * e)))
    ∏ b, (Y - j(u ζ ^ b q ^ e))`, first over `ℚ(ζ_p)`, then over any field carrying a primitive
    `p`-th root, and at an arbitrary level datum `(e, u)`.

  The module also exports the at-slot root API: the slot values are exactly the roots, they are
  distinct, and the slot polynomial factors through them.

  Together with `Existence`, this is the public surface of the theory at a prime.
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.KatzLevelPCusps
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.ModularEquation.Construction
import FLTForHuman.ModularCurve.ModularEquation.Existence
import FLTForHuman.ModularCurve.ModularEquation.Support.LevelEmbedding

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve

/-! ## The relative degree of `j(q ^ N)` -/

section Finrank

variable {N : ℕ} [NeZero N]

/-- For an irreducible datum the relative degree is `ψ(N)`: `data.toAdjoin` is the
minimal polynomial of `j(q ^ N)`, and `IntermediateField.adjoin.finrank` turns the
degree of that minimal polynomial into the degree of the simple extension. -/
private theorem finrank_adjoin_jqN_eq (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) :
    Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ = dedekindPsi N := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      rw [← Polynomial.aeval_def]
      exact aeval_jqN_toAdjoin data⟩
  rw [IntermediateField.adjoin.finrank hint, ModularPolynomialData.minpoly_jqN_eq data hirr,
    ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

end Finrank

/-- The relative degree at a prime is `p + 1`. -/
theorem finrank_adjoin_jqN_eq_of_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN ℓ} : Set (LaurentSeries ℚ))) = ℓ + 1 := by
  obtain ⟨data, hirr, -⟩ := exists_phiIrreducible_evalSymm ℓ
  rw [show Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          ({jqN ℓ} : Set (LaurentSeries ℚ))) = dedekindPsi ℓ from
      finrank_adjoin_jqN_eq data hirr,
    dedekindPsi_prime hℓ.out]

/-! ## Uniqueness of the datum -/

section Uniqueness

variable {N : ℕ} [NeZero N]

/-- The `Y`-degree of the transported datum is `ψ(N)`. -/
private theorem natDegree_toAdjoin (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

/-- Every datum at a prime has `toAdjoin` equal to the minimal polynomial of
`j(q ^ p)`: it is monic, it annihilates `j(q ^ p)`, and its degree is the
minimal one, `p + 1`.

The `p + 1` is not read off the datum. `natDegree_toAdjoin` plus divisibility give
`(minpoly …).natDegree ≤ ψ(p)` — the datum is a monic annihilator, so the minimal polynomial
divides it — while `eq_of_monic_of_dvd_of_natDegree_le` wants the *reverse* inequality,
`ψ(p) ≤ (minpoly …).natDegree`. That one is `finrank_adjoin_jqN_eq_of_prime`, i.e. the
irreducibility of the datum's `Φ`, and it is the whole reason this theorem (and
`eq_of_prime` on it) is char 0 rather than bookkeeping. -/
private theorem toAdjoin_eq_minpoly (p : ℕ) [hp : Fact p.Prime] (data : ModularPolynomialData p) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN p) := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN p) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin data⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN p)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_of_prime p
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ (aeval_jqN_toAdjoin data)) ?_
  rw [hdeg, natDegree_toAdjoin, dedekindPsi_prime hp.out]

end Uniqueness

namespace ModularPolynomialData

/-- Any two modular-polynomial data at a prime are equal. -/
theorem eq_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (d d' : ModularPolynomialData p) :
    d = d' := by
  have h : d.Φ = d'.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    change d.toAdjoin = d'.toAdjoin
    rw [toAdjoin_eq_minpoly p d, toAdjoin_eq_minpoly p d']
  cases d
  cases d'
  cases h
  rfl

end ModularPolynomialData

end ModularCurve

namespace ModularCurve
namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## Transport of the identity along a `ℚ`-algebra embedding -/

section Transport

variable {K₀ : Type*} [Field K₀] [Algebra ℚ K₀]

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
    data.Φ.map (evalAtJK (CyclotomicField p ℚ) p) = phiProd p (conj p (cycUnit p)) := by
  have : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have : IsGalois ℚ (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.isGalois {p} ℚ (CyclotomicField p ℚ)
  have hζ := cycUnit_spec p
  obtain ⟨c, hdescend⟩ := exists_phiGenDescends p (cycUnit p) hζ
  have hIntCoeffs : ∀ k, IntCoeffs (c k) := fun k => hdescend.intCoeffs (cycUnit_pow p) k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => mem_adjoin_jq_of_phiGenDescends p (cycUnit p) hζ c hdescend k
  obtain ⟨data₀, hdata₀⟩ := exists_modularPolynomialData_coeff_eq hdescend hIntCoeffs hmem
  rw [ModularPolynomialData.eq_of_prime p data data₀]
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, evalAtJK_def, RingHom.comp_apply, hdata₀ k,
    qEmbedT_eq_coeffEmb_qExpand, ← hdescend k]

/-- The modular polynomial splits into its `p + 1` conjugates, stated with `evalAtJK K p`. -/
theorem splits_of_prime {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    data.Φ.map (evalAtJK K p) = phiProd p (conj p ζ) := by

  have : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hζ₀ := cycUnit_spec p
  have hirr := Polynomial.cyclotomic.irreducible_rat hp.out.pos
  obtain ⟨σ, hσ⟩ : ∃ σ : CyclotomicField p ℚ →ₐ[ℚ] K, σ (cycUnit p : CyclotomicField p ℚ) = ζ :=
    ⟨(hζ₀.embeddingsEquivPrimitiveRoots K hirr).symm
        ⟨ζ, (mem_primitiveRoots hp.out.pos).mpr hζ⟩, by
      rw [← hζ₀.embeddingsEquivPrimitiveRoots_apply_coe K hirr, Equiv.apply_symm_apply]⟩
  have hσu : Units.map (σ : CyclotomicField p ℚ →+* K).toMonoidHom (cycUnit p) = ζ :=
    Units.ext (by rw [Units.coe_map]; exact hσ)

  have hmap : evalAtJK K p
      = (coeffMap (σ : CyclotomicField p ℚ →+* K)).comp (evalAtJK (CyclotomicField p ℚ) p) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.comp_apply, evalAtJK_X, coeffMap_qExpand, coeffMap_coeffEmb_algHom]
  have h := congrArg (Polynomial.map (coeffMap (σ : CyclotomicField p ℚ →+* K)))
    (splits_of_prime_cyclotomicField p data)
  rw [map_coeffMap_phiProd, hσu, Polynomial.map_map] at h
  calc data.Φ.map (evalAtJK K p)
      = data.Φ.map ((coeffMap (σ : CyclotomicField p ℚ →+* K)).comp
          (evalAtJK (CyclotomicField p ℚ) p)) := by rw [hmap]
    _ = phiProd p (conj p ζ) := h

/-! ## The splitting at a general slot -/

/-- The twisted, dilated slot splitting. -/
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
  have hsplits := splits_of_prime p (ζ ^ (N / p)) hζp data

  have hhom : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))
      = ((qExpand K e).comp (qTwist u)).comp (evalAtJK K p) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJK_def, RingHom.comp_apply,
      evalAtJ_X, qEmbedT_jq]
    rw [← coeffEmb_qExpand K p jq, iota_jq (K := K) (N := p), qExpand_qTwist_TS, mul_one,
      zpow_natCast, coeffEmb_jq]
    exact (TS_congr (Nat.mul_comm e p) (u ^ p)).symm

  have h₀ : ((qExpand K e).comp (qTwist u)) (conj p (ζ ^ (N / p)) (0 : Fin (p + 1)))
      = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)) := by
    rw [RingHom.comp_apply, conj_zero_eq, qExpand_qTwist_TS, mul_one, zpow_natCast,
      coeffEmb_jq]
    exact TS_congr (by ring) (u ^ (p * p))

  have h₁ : ∀ b : Fin p,
      ((qExpand K e).comp (qTwist u)) (conj p (ζ ^ (N / p)) b.succ)
      = qExpand K e (qTwist (u * ζ ^ ((b : ℕ) * (N / p))) (coeffEmb K jq)) := by
    intro b
    rw [RingHom.comp_apply, conj_succ_eq, qExpand_qTwist_TS,
      Nat.cast_one, zpow_one, ← pow_mul, Nat.mul_comm (N / p) (b : ℕ), coeffEmb_jq]
    exact TS_congr (mul_one e) (u * ζ ^ ((b : ℕ) * (N / p)))

  have hmain : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))
      = (phiProd p (conj p (ζ ^ (N / p)))).map ((qExpand K e).comp (qTwist u)) := by
    calc data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))
        = (data.Φ.map (evalAtJK K p)).map ((qExpand K e).comp (qTwist u)) := by
          rw [hhom, ← Polynomial.map_map]
      _ = (phiProd p (conj p (ζ ^ (N / p)))).map ((qExpand K e).comp (qTwist u)) := by
          rw [hsplits]
  have hpush : (phiProd p (conj p (ζ ^ (N / p)))).map ((qExpand K e).comp (qTwist u))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e))
          (qTwist (u ^ (p * p)) (coeffEmb K jq))))
        * ∏ b ∈ Finset.range p,
            (Polynomial.X - Polynomial.C (qExpand K e
              (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))) := by
    rw [phiProd, Polynomial.map_prod, Fin.prod_univ_succ]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 1
    · rw [h₀]
    · rw [Finset.prod_range
        (fun b => Polynomial.X - Polynomial.C (qExpand K e
          (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq))))]
      exact Finset.prod_congr rfl fun i _ => by rw [h₁ i]
  rw [hmain, hpush]

end PhiGen
end ModularCurve

namespace ModularCurve
namespace PhiGen

variable {K : Type*} [Field K]

/-! ## The transport engine

`integral` is the core: the splitting, pulled back from `CyclotomicField p ℚ` to the
integral cyclotomic order `cyclRing ℤ p` along the injective `iota`. `zetaLift` then pushes it
forward to an arbitrary field along the chosen primitive root `ζ`. -/

/-- Evaluating an integer polynomial at `jq` and then pushing it through `φ` is evaluating it
at `φ jq`. -/
private theorem comp_evalAtJ {L : Type*} [CommRing L] (φ : LaurentSeries ℚ →+* L) :
    φ.comp evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom L) (φ jq) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have h1 : evalAtJ (Polynomial.C a) = ((a : ℤ) : LaurentSeries ℚ) := by
      simp [evalAtJ]
    rw [RingHom.comp_apply, h1, map_intCast, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    simp
  · rw [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

section Engine

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The map from the integral cyclotomic order to `CyclotomicField p ℚ` sending
the abstract root to the chosen primitive root `cycUnit p`. -/
private def iota : cyclRing ℤ p →+* CyclotomicField p ℚ :=
  AdjoinRoot.lift (Int.castRingHom (CyclotomicField p ℚ))
    ((cycUnit p : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ) (by
      rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
      exact Polynomial.IsRoot.eq_zero ((cycUnit_spec p).isRoot_cyclotomic hp.out.pos))

private theorem iota_units_zeta :
    Units.map (iota p).toMonoidHom (cyclZeta ℤ p) = cycUnit p :=
  Units.ext (by rw [Units.coe_map, val_cyclZeta]; exact AdjoinRoot.lift_root _)

/-- `iota` is injective: the cyclotomic polynomial is the minimal polynomial of
the chosen primitive root over `ℚ`, and `map_dvd_map` reflects divisibility along
the injective `ℤ → ℚ`. -/
private theorem iota_injective : Function.Injective (iota p) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [iota, AdjoinRoot.lift_mk] at ha
  rw [AdjoinRoot.mk_eq_zero]
  have hq : Polynomial.aeval ((cycUnit p : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ)
      (g.map (Int.castRingHom ℚ)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap ℚ (CyclotomicField p ℚ)).comp (Int.castRingHom ℚ)
        = Int.castRingHom (CyclotomicField p ℚ) from RingHom.ext_int _ _]
    exact ha
  have hdvd : Polynomial.cyclotomic p ℚ ∣ g.map (Int.castRingHom ℚ) := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat (cycUnit_spec p) hp.out.pos]
    exact minpoly.dvd ℚ _ hq
  rw [← Polynomial.map_cyclotomic_int p ℚ] at hdvd
  exact (Polynomial.map_dvd_map (Int.castRingHom ℚ) Int.cast_injective
    (Polynomial.cyclotomic.monic p ℤ)).mp hdvd

/-- The splitting over the integral cyclotomic order: pull the char-0 identity
back along the injective `iota`. Both the `X` slot and the `jq` slot are read
through `coeffMap (iota p)` and `map_jqModC`, and distinctness of the conjugates is
what makes the pullback legitimate. -/
private theorem integral (data : ModularPolynomialData p) :
    phiAtSeed data (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))
      = (Polynomial.X - Polynomial.C (qExpand (cyclRing ℤ p) (p * p)
          (jqModC (cyclRing ℤ p))))
        * ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
            (jqModC (cyclRing ℤ p)))) := by
  classical
  have hK := ModularCurve.PhiGen.splits_of_prime p (cycUnit p) (cycUnit_spec p) data
  have hLK : data.Φ.map (evalAtJK (CyclotomicField p ℚ) p)
      = phiAtSeed data (qExpand (CyclotomicField p ℚ) p (jqModC (CyclotomicField p ℚ))) := by
    have hseed : qEmbedT (CyclotomicField p ℚ) p jq
        = qExpand (CyclotomicField p ℚ) p (jqModC (CyclotomicField p ℚ)) := by
      rw [qEmbedT_jq, coeffEmb_jq]
    rw [evalAtJK_def, comp_evalAtJ, hseed, phiAtSeed]
  have hseedO : coeffMap (iota p)
      (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))
      = qExpand (CyclotomicField p ℚ) p (jqModC (CyclotomicField p ℚ)) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (iota p)
  have hmapProd :
      ((Polynomial.X - Polynomial.C (qExpand (cyclRing ℤ p) (p * p)
          (jqModC (cyclRing ℤ p))))
        * ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
            (jqModC (cyclRing ℤ p))))).map (coeffMap (iota p))
      = phiProd p (conj p (cycUnit p)) := by
    rw [phiProd, Fin.prod_univ_succ, Polynomial.map_mul]
    congr 1
    · rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, conj_zero]
      congr 2
      rw [coeffMap_qExpand, coeffEmb_jq]
      congr 1
      exact map_jqModC (iota p)
    · rw [← Polynomial.coe_mapRingHom, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        conj_succ,
        coeffMap_qTwist (iota p) ((cyclZeta ℤ p) ^ (b : ℕ))
          (Units.map (iota p).toMonoidHom ((cyclZeta ℤ p) ^ (b : ℕ))) rfl,
        map_pow, iota_units_zeta, coeffEmb_jq]
      exact congrArg
        (fun z => Polynomial.X - Polynomial.C (qTwist (cycUnit p ^ (b : ℕ)) z))
        (map_jqModC (iota p))
  apply Polynomial.map_injective (coeffMap (iota p))
    (ModularCurve.coeffMap_injective (iota_injective p))
  have hmain : (phiAtSeed data (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))).map
        (coeffMap (iota p)) = phiProd p (conj p (cycUnit p)) := by
    calc (phiAtSeed data (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))).map
            (coeffMap (iota p))
        = phiAtSeed data (qExpand (CyclotomicField p ℚ) p (jqModC (CyclotomicField p ℚ))) := by
          rw [phiAtSeed_map, hseedO]
      _ = data.Φ.map (evalAtJK (CyclotomicField p ℚ) p) := hLK.symm
      _ = phiProd p (conj p (cycUnit p)) := hK
  exact hmain.trans hmapProd.symm

/-- The push-forward: the integral identity transported along the chosen primitive
root `ζ` of an arbitrary field. -/
private def zetaLift (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    cyclRing ℤ p →+* K :=
  AdjoinRoot.lift (Int.castRingHom K) (ζ : K) (by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
    exact Polynomial.IsRoot.eq_zero (hζ.isRoot_cyclotomic hp.out.pos))

private theorem zetaLift_units_zeta (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    Units.map (zetaLift p ζ hζ).toMonoidHom (cyclZeta ℤ p) = ζ :=
  Units.ext (by rw [Units.coe_map, val_cyclZeta]; exact AdjoinRoot.lift_root _)

/-- The splitting at the level-`p` nome over an arbitrary field: push `integral`
forward along `ζ`. -/
theorem phiAtSeed_qExpand_prime_eq (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    phiAtSeed data (qExpand K p (jqModC K))
      = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by
  classical
  have h := congrArg (Polynomial.map (coeffMap (zetaLift p ζ hζ))) (integral p data)
  have hseed : coeffMap (zetaLift p ζ hζ)
      (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))
      = qExpand K p (jqModC K) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (zetaLift p ζ hζ)
  have hspread : coeffMap (zetaLift p ζ hζ)
      (qExpand (cyclRing ℤ p) (p * p) (jqModC (cyclRing ℤ p)))
      = qExpand K (p * p) (jqModC K) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (zetaLift p ζ hζ)
  have hfac : ∀ b : Fin p,
      (Polynomial.mapRingHom (coeffMap (zetaLift p ζ hζ)))
        (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
          (jqModC (cyclRing ℤ p))))
      = Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K)) := by
    intro b
    rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      coeffMap_qTwist (zetaLift p ζ hζ) ((cyclZeta ℤ p) ^ (b : ℕ))
        (Units.map (zetaLift p ζ hζ).toMonoidHom ((cyclZeta ℤ p) ^ (b : ℕ))) rfl,
      map_pow, zetaLift_units_zeta]
    exact congrArg (fun z => Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) z))
      (map_jqModC (zetaLift p ζ hζ))
  calc phiAtSeed data (qExpand K p (jqModC K))
      = (phiAtSeed data (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))).map
          (coeffMap (zetaLift p ζ hζ)) := by
        rw [phiAtSeed_map, hseed]
    _ = ((Polynomial.X - Polynomial.C (qExpand (cyclRing ℤ p) (p * p)
            (jqModC (cyclRing ℤ p))))
          * ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
              (jqModC (cyclRing ℤ p))))).map (coeffMap (zetaLift p ζ hζ)) := h
    _ = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
        * ∏ b ∈ Finset.range p,
            (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by
        rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hspread,
          ← Polynomial.coe_mapRingHom, map_prod, Finset.prod_congr rfl fun b _ => hfac b,
          Fin.prod_univ_eq_prod_range
            (fun b => Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))]

/-- The splitting at a general slot over an arbitrary field: push the level-`p`
identity through `qExpand K e ∘ qTwist u`. -/
theorem phiAtSeed_slot_prime_eq (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    phiAtSeed data (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) := by
  classical
  set f : LaurentSeries K →+* LaurentSeries K := (qExpand K e).comp (qTwist u) with hf
  have hseed : f (qExpand K p (jqModC K)) = qExpand K (p * e) (qTwist (u ^ p) (jqModC K)) := by
    rw [hf, RingHom.comp_apply, qTwist_qExpand, qExpand_qExpand, zpow_natCast]
    exact qExpand_congr (Nat.mul_comm e p) _
  have hspread : f (qExpand K (p * p) (jqModC K)) = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)) := by
    rw [hf, RingHom.comp_apply, qTwist_qExpand, qExpand_qExpand, zpow_natCast]
    exact qExpand_congr (by ring) _
  have hfac : ∀ b ∈ Finset.range p,
      (Polynomial.mapRingHom f) (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))
        = Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) := by
    intro b _
    rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hf,
      RingHom.comp_apply, qTwist_qTwist]
  calc phiAtSeed data (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))
      = phiAtSeed data (f (qExpand K p (jqModC K))) := by
        rw [hseed]
    _ = (phiAtSeed data (qExpand K p (jqModC K))).map f :=
        (phiAtSeed_map data (qExpand K p (jqModC K)) f).symm
    _ = ((Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
          * ∏ b ∈ Finset.range p,
              (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))).map f :=
        congrArg (Polynomial.map f) (phiAtSeed_qExpand_prime_eq p ζ hζ data)
    _ = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e))
          (qTwist (u ^ (p * p)) (jqModC K))))
        * ∏ b ∈ Finset.range p,
            (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) := by
        rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hspread,
          ← Polynomial.coe_mapRingHom, map_prod, Finset.prod_congr rfl hfac]

end Engine

/-! ## The two headlines -/

/-- The modular polynomial splits into its `p + 1` conjugates over an arbitrary field; the
`eval₂RingHom` map is `phiAtSeed` by definition. -/
theorem splits_prime_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K p (jqModC K)))
      = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) :=
  phiAtSeed_qExpand_prime_eq p ζ hζ data

/-- The headline at the general slot: the same splitting with the level datum `(e, u)`. -/
theorem splits_prime_at_slot_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) :=
  phiAtSeed_slot_prime_eq p ζ hζ data e u

end PhiGen

/-! ## The at-slot roots API -/

section Roots

variable {K : Type*} [Field K]

/-- The product `(X - j(u ^ p² q ^ p²e)) · ∏_{b < p} (X - j(u ζ^b q^e))` is
nonzero: its factors are `X - C` and a product of monic linear factors. It stays `private`
because its public home is the more general `PhiSlotRoots.prod_form_ne_zero`. -/
private theorem prod_form_ne_zero (ζ : Kˣ) (p : ℕ) [NeZero p] (e : ℕ) [NeZero e] (u : Kˣ) :
    (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)))) *
        ∏ b ∈ Finset.range p,
          (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) ≠ 0 :=
  mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero

/-- The roots of `data.Φ`, read at the slot `u q ^ e`, are the `p + 1` values
`j(u ^ p² q ^ p²e)` and `j(u ζ^b q^e)` — via the at-slot splitting and
`roots_mul`. -/
theorem roots_prime_at_slot_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).roots
      = (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))) ::ₘ
          (Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) := by
  rw [ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u,
    Polynomial.roots_mul (prod_form_ne_zero ζ p e u), Polynomial.roots_X_sub_C,
    Finset.prod_eq_multiset_prod, Finset.range_val,
    show (Multiset.range p).map
          (fun b => Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K))))
        = ((Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))).map
            (fun a => Polynomial.X - Polynomial.C a) from
      (Multiset.map_map (fun a => Polynomial.X - Polynomial.C a)
        (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) (Multiset.range p)).symm,
    Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

/-- Those `p + 1` roots are distinct: the extra root sits at level `p²` while the
others sit at level `e` (separated by `TS_injective`, whose level is the twist
exponent), and the latter are separated by `IsPrimitiveRoot.pow_inj` on `ζ`. -/
theorem roots_prime_at_slot_nodup_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    ((qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))) ::ₘ
        (Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))).Nodup := by
  rw [Multiset.nodup_cons]
  constructor
  · intro hmem
    obtain ⟨b, hb, heq⟩ := Multiset.mem_map.mp hmem
    have h := (TS_injective (K := K) (e := e) (e' := p * (p * e)) (u := u * ζ ^ b) (u' := u ^ (p * p)) heq).1
    have hp2 : 2 ≤ p := hp.out.two_le
    have he1 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
    have hmono : 2 * (2 * e) ≤ p * (p * e) := Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
    rw [← h] at hmono
    omega
  · refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range p)
    intro b hb b' hb' heq
    rw [Multiset.mem_range] at hb hb'
    have h := (TS_injective (K := K) (e := e) (e' := e) (u := u * ζ ^ b) (u' := u * ζ ^ b') heq).2
    have h2 : ζ ^ b = ζ ^ b' := mul_left_cancel h
    have h3 : ((ζ : Kˣ) : K) ^ b = ((ζ : Kˣ) : K) ^ b' := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2]
    exact hζ.pow_inj hb hb' h3

/-- The packaged distinctness of `data.Φ`'s roots at the slot. -/
theorem roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).roots.Nodup := by
  rw [roots_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u]
  exact roots_prime_at_slot_nodup_of_isPrimitiveRoot p ζ hζ e u

/-- Membership in the root multiset, in iff form: `y` is a root of the slot
polynomial exactly when it is the extra conjugate or one of the `p` finite ones
`j(u ζ^b q^e)`. -/
theorem isRoot_prime_at_slot_iff_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) (y : LaurentSeries K) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).IsRoot y ↔
      y = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)) ∨
        ∃ b < p, y = qExpand K e (qTwist (u * ζ ^ b) (jqModC K)) := by
  have hne : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))) ≠ 0 := by
    rw [ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u]
    exact prod_form_ne_zero ζ p e u
  rw [← Polynomial.mem_roots hne, roots_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u,
    Multiset.mem_cons, Multiset.mem_map]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mp hb, rfl⟩
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mpr hb, rfl⟩

/-- The same roots, read as `TS` values (`TS K e u = qExpand K e (qTwist u (jqModC K))`
by definition). Five C-layer consumers. -/
theorem roots_phiAtSeed_TS (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (phiAtSeed data (TS K (p * e) (u ^ p))).roots
      = TS K (p * (p * e)) (u ^ (p * p)) ::ₘ (Multiset.range p).map (fun b => TS K e (u * ζ ^ b)) :=
  roots_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u

end Roots

end ModularCurve

namespace ModularCurve

/-- At a prime there is a symmetric datum. -/
theorem exists_modularPolynomialData_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ := by
  obtain ⟨data, _, hsymm⟩ := exists_phiIrreducible_evalSymm ℓ
  exact ⟨data, hsymm⟩

namespace ModularPolynomialData

/-- At a prime the datum is symmetric: uniqueness identifies it with the symmetric datum the
capstone produces. -/
theorem evalSymm_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) :
    EvalSymm data.Φ := by
  obtain ⟨d, hd⟩ := exists_modularPolynomialData_evalSymm p
  rw [ModularPolynomialData.eq_of_prime p data d]
  exact hd

end ModularPolynomialData

/-! ## The transpose of `Φ_p` and its coefficient-degree bound -/

/-- The inner map of the swap is the coefficient map `c ↦ c.map C`: both send `X` to the
constant polynomial `X`. -/
private theorem swapInner_eq_map (c : Polynomial ℤ) :
    swapInner c = c.map (Polynomial.C : ℤ →+* Polynomial ℤ) := by
  show Polynomial.aeval (R := ℤ) (Polynomial.X : Polynomial (Polynomial ℤ)) c = _
  rw [Polynomial.aeval_def, Polynomial.map]
  congr 1

/-- The swap of `C c * X ^ b` is the transpose monomial `c.map C * C (X ^ b)`. -/
private theorem swapBivar_C_mul_X_pow (c : Polynomial ℤ) (b : ℕ) :
    swapBivar (Polynomial.C c * Polynomial.X ^ b)
      = c.map (Polynomial.C : ℤ →+* Polynomial ℤ) * Polynomial.C (Polynomial.X ^ b) := by
  rw [map_mul, map_pow, swapBivar_X, ← map_pow]
  congr 1
  show Polynomial.eval₂ swapInner (Polynomial.C Polynomial.X) (Polynomial.C c) = _
  rw [Polynomial.eval₂_C, swapInner_eq_map]

/-- The swap exchanges the two coefficient indices: the `a`-th coefficient of the `k`-th
coefficient of `swapBivar Φ` is the `k`-th coefficient of the `a`-th coefficient of `Φ`. -/
private theorem coeff_coeff_swapBivar (Φ : Polynomial (Polynomial ℤ)) (k a : ℕ) :
    ((swapBivar Φ).coeff k).coeff a = (Φ.coeff a).coeff k := by
  induction Φ using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial b c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, swapBivar_C_mul_X_pow, Polynomial.coeff_mul_C,
      Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : a = b
    · subst h; simp
    · simp [h]

namespace ModularPolynomialData

/-- The transport form of the coefficient-degree bound: with `k` the `Y`-index, every
`X`-coefficient of `Φ_p` has `Y`-degree at most `p + 1`, read off `swapBivar Φ_p = Φ_p` and
`natDegree Φ_p = p + 1`. -/
theorem natDegree_coeff_le_of_swapBivar (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (k : ℕ) : (data.Φ.coeff k).natDegree ≤ p + 1 := by
  have hsymm := swapBivar_eq_of_evalSymm (ModularPolynomialData.evalSymm_of_prime p data)
  have hdeg : data.Φ.natDegree = p + 1 := by
    rw [data.natDegree_eq, dedekindPsi_prime (Fact.out : p.Prime)]
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [← hsymm, coeff_coeff_swapBivar]
  have : data.Φ.coeff a = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact_mod_cast ha)
  rw [this, Polynomial.coeff_zero]

/-- **The coefficient-degree bound.** Every `Y`-coefficient of `Φ_p` has `Y`-degree at most
`p + 1`. -/
theorem natDegree_coeff_le (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (k : ℕ) : (data.Φ.coeff k).natDegree ≤ p + 1 :=
  natDegree_coeff_le_of_swapBivar p data k

end ModularPolynomialData

end ModularCurve

end
