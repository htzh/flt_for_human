/-
The uniqueness, irreducibility and symmetry of the modular polynomial `Φ_N`, and the two
`ModularPolynomialData` rows that read `Φ` at a composite level.

Six facts about the datum `data : ModularPolynomialData N`, which is a monic `Φ ∈
ℤ[X][Y]` of `Y`-degree `ψ(N)` vanishing at `(j(q), j(q ^ N))`:

* `ModularPolynomialData.eq_all` — any two data at the same level are equal. Each
  `toAdjoin` is the minimal polynomial of `j(q ^ N)` (`toAdjoin_eq_minpoly_all`: it is
  monic, it annihilates `j(q ^ N)` because `Φ` does, and its degree is that of the field
  extension), and the coefficient map is injective;
* `phiIrreducible_all` — the datum is irreducible, since `toAdjoin` is a minimal
  polynomial;
* `phiIrreducible_of_prime`, `ModularPolynomialData.evalSymm_of_prime` — at a prime `p`,
  irreducible and symmetric: `exists_phiIrreducible_evalSymm` (resp.
  `exists_modularPolynomialData_evalSymm`) produces such a datum, and the prime-level
  uniqueness `eq_of_prime` identifies the caller's with it;
* `ModularPolynomialData.dvd_resultant_of_mul` — the datum at `ℓ * M` divides the
  resultant of the data at `ℓ` and at `M`;
* `ModularPolynomialData.natDegree_coeff_le`, and the pin's stronger
  `natDegree_coeff_le'` beside it — every `Y`-coefficient of `Φ_p` is of `Y`-degree at
  most `p + 1`.

`toAdjoin_eq_minpoly_all` is the engine and is public: it is what the uniqueness, the
irreducibility and `ModularPolynomialLeadingCoeff`'s leading-coefficient computation all
read. It needs `aeval_jqN_toAdjoin` and `finrank_adjoin_jqN_eq_dedekindPsi`, both imported.

After FLT's `S_ModularCurve_ModularPolynomialData_eq_all.lean`,
`S_ModularCurve_phiIrreducible_of_prime.lean`,
`S_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean` and
`S_ModularCurve_phiIrreducible_all.lean`, pinned at `aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_phiIrreducible_all.lean>.

The last two rows the module hosts are FLT's 134-line
`S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean` and 62-line
`S_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean`: the resultant
divisibility at a composite level and the coefficient-degree bound, both read at their
`Theorems/` wrappers. The divisibility's one structural input is `minpoly_jqN_eq`
(imported); the coefficient bound's two premises are `evalSymm_of_prime` (above) and
`swapBivar_eq_of_evalSymm` (`ModularPolynomialIrreducible.lean`, through `Degree/PhiData`).

spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean
spec-pin: Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean
spec-pin: Theorems/Thm_ModularCurve_phiIrreducible_all.lean
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_all.lean   -- comparable copy: homes `toAdjoin_eq_minpoly_all`
spec-pin: P2M/Sol/S_ModularCurve_phiIrreducible_all.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.Degree.PhiData
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve

/-- The `Y`-degree of the transported datum is `ψ(N)`. Re-derived `private`
(the port's copy in `ModularPolynomialUniqueness.lean` is `private`); the pin's
binder spelling `{N : ℕ} [NeZero N] (data : …)`. -/
private theorem natDegree_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

/-- Every datum at level `N` has `toAdjoin` equal to the minimal polynomial of
`j(q ^ N)`: it is monic, it annihilates `j(q ^ N)`, and its degree is the
minimal one, `ψ(N)`. This is the pin's `toAdjoin_eq_minpoly_all`, the datum's
uniqueness fact, and the statement is the pin's `toAdjoin_eq_minpoly_all`. -/
theorem toAdjoin_eq_minpoly_all (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN N) := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin data⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN N)).natDegree = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_dedekindPsi N
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ (aeval_jqN_toAdjoin data)) ?_
  rw [hdeg, natDegree_toAdjoin]

namespace ModularPolynomialData

/-- Any two modular-polynomial data at the same level `N` are equal: the
transpose `toAdjoin` is always the minimal polynomial of `j(q ^ N)`. Verbatim
from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean`. -/
theorem eq_all (N : ℕ) [NeZero N] (d d' : ModularPolynomialData N) : d = d' := by
  have h : d.Φ = d'.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    change d.toAdjoin = d'.toAdjoin
    rw [toAdjoin_eq_minpoly_all N d, toAdjoin_eq_minpoly_all N d']
  cases d
  cases d'
  cases h
  rfl

/-- At a prime `p` the datum is symmetric. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean`. -/
theorem evalSymm_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) :
    EvalSymm data.Φ := by
  obtain ⟨d, hd⟩ := exists_modularPolynomialData_evalSymm p
  rw [ModularPolynomialData.eq_of_prime p data d]
  exact hd

end ModularPolynomialData

/-- At a prime `p` the datum is irreducible. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean`. -/
theorem phiIrreducible_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) : PhiIrreducible data := by
  obtain ⟨d₀, h, -⟩ := exists_phiIrreducible_evalSymm p
  rwa [ModularPolynomialData.eq_of_prime p data d₀]

/-- At every level `N` the datum is irreducible: `toAdjoin` is the minimal polynomial
of `j(q ^ N)`, and a minimal polynomial is irreducible. Verbatim from
`Theorems/Thm_ModularCurve_phiIrreducible_all.lean`. -/
theorem phiIrreducible_all (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    PhiIrreducible data := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) :=
    ⟨data.toAdjoin, data.toAdjoin_monic, by
      simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin data⟩
  show Irreducible data.toAdjoin
  rw [toAdjoin_eq_minpoly_all N data]
  exact minpoly.irreducible hint

/-! ## The resultant at a composite level

`dvd_resultant_of_mul`: the datum at `ℓ * M` divides the resultant of the data at `ℓ` and
`M`. The proof is one evaluation — at `Ξ : ℤ[X][Y] →+* LaurentSeries ℚ` with `Ξ C = evalAtJ`
and `Ξ X = jqN (ℓ * M)` — of the resultant identity, read over the algebraic closure as a
product over the roots of the level-`ℓ` factor, whose common root with the level-`M` factor
is `jqN ℓ`. -/

/-- `(qExpand ℚ ℓ) ∘ evalAtJ` is evaluation at `j(q ^ ℓ)`, as ring homs
`ℤ[X] → LaurentSeries ℚ`: the two computation lemmas of the pin's `Ξ` are read off
it. `Degree/PhiData.lean` keeps the same statement `private`, and a `private`
declaration cannot be imported, so the home states the form it uses. -/
private theorem qExpand_comp_evalAtJ (ℓ : ℕ) [NeZero ℓ] :
    (qExpand ℚ ℓ).comp evalAtJ
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN ℓ) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

namespace ModularPolynomialData

/-- **The resultant divisibility.** The datum at `ℓ * M` divides the resultant of the
data at `ℓ` and at `M`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean`. -/
theorem dvd_resultant_of_mul
    (ℓ M : ℕ) [NeZero ℓ] [NeZero M]
    (dℓ : ModularPolynomialData ℓ) (dM : ModularPolynomialData M)
    (dN : ModularPolynomialData (ℓ * M)) :
    dN.Φ ∣ (dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))).resultant
      (dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom (Polynomial (Polynomial ℤ))))
        (Polynomial.C Polynomial.X)) := by

  set B := Polynomial (Polynomial ℤ)
  set f : Polynomial B := dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* B) with hf
  set g : Polynomial B := dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom B))
    (Polynomial.C Polynomial.X) with hg
  set R : B := f.resultant g with hR
  set L := LaurentSeries ℚ

  set Ξ : B →+* L := Polynomial.eval₂RingHom evalAtJ (jqN (ℓ * M)) with hΞ
  have hΞC : Ξ.comp Polynomial.C = evalAtJ := RingHom.ext fun a => by
    rw [RingHom.comp_apply, hΞ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  have hΞX : Ξ Polynomial.X = jqN (ℓ * M) := by
    rw [hΞ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

  set f' : Polynomial L := dℓ.Φ.map evalAtJ with hf'
  set g' : Polynomial L := dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom L))
    (Polynomial.C (jqN (ℓ * M))) with hg'
  have hff' : f.map Ξ = f' := by
    rw [hf, Polynomial.map_map, hΞC]
  have hgg' : g.map Ξ = g' := by
    rw [hg, ← Polynomial.coe_mapRingHom, Polynomial.hom_eval₂, hg']
    congr 1
    · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hΞX]

  have hf'm : f'.Monic := dℓ.monic.map _
  have hdegf : f'.natDegree = f.natDegree := by
    rw [hf', hf, dℓ.monic.natDegree_map, dℓ.monic.natDegree_map]

  set z₀ : L := jqN ℓ with hz₀
  have hfz : f'.eval z₀ = 0 := by
    rw [hf', Polynomial.eval_map]
    exact dℓ.eval_eq_zero
  have hgz : g'.eval z₀ = 0 := by
    rw [hg', ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂, Polynomial.coe_evalRingHom,
      Polynomial.eval_C]
    have h1 : (Polynomial.evalRingHom z₀).comp (Polynomial.mapRingHom (Int.castRingHom L)) =
        Polynomial.eval₂RingHom (Int.castRingHom L) z₀ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    rw [h1, ← qExpand_comp_evalAtJ ℓ]
    have h2 : jqN (ℓ * M) = qExpand ℚ ℓ (jqN M) := by
      rw [jqN, jqN, qExpand_qExpand]
    rw [h2, ← Polynomial.hom_eval₂, dM.eval_eq_zero, map_zero]

  have hRes : f'.resultant g' f.natDegree g.natDegree = 0 := by
    set Lb := AlgebraicClosure L
    apply (algebraMap L Lb).injective
    rw [map_zero, ← Polynomial.resultant_map_map]
    have hsplit : (f'.map (algebraMap L Lb)).Splits := IsAlgClosed.splits _
    have hdeg1 : (f'.map (algebraMap L Lb)).natDegree = f.natDegree := by
      rw [Polynomial.natDegree_map, hdegf]
    have hdeg2 : (g'.map (algebraMap L Lb)).natDegree ≤ g.natDegree := by
      rw [Polynomial.natDegree_map, ← hgg']
      exact Polynomial.natDegree_map_le
    rw [← hdeg1, Polynomial.resultant_eq_prod_eval _ _ _ hdeg2 hsplit]
    have hz : algebraMap L Lb z₀ ∈ (f'.map (algebraMap L Lb)).roots := by
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf'm.ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map, Polynomial.eval₂_hom, hfz, map_zero]
    have hz' : Polynomial.eval (algebraMap L Lb z₀) (g'.map (algebraMap L Lb)) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hgz, map_zero]
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, hz, hz'⟩), mul_zero]
  have hΞR : Ξ R = 0 := by
    rw [hR, ← Polynomial.resultant_map_map, hff', hgg']
    exact hRes

  set θ : B →+* Polynomial ℚ⟮jq⟯ := Polynomial.mapRingHom evalAtJGen with hθ
  have hθinj : Function.Injective θ := Polynomial.map_injective _ evalAtJGen_injective
  have haeval : Polynomial.aeval (jqN (ℓ * M)) (θ R) = 0 := by
    rw [hθ, Polynomial.coe_mapRingHom, Polynomial.aeval_def, Polynomial.eval₂_map,
      algebraMap_comp_evalAtJGen]
    exact hΞR
  have hmin : minpoly ℚ⟮jq⟯ (jqN (ℓ * M)) = θ dN.Φ := by
    rw [dN.minpoly_jqN_eq (phiIrreducible_all _ dN)]
    rfl
  have hdvd : θ dN.Φ ∣ θ R := by
    rw [← hmin]
    exact minpoly.dvd _ _ haeval

  rw [← Polynomial.modByMonic_eq_zero_iff_dvd dN.monic]
  apply hθinj
  rw [map_zero, hθ, Polynomial.coe_mapRingHom, Polynomial.map_modByMonic _ dN.monic,
    Polynomial.modByMonic_eq_zero_iff_dvd (dN.monic.map _)]
  exact hdvd

end ModularPolynomialData

/-! ## The transpose of `Φ_p` and its coefficient-degree bound

`natDegree_coeff_le`: every `Y`-coefficient of `Φ_p` has `Y`-degree at most `p + 1`. The
proof transports the bound through `swapBivar` (`swapInner_eq_map`,
`swapBivar_C_mul_X_pow`, `coeff_coeff_swapBivar`) and then reads
`swapBivar Φ = Φ` off the two ported premises, `evalSymm_of_prime` and
`swapBivar_eq_of_evalSymm`. The three `swapBivar` bookkeeping lemmas are `private`: they
are the pin's local helpers, used only by the headline below. -/

/-- The inner map of the swap is the coefficient map `c ↦ c.map C`: both send
`X` to the constant polynomial `X`. -/
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
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial b c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, swapBivar_C_mul_X_pow, Polynomial.coeff_mul_C,
      Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : a = b
    · subst h; simp
    · simp [h]

namespace ModularPolynomialData

/-- The pin's stronger form of the coefficient-degree bound: with `k` the
`Y`-index, every `X`-coefficient of `Φ_p` has `Y`-degree at most `p + 1`. The
bound comes from `swapBivar Φ_p = Φ_p` (`swapBivar_eq_of_evalSymm` at
`evalSymm_of_prime`) and `natDegree Φ_p = p + 1`. -/
theorem natDegree_coeff_le' (p : ℕ) [Fact p.Prime]
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

/-- **The coefficient-degree bound.** Every `Y`-coefficient of `Φ_p` has `Y`-degree at
most `p + 1`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean`. -/
theorem natDegree_coeff_le (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (k : ℕ) : (data.Φ.coeff k).natDegree ≤ p + 1 :=
  natDegree_coeff_le' p data k

end ModularPolynomialData

end ModularCurve

end

#print axioms ModularCurve.ModularPolynomialData.eq_all
#print axioms ModularCurve.phiIrreducible_of_prime
#print axioms ModularCurve.phiIrreducible_all
#print axioms ModularCurve.ModularPolynomialData.evalSymm_of_prime
#print axioms ModularCurve.ModularPolynomialData.dvd_resultant_of_mul
#print axioms ModularCurve.ModularPolynomialData.natDegree_coeff_le'
#print axioms ModularCurve.ModularPolynomialData.natDegree_coeff_le
