/-
  T12 — the properties, concluded: the irreducible symmetric datum.

  The module owns the **symmetry** argument: the transpose engine (`swapBivar` is
  mathlib's `Bivariate.swap`; a coefficient-bounded polynomial has a monic
  transpose of a computable degree), the q-expansion dictionary that reads pole
  bounds as those coefficient bounds, `EvalSymm` and its two conversions to the
  transpose identity, and the transposed evaluation with its minimal polynomial. On
  top of it sits `exists_phiIrreducible_evalSymm`, the cone's own construction: it
  chooses a primitive `ℓ`-th root in `CyclotomicField ℓ ℚ` (mathlib supplies one)
  and runs (a) descent (T11) → (b) integrality (T9) → (c) membership (T8) → T11's
  assembly → irreducibility from the splitting, then symmetry on the main line: the
  descent `(phiProd).coeff k = coeffEmb K ((c k)(q ^ ℓ))` is read off `hc`, T10's
  two pole-bound exports (`phiProd_conj_coeff_zero_lead`,
  `phiProd_conj_coeff_eq_zero_of_le`) give the constant term's leading coefficient
  and the two vanishing bounds, the dictionary turns those into
  `(swapBivar Φ).map evalAtJGen` being monic of degree `ψ(ℓ)`, and the datum
  annihilates `j(q ^ ℓ)`, so the transpose is `Φ` itself by uniqueness of the
  minimal polynomial. It is a join, not new mathematics, and it is T13's entry
  point.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean` (895 lines) for the
  transpose half, `P2M/Sol/S_ModularCurve_swapBivar_eq_of_evalSymm.lean` (95 lines)
  for the converse, `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean`
  (124 lines) and `P2M/Sol/S_ModularCurve_exists_phiIrreducible_evalSymm.lean` (62
  lines). The capstone's statement is the `Theorems/` wrapper of the last verbatim;
  the others contribute the engine and the symmetry argument, which the capstone
  proves.

  ## Assumptions

  `Defs/PhiGen`, `Defs/Polynomial`, `Defs/Fields`, `Defs/Jq`,
  `Defs/BivariateEval` (`ev`, `swap_eq_of_evalSymm`); T10's `PhiGenPoleBounds`;
  T11's `ModularPolynomialAssembly` (the assembly) and `PhiGenDescent`
  (`exists_phiGenDescends`); T9's `PhiGenIntegrality`; T8's
  `ModularForms/PhiGenDescends`; `ModularPolynomialIrreducible` (`phiIrreducible_of_splits`,
  `eval_swap_eq_zero_of_splits`, `minpoly_jqN_eq`, `evalAtJGen_injective`).
  Checked by `spec/check_port.py` through the `spec-pin:` lines below; the module is
  not listed in `spec/old_check_stmts.py`.

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean
  spec-pin: Theorems/Thm_ModularCurve_swapBivar_eq_of_evalSymm.lean
  spec-pin: Theorems/Thm_ModularCurve_swapBivar_monic_of_coeff_bounds.lean
-/
import FLTForHuman.ModularCurve.ModularPolynomialIrreducible
import FLTForHuman.ModularCurve.ModularPolynomialAssembly
import FLTForHuman.ModularCurve.PhiGenDescent
import FLTForHuman.ModularCurve.PhiGenPoleBounds
import FLTForHuman.ModularForms.PhiGenDescends

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve

/-! ## The transpose as mathlib's `Bivariate.swap`

`swapBivar` is mathlib's `Bivariate.swap` as a ring hom on `ℤ[X][Y]`
(`swapBivar_eq_swap`). Keeping that single bridge lets the transpose and symmetry
proofs below cite mathlib's bivariate lemmas instead of re-deriving them, without
touching the `Defs` API. The coefficient-cast evaluation `ev` that mediates between
them, and the converse direction `swap_eq_of_evalSymm`, are in
`Defs/BivariateEval.lean`. -/

section SwapBivarGlue

/-- `swapBivar` is mathlib's `Bivariate.swap`, as ring homs. -/
private theorem swapBivar_eq_swap (Φ : Polynomial (Polynomial ℤ)) :
    swapBivar Φ = Bivariate.swap Φ := by
  have h : swapBivar = (Bivariate.swap (R := ℤ)).toAlgHom.toRingHom :=
    Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _)
      (by simp [Bivariate.swap_X])) (by simp [Bivariate.swap_Y])
  exact RingHom.congr_fun h Φ

end SwapBivarGlue

/-! ## The transpose engine: `swapBivar` of a coefficient-bounded polynomial -/

section SwapBivarEval

/-- The transpose commutes with evaluation: `(swapBivar Φ)(x, y) = Φ(y, x)`.
Mathlib's `Bivariate.aevalAeval_swap`, read through `swapBivar_eq_swap` and the
`ev = aevalAeval` bridge. -/
private theorem swapBivar_eval₂ (Φ : Polynomial (Polynomial ℤ)) (x y : LaurentSeries ℚ) :
    (swapBivar Φ).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x := by
  rw [swapBivar_eq_swap, aeval_toRingHom_eq, aeval_toRingHom_eq]
  change ev (Bivariate.swap Φ) x y = ev Φ y x
  exact ev_swap Φ x y

/-- `swapBivar Φ = Φ` implies `EvalSymm Φ`. -/
theorem evalSymm_of_swapBivar_eq {Φ : Polynomial (Polynomial ℤ)} (h : swapBivar Φ = Φ) :
    EvalSymm Φ := fun x y => by
  conv_lhs => rw [← h]
  exact swapBivar_eval₂ Φ x y

end SwapBivarEval

namespace ModularPolynomialData

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

/-- The transposed `Φ` annihilates `j(q ^ N)` in `ℚ(j(q))[Y]` as soon as `Φ` does
under the swapped evaluation. -/
theorem aeval_jqN_transposeToAdjoin (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0) :
    Polynomial.aeval (jqN N) ((swapBivar data.Φ).map evalAtJGen) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen,
    evalAtJ_def, swapBivar_eval₂, ← evalAtJqN_def]
  exact hswap

end ModularPolynomialData

/-! ## Degree bookkeeping for the transpose -/

section Engine

private theorem swapBivar_C (c : Polynomial ℤ) :
    swapBivar (Polynomial.C c) = c.map Polynomial.C := by
  rw [swapBivar_eq_swap]
  exact Bivariate.swap_C c

private theorem degree_swapBivar_lt {Ψ : Polynomial (Polynomial ℤ)} {D : ℕ}
    (h : ∀ k, (Ψ.coeff k).degree < (D : WithBot ℕ)) :
    (swapBivar Ψ).degree < (D : WithBot ℕ) := by
  conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow Ψ, map_sum]
  refine (Polynomial.degree_sum_le _ _).trans_lt
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe D)).2 fun k _ => ?_)
  rw [map_mul, map_pow, swapBivar_C, swapBivar_X, ← map_pow]
  refine lt_of_le_of_lt (le_trans (Polynomial.degree_mul_le _ _) ?_) (h k)
  calc ((Ψ.coeff k).map Polynomial.C).degree + (Polynomial.C (Polynomial.X ^ k)).degree
      ≤ (Ψ.coeff k).degree + 0 := by
        gcongr
        · exact le_of_eq (Polynomial.degree_map_eq_of_injective Polynomial.C_injective _)
        · exact Polynomial.degree_C_le
    _ = (Ψ.coeff k).degree := add_zero _

/-- A bivariate polynomial whose `Y ^ 0` coefficient is monic of degree `d` and
whose higher coefficients have degree `< d` has a monic transpose of degree `d`.
Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_swapBivar_monic_of_coeff_bounds.lean`. -/
theorem swapBivar_monic_of_coeff_bounds {Φ : Polynomial (Polynomial ℤ)} {d : ℕ}
    (h0 : (Φ.coeff 0).Monic) (h0deg : (Φ.coeff 0).natDegree = d)
    (hk : ∀ k, k ≠ 0 → (Φ.coeff k).degree < (d : WithBot ℕ)) :
    (swapBivar Φ).Monic ∧ (swapBivar Φ).natDegree = d := by
  have hsplit : swapBivar Φ = Polynomial.C Polynomial.X * swapBivar Φ.divX
      + (Φ.coeff 0).map Polynomial.C := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add Φ]
    rw [map_add, map_mul, swapBivar_X, swapBivar_C]
  have hmap : ((Φ.coeff 0).map Polynomial.C).Monic := h0.map _
  have hmapdeg : ((Φ.coeff 0).map Polynomial.C).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmap.ne_zero, h0.natDegree_map, h0deg]
  have hsmall : (Polynomial.C Polynomial.X * swapBivar Φ.divX).degree
      < (d : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    have hX : (Polynomial.C (Polynomial.X : Polynomial ℤ)).degree = 0 :=
      Polynomial.degree_C Polynomial.X_ne_zero
    rw [hX, zero_add]
    exact degree_swapBivar_lt fun k => by
      rw [Polynomial.coeff_divX]; exact hk (k + 1) (Nat.succ_ne_zero k)
  have hlt : (Polynomial.C Polynomial.X * swapBivar Φ.divX).degree
      < ((Φ.coeff 0).map Polynomial.C).degree := by rw [hmapdeg]; exact hsmall
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact hmap.add_of_right hlt
  · rw [hsplit, Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_add_eq_right_of_degree_lt hlt), h0.natDegree_map, h0deg]

end Engine

/-! ## Reading the pole bounds as coefficient bounds -/

section Dictionary

/-- A polynomial whose `q`-expansion vanishes from `-D` down has degree `< D`. -/
theorem degree_lt_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
    (h : ∀ m : ℕ, D ≤ m → (evalAtJ P).coeff (-(m : ℤ)) = 0) :
    P.degree < (D : WithBot ℕ) := by
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe D
  rw [← Polynomial.natDegree_lt_iff_degree_lt hP0]
  by_contra hle
  rw [not_lt] at hle
  have hQdeg : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hcoeff := coeff_aeval_jq_neg (P.map (Int.castRingHom ℚ)) (m := P.natDegree) hQdeg.le
  rw [← evalAtJ_eq_aeval_map, h P.natDegree hle, Polynomial.coeff_map,
    eq_intCast] at hcoeff
  have hlead : P.coeff P.natDegree = 0 := by exact_mod_cast hcoeff.symm
  exact hP0 (Polynomial.leadingCoeff_eq_zero.mp hlead)

/-- A polynomial of degree `≤ D` whose `q`-expansion is `1` at `q ^ (-D)` is
monic of degree `D`. -/
theorem monic_of_evalAtJ_coeff_eq_one {P : Polynomial ℤ} {D : ℕ}
    (hle : P.natDegree ≤ D) (h1 : (evalAtJ P).coeff (-(D : ℤ)) = 1) :
    P.Monic ∧ P.natDegree = D := by
  have hQdeg : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hcoeff := coeff_aeval_jq_neg (P.map (Int.castRingHom ℚ)) (m := D) (hQdeg.le.trans hle)
  rw [← evalAtJ_eq_aeval_map, h1, Polynomial.coeff_map, eq_intCast] at hcoeff
  have hPD : P.coeff D = 1 := by exact_mod_cast hcoeff.symm
  have hge : D ≤ P.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hPD]; exact one_ne_zero)
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one D hle hPD, le_antisymm hle hge⟩

/-- A polynomial whose `q`-expansion vanishes strictly below `-D` has degree `≤ D`. -/
theorem natDegree_le_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
    (h : ∀ m : ℕ, D < m → (evalAtJ P).coeff (-(m : ℤ)) = 0) :
    P.natDegree ≤ D := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  by_contra hlt
  rw [not_le] at hlt
  have hdeg := degree_lt_of_evalAtJ_coeff_eq_zero (P := P) (D := D + 1)
    (fun m hm => h m (by omega))
  rw [← Polynomial.natDegree_lt_iff_degree_lt hP0] at hdeg
  omega

end Dictionary

/-! ## The converse: evaluated symmetry forces `swapBivar Φ = Φ` -/

/-- Evaluated symmetry forces the transpose to be `Φ` itself. Verbatim from the
pin wrapper `Theorems/Thm_ModularCurve_swapBivar_eq_of_evalSymm.lean`. -/
theorem swapBivar_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    swapBivar Φ = Φ := by
  rw [swapBivar_eq_swap, swap_eq_of_evalSymm h]

/-! ## A generic step: coefficients of a level substitution

The lemma mentions no datum, which is why it is extracted; everything else the
symmetry proof needs is a statement about `data` and stays in the main line. -/

/-- A `q ↦ q ^ N` substitution creates and loses no coefficients: the coefficient of
`q ^ (N * m)` in the expanded embedding is the embedding of the `q ^ m`
coefficient. -/
private theorem coeff_coeffEmb_qExpand {L : Type*} [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (f : LaurentSeries ℚ) (m : ℤ) :
    (coeffEmb L (qExpand ℚ N f)).coeff ((N : ℤ) * m) = algebraMap ℚ L (f.coeff m) := by
  rw [coeffEmb_coeff, qExpand_coeff_mul]

/-! ## Existence of an irreducible symmetric datum -/

/-- **The root the descent is run at**: `ℚ(ζ_ℓ)`'s primitive `ℓ`-th root (mathlib's), as a unit with
`ζ ^ ℓ = 1`. Naming it keeps the choice of where the descent happens — which is all the cyclotomic
setup amounts to — out of the existence proof, which then reads as the chain it is. -/
private theorem exists_primitiveRoot_cyclotomic (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    [hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ)] :
    ∃ ζ : (CyclotomicField ℓ ℚ)ˣ,
      IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ ∧ ζ ^ ℓ = 1 := by
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]
    exact hz
  refine ⟨hzu.unit, hζ, ?_⟩
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]

/-- **There is an irreducible symmetric modular polynomial datum at every prime `ℓ`**: run the
descent at the cyclotomic field's primitive root, read off the coefficients' integrality (T9) and
their membership in the `j`-line (T8), assemble the datum (T11), and conclude irreducibility and
symmetry from the splitting (the block's dictionary and `swapBivar_monic_of_coeff_bounds`, then
uniqueness of the minimal polynomial), the latter from T10's pole bounds on the descended family.
The statement is the pin wrapper's
`Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean`; the setup it needs from the field —
cyclotomic, hence finite and Galois — is the three instances below, and the root is
`exists_primitiveRoot_cyclotomic`. -/
theorem exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨ζ, hζ, hζ1⟩ := exists_primitiveRoot_cyclotomic ℓ
  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ ζ hζ
  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc
    (fun k => hc.intCoeffs hζ1 k)
    (fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ ζ hζ c hc k)
  have hsplit : data.Φ.map
        (((coeffEmb (CyclotomicField ℓ ℚ)).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ) := by
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_map, RingHom.comp_apply, RingHom.comp_apply, hcoeff k, hc k]
  have hirr : PhiIrreducible data := PhiGen.phiIrreducible_of_splits ℓ ζ hζ data hsplit
  have hswap : data.Φ.eval₂ (evalAtJqN ℓ) jq = 0 :=
    PhiGen.eval_swap_eq_zero_of_splits ℓ ζ data hsplit
  have h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-((dedekindPsi ℓ : ℕ) : ℤ)) = 1 := by
    rw [hcoeff 0, dedekindPsi_prime hℓ.out]
    refine (algebraMap ℚ (CyclotomicField ℓ ℚ)).injective ?_
    rw [← coeff_coeffEmb_qExpand (N := ℓ), ← hc 0, map_one]
    have hidx : (ℓ : ℤ) * (-((ℓ + 1 : ℕ) : ℤ)) = -((ℓ * ℓ + ℓ : ℕ) : ℤ) := by push_cast; ring
    rw [hidx]
    exact PhiGen.phiProd_conj_coeff_zero_lead ℓ ζ hζ
  have h0le : ∀ m : ℕ, dedekindPsi ℓ < m →
      (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0 := by
    intro m hm
    rw [dedekindPsi_prime hℓ.out] at hm
    rw [hcoeff 0]
    exact hc.poleOrderLE 0 (-(m : ℤ)) (by push_cast; omega)
  have hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi ℓ ≤ m →
      (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0 := by
    intro k hk0 m hm
    rw [dedekindPsi_prime hℓ.out] at hm
    rw [hcoeff k]
    refine (algebraMap ℚ (CyclotomicField ℓ ℚ)).injective ?_
    rw [← coeff_coeffEmb_qExpand (N := ℓ), ← hc k, map_zero]
    have hidx : (ℓ : ℤ) * (-(m : ℤ)) = -((ℓ * m : ℕ) : ℤ) := by push_cast; ring
    rw [hidx]
    exact PhiGen.phiProd_conj_coeff_eq_zero_of_le ℓ ζ k hk0 (ℓ * m)
      (by nlinarith [hℓ.out.two_le])
  obtain ⟨h0monic, h0deg⟩ := monic_of_evalAtJ_coeff_eq_one
    (natDegree_le_of_evalAtJ_coeff_eq_zero h0le) h0top
  obtain ⟨hTmonic, hTdeg⟩ := swapBivar_monic_of_coeff_bounds h0monic h0deg
    fun k hk0 => degree_lt_of_evalAtJ_coeff_eq_zero (hk k hk0)
  have hTmonicGen : ((swapBivar data.Φ).map evalAtJGen).Monic := hTmonic.map evalAtJGen
  have hTdegGen : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi ℓ := by
    rw [hTmonic.natDegree_map]
    exact hTdeg.le
  have hTeq : swapBivar data.Φ = data.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    show (swapBivar data.Φ).map evalAtJGen = data.toAdjoin
    have hdvd : data.toAdjoin ∣ (swapBivar data.Φ).map evalAtJGen := by
      rw [← data.minpoly_jqN_eq hirr]
      exact minpoly.dvd _ _ (data.aeval_jqN_transposeToAdjoin hswap)
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le data.toAdjoin_monic hTmonicGen hdvd ?_
    show ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ (data.Φ.map evalAtJGen).natDegree
    rw [data.monic.natDegree_map, data.natDegree_eq]
    exact hTdegGen
  exact ⟨data, hirr, evalSymm_of_swapBivar_eq hTeq⟩

end ModularCurve

end

