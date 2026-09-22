/-
  T8 — the cone's (c): the descended coefficients of the conjugate product lie in
  `ℚ[jq]`.

  This is the application that R1 was isolated for. The descended coefficients
  `c k` are made `SL₂(ℤ)`-invariant (not merely `Γ₀(ℓ)`-invariant) by the
  **Hecke-coset construction** (base/013 §4.3): the coset polynomial
  `(X - F(ℓτ)) · ∏_{b<ℓ} (X - F((τ+b)/ℓ))` is invariant when `F` is, and its
  coefficients are realized by the Hecke translates of `jq`; T7's headline then
  puts them in `ℚ[jq]`. That is why the level-one q-expansion principle suffices
  and the level-`N` one is never needed.

  FLT provenance, pinned `aa2d8b3`:

  - `P2M/Sol/S_ModularCurve_cosetPoly_smul.lean` (244) — the coset polynomial's
    `SL₂(ℤ)`-invariance, via the action of `SL₂(ℤ)` on `ℙ¹(𝔽_ℓ)`
    (`heckeRep`/`redMatrix`, the four commutation lemmas, `Equiv.prod_comp`);
  - `P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean`
    (281) — realize `c k` by the Hecke translates (the `sigma` embedding of
    `ℚ(ζ_ℓ)` into `ℂ`, `conjC`, `rep`), then apply T7's headline;
  - `P2M/Sol/S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean` (47) —
    the exported application.

  **Deduplication.** FLT's `…hasSum_cosetPoly_coeff.lean` copies the whole
  `RealL` block and the `jt`/`jqC` glue from T7's file. The port imports T7's
  public `RealL` + closure instead (the payoff of T7 exporting it) and keeps only
  the tiny `jt`/`jqC`/`realL_jqC` glue private here. The Hecke matrices come from
  `FLTForHuman.ModularForms.Defs.HeckeOperator` and the translates from
  `FLTForHuman.ModularForms.HeckeQExpansion`.

  The four public statements are verbatim from their `Theorems/` wrappers (so
  they use the wrappers' spelling, per T7's log §7.3); `hasSum_coeff_of_phiGenDescends`
  and all the internal group theory are private.

  Assumes `PhiGen.conj`/`phiProd`/`PhiGenDescends`, `qTwist_coeff`, `coeffMap`,
  `coeffEmb`, `coeffMap_qExpand` and `qExpand_coeff_*` from the port's `Defs/`;
  T6's `hasSum_jq_qParam`; T7's `RealL` closure and headline.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.HeckeQExpansion
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularForms.Hauptmodul

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups ModularForm OnePoint

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

/-! ## The coset polynomial is `SL₂(ℤ)`-invariant

`heckeRep` labels the `ℓ + 1` cosets by `ℙ¹(𝔽_ℓ)`, `redMatrix` is `SL₂(ℤ)`'s
action there (the transpose-inverse mod `ℓ`), and the four commutation lemmas say
that multiplying a coset representative by `SL₂(ℤ)` stays inside the coset
system. Reindexing the product by `Equiv.prod_comp` then gives invariance. -/

namespace CosetPoly

open ModularForm

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

set_option backward.isDefEq.respectTransparency.types false in
private theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

set_option backward.isDefEq.respectTransparency.types false in
private theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

set_option backward.isDefEq.respectTransparency.types false in
private theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

set_option backward.isDefEq.respectTransparency.types false in
private theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0, p * g 0 1; e, g 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section projectiveLine

variable {p : ℕ}

/-- The coset representative labelled by `x ∈ ℙ¹(𝔽_p)`: `heckeDiagMatrix p` at
`∞` and `heckeMatrix p j` at `j`. -/
private def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[scoped simp] private theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[scoped simp] private theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

variable [Fact p.Prime]

/-- `SL₂(ℤ)`'s action on `ℙ¹(𝔽_p)`: the transpose-inverse of `g` mod `p`. -/
private def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p);
      ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) -
            ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p) = 1 by linear_combination this]
      exact one_ne_zero)

@[scoped simp] private theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix (p := p) g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] private theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix (p := p) g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] private theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix (p := p) g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] private theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix (p := p) g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

private instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

private theorem heckeRep_mul (g : SL(2, ℤ)) (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix (p := p) g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    ·
      rw [ite_eq_left (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      exact heckeDiagMatrix_mul_of_eq' hp g e he
    ·
      rw [ite_eq_right (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix (p := p) g 0 0 / redMatrix (p := p) g 1 0 with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      exact heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix (p := p) g 1 0 * j + redMatrix (p := p) g 1 1 = 0
    ·
      rw [ite_eq_left h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      exact heckeMatrix_mul_of_eq' hp g j.val e he
    ·
      rw [ite_eq_right h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix (p := p) g 0 0 * j + redMatrix (p := p) g 0 1) /
        (redMatrix (p := p) g 1 0 * j + redMatrix (p := p) g 1 1) with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
            = redMatrix (p := p) g 1 0 * j + redMatrix (p := p) g 1 1 by
              rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
          hy, div_mul_cancel₀ _ h, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
        ring
      exact heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)

private theorem apply_heckeRep_smul_smul (F : ℍ → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) (g : SL(2, ℤ))
    (x : OnePoint (ZMod p)) (τ : ℍ) :
    F (heckeRep p x • g • τ) = F (heckeRep p (redMatrix (p := p) g • x) • τ) := by
  obtain ⟨g', hmul⟩ := heckeRep_mul g x
  have h1 : heckeRep p x • g • τ = (heckeRep p x * mapGL ℝ g) • τ := by
    rw [mul_smul]; rfl
  have h2 : (mapGL ℝ g' * heckeRep p (redMatrix (p := p) g • x)) • τ
      = g' • heckeRep p (redMatrix (p := p) g • x) • τ := by
    rw [mul_smul]; rfl
  rw [h1, hmul, h2, hF]

end projectiveLine

section reindex

variable {p : ℕ} [NeZero p]

private theorem prod_range_eq_prod_zmod {M : Type} [CommMonoid M] (G : ℕ → M) :
    ∏ j ∈ Finset.range p, G j = ∏ x : ZMod p, G x.val := by
  refine Finset.prod_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val)
    (fun _ _ ↦ Finset.mem_univ _) (fun x _ ↦ Finset.mem_range.mpr x.val_lt)
    (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

private theorem prod_fin_eq_prod_zmod {M : Type} [CommMonoid M] (G : ℕ → M) :
    ∏ b : Fin p, G (b : ℕ) = ∏ x : ZMod p, G x.val := by
  rw [Fin.prod_univ_eq_prod_range, prod_range_eq_prod_zmod]

private theorem cosetPoly_eq_prod_onePoint (F : ℍ → ℂ) (τ : ℍ) :
    (X - C (F (heckeDiagMatrix p • τ))) * ∏ b : Fin p, (X - C (F (heckeMatrix p (b : ℕ) • τ)))
      = ∏ x : OnePoint (ZMod p), (X - C (F (heckeRep p x • τ))) := by
  rw [prod_fin_eq_prod_zmod (fun j ↦ X - C (F (heckeMatrix p j • τ)))]
  exact (Fintype.prod_option (fun x : OnePoint (ZMod p) ↦ X - C (F (heckeRep p x • τ)))).symm

end reindex

private theorem cosetPoly_smul' (ℓ : ℕ) (hℓ : ℓ.Prime) (F : ℍ → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (X - C (F (heckeDiagMatrix ℓ • γ • τ))) * ∏ b : Fin ℓ, (X - C (F (heckeMatrix ℓ (b : ℕ) • γ • τ)))
      = (X - C (F (heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ, (X - C (F (heckeMatrix ℓ (b : ℕ) • τ))) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [cosetPoly_eq_prod_onePoint F (γ • τ), cosetPoly_eq_prod_onePoint F τ]
  calc ∏ x : OnePoint (ZMod ℓ), (X - C (F (heckeRep ℓ x • γ • τ)))
      = ∏ x : OnePoint (ZMod ℓ), (X - C (F (heckeRep ℓ (redMatrix (p := ℓ) γ • x) • τ))) :=
        Finset.prod_congr rfl fun x _ ↦ by rw [apply_heckeRep_smul_smul F hF γ x τ]
    _ = ∏ x : OnePoint (ZMod ℓ), (X - C (F (heckeRep ℓ x • τ))) :=
        Equiv.prod_comp (MulAction.toPerm (redMatrix (p := ℓ) γ)) (fun x ↦ X - C (F (heckeRep ℓ x • τ)))

end CosetPoly

/-- The coset polynomial `(X - F(ℓτ)) · ∏_{b<ℓ} (X - F((τ+b)/ℓ))` is
`SL₂(ℤ)`-invariant whenever `F` is. Stated verbatim from
`Theorems/Thm_ModularCurve_cosetPoly_smul.lean`. -/
theorem cosetPoly_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (F : UpperHalfPlane → ℂ)
    (hF : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • γ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • γ • τ)))
      = (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • τ))) :=
  CosetPoly.cosetPoly_smul' ℓ hℓ F hF γ τ

/-! ## Realizing the descended coefficient

The `σ : ℚ(ζ_ℓ) → ℂ` embedding sends `ζ_ℓ ↦ exp(2πi/ℓ)`, so `conjC` (the
coefficientwise image of `PhiGen.conj`) is realized by the Hecke translates of
`jq`. The `RealL` closure gives the product, and reducing period `ℓ` to `1`
recovers the realization T7's headline consumes. -/

private def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

private abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

private def jqC : LaurentSeries ℂ := coeffMap castC jq

private lemma jqC_coeff (m : ℤ) : jqC.coeff m = ((jq.coeff m : ℚ) : ℂ) := rfl

private lemma realL_jqC : RealL 1 jqC jt := fun τ => hasSum_jq_qParam τ

private lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  E4_cube_div_discriminant_smul γ τ

section Sigma

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

/-- A primitive `ℓ`-th root of unity in `ℂ`, `exp(2πi/ℓ)`. -/
private def expRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓ)

private lemma isPrimitiveRoot_expRoot : IsPrimitiveRoot (expRoot ℓ) ℓ :=
  Complex.isPrimitiveRoot_exp ℓ hℓ.out.ne_zero

/-- The embedding `ℚ(ζ_ℓ) → ℂ` sending `ζ` to `exp(2πi/ℓ)`. -/
private def sigma (ζ : (CyclotomicField ℓ ℚ)ˣ)
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) : CyclotomicField ℓ ℚ →+* ℂ :=
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  ((hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)).symm
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩).toRingHom

variable (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

set_option linter.style.haveILetI false in
private lemma sigma_zeta : sigma ℓ ζ hζ (ζ : CyclotomicField ℓ ℚ) = expRoot ℓ := by
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  let e := hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)
  let r : primitiveRoots ℓ ℂ :=
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζ ℂ
    (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos) (e.symm r)
  have h' : e (e.symm r) = (e.symm r) ↑ζ := h
  rw [Equiv.apply_symm_apply] at h'
  exact h'.symm

omit hℓ in
private lemma sigma_ratCast' (σ : CyclotomicField ℓ ℚ →+* ℂ) (q : ℚ) :
    σ (q : CyclotomicField ℓ ℚ) = (q : ℂ) :=
  map_ratCast σ q

end Sigma

section Translates

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ)
  (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

/-- `PhiGen.conj i` with coefficients pushed to `ℂ` along `σ`. -/
private def conjC (i : Fin (ℓ + 1)) : LaurentSeries ℂ :=
  coeffMap (sigma ℓ ζ hζ) (PhiGen.conj ℓ ζ i)

/-- The coset representative labelled by `i : Fin (ℓ+1)`: the diagonal matrix at
`0` and the `b`-th Hecke matrix at `b+1`. -/
private def rep (i : Fin (ℓ + 1)) : GL (Fin 2) ℝ :=
  Fin.cases (ModularForm.heckeDiagMatrix ℓ) (fun b : Fin ℓ => ModularForm.heckeMatrix ℓ (b : ℕ)) i

omit hℓ in
@[scoped simp] private lemma rep_zero : rep ℓ 0 = ModularForm.heckeDiagMatrix ℓ := by simp [rep]
omit hℓ in
@[scoped simp] private lemma rep_succ (b : Fin ℓ) :
    rep ℓ b.succ = ModularForm.heckeMatrix ℓ (b : ℕ) := by simp [rep]

private lemma realL_conjC_zero :
    RealL ℓ (conjC ℓ ζ hζ 0) (fun τ => jt (ModularForm.heckeDiagMatrix ℓ • τ)) := by
  intro τ
  have h := hasSum_qParam_heckeDiagMatrix_smul ℓ jqC jt realL_jqC τ
  have hconj : conjC ℓ ζ hζ 0 = qExpand ℂ (ℓ * ℓ) jqC := by
    rw [conjC, PhiGen.conj_zero, coeffMap_qExpand]
    congr 1
    ext m
    simp [jqC_coeff, map_ratCast]
  rw [hconj]
  exact h

omit hℓ in
private lemma expRoot_pow_zpow (b : ℕ) (m : ℤ) :
    (expRoot ℓ ^ b) ^ m = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
  rw [expRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  ring

private lemma realL_conjC_succ (b : Fin ℓ) :
    RealL ℓ (conjC ℓ ζ hζ b.succ) (fun τ => jt (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)) := by
  intro τ
  have h := hasSum_qParam_heckeMatrix_smul ℓ (b : ℕ) jqC jt realL_jqC τ
  refine h.congr_fun fun m => ?_
  congr 1
  rw [conjC, PhiGen.conj_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val,
    map_zpow₀, Units.val_pow_eq_pow_val, map_pow, sigma_zeta, expRoot_pow_zpow]
  congr 1
  simp [jqC_coeff, map_ratCast]

private lemma realL_conjC (i : Fin (ℓ + 1)) :
    RealL ℓ (conjC ℓ ζ hζ i) (fun τ => jt (rep ℓ i • τ)) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · simpa only [rep_zero] using realL_conjC_zero ℓ ζ hζ
  · simpa only [rep_succ] using realL_conjC_succ ℓ ζ hζ b

private lemma map_phiProd :
    (PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ)) =
      ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conjC ℓ ζ hζ i)) := by
  rw [PhiGen.phiProd, ← Polynomial.coe_mapRingHom, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [conjC]

private lemma realL_phiProd_coeff (k : ℕ) :
    RealL ℓ (((PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ))).coeff k)
      (fun τ => (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))).coeff k) := by
  rw [map_phiProd]
  exact RealL.coeff_prod_X_sub_C (by exact_mod_cast hℓ.out.pos) Finset.univ
    (fun i _ => realL_conjC ℓ ζ hζ i) k

private lemma realL_one_of_realL_qExpand (x : LaurentSeries ℂ) (F : ℍ → ℂ)
    (hx : RealL ℓ (qExpand ℂ ℓ x) F) : RealL 1 x F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
  have h := hx τ
  rw [← hinj.hasSum_iff] at h
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

private lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap (sigma ℓ ζ hζ) (coeffEmb (CyclotomicField ℓ ℚ) x) = coeffMap castC x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffMap_coeff, eq_ratCast, map_ratCast]
  rfl

include hζ in
/-- The intermediate that turns the descent hypothesis `hc` into the realization
T7's headline consumes: the `k`-th coefficient of the coset polynomial is the
`q`-expansion of `c k`. Kept private; the real consumer is the cone's (d). -/
private theorem hasSum_coeff_of_phiGenDescends (c : ℕ → LaurentSeries ℚ)
    (hc : PhiGen.PhiGenDescends ℓ ζ c) (k : ℕ) (τ : ℍ) :
    HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m)
      (((Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeDiagMatrix ℓ • τ) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeMatrix ℓ (b : ℕ) • τ) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)))).coeff k) := by
  have h1 := realL_phiProd_coeff ℓ ζ hζ k
  rw [Polynomial.coeff_map, hc k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1 τ
  have hprod : (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))) =
      (Polynomial.X - Polynomial.C (jt (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (jt (ModularForm.heckeMatrix ℓ (b : ℕ) • τ))) := by
    rw [Fin.prod_univ_succ]; simp only [rep_zero, rep_succ]
  rw [hprod] at h2
  exact h2

end Translates

end ModularCurve

namespace ModularCurve.PhiGen

/-- The cone's (c): a descended coefficient of the conjugate product `Φ_ℓ` lies
in `ℚ[jq]`. Stated verbatim from
`Theorems/Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean`.

The proof applies T7's headline `mem_adjoin_jq_of_hasSum_of_slash_invariant` to
`c k`, whose realization is `hasSum_coeff_of_phiGenDescends` and whose
`SL₂(ℤ)`-invariance is `cosetPoly_smul` applied to `jt`. -/
theorem mem_adjoin_jq_of_phiGenDescends (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)
    (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) :
    c k ∈ Algebra.adjoin ℚ {jq} := by
  refine mem_adjoin_jq_of_hasSum_of_slash_invariant (c k) _
    (hasSum_coeff_of_phiGenDescends ℓ ζ hζ c hc k) fun γ τ => ?_
  exact congrArg (fun p : Polynomial ℂ => p.coeff k)
    (cosetPoly_smul ℓ hℓ.out jt jt_smul γ τ)

end ModularCurve.PhiGen

end
