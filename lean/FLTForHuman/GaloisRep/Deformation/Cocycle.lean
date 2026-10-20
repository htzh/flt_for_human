/-
  The cocycle engine of the descent: Poincaré averaging, Hilbert 90 for `GLₙ`, the PGLₙ
  adjustment, Schur uniqueness and the Galois bookkeeping.

  Piece two of the pin node
  `Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
  (pinned `aa2d8b3`), taken whole: pin lines 319–903, the `section PieceDCS` and
  `section PieceSUA` of the `S_` file (re-cut by piece group, §4 of the work order).

  What it establishes. For a finite Galois extension `L/K`, a *cocycle* is
  `c : Gal(L/K) → GL n L` with `c (σ * τ) = c σ * mapGLn σ (c τ)` (`IsGLnCocycle`), a
  *coboundary* is `c σ = B * mapGLn σ B⁻¹` (`IsGLnCoboundary`), and `mapGLn` is the action of
  `Gal(L/K)` on `GL n L` through `Matrix.GeneralLinearGroup.map`
  (`mapGLn_one`, `mapGLn_mul`). Every coboundary is a cocycle, and
  `exists_isGLnCoboundary_of_isGLnCocycle` is the converse — Hilbert 90 for `GLₙ(L)`, so
  `isGLnCocycle_iff_isGLnCoboundary`. The proof is the pin's: the Poincaré sum
  `glnPoincare c M = ∑ σ, c σ * M.map σ` and its column form `glnPoincareVec`
  (`glnPoincare_col`) are `c`-fixed (`glnPoincare_cocycle_fixed`); column-vector spanning
  (`glnPoincareVec_span_eq_top`) follows from Dedekind independence of the characters
  (`linearIndependent_monoidHom`, mathlib) through the dual-functional argument of
  `eq_zero_of_forall_dotProduct_glnPoincareVec`; a Poincaré sum with non-zero determinant
  `exists_glnPoincare_det_ne_zero` then gives the coboundary.

  The PGLₙ adjustment. `glnTwistedNorm σ d Q = ∏_{k<d} (map σ)^[k] Q` — with its recursive
  characterisation `glnTwistedNorm_zero`/`_succ` — is the twisted norm of `Q`. Its scalar
  computation is `glnTwistedNorm_scalarGL`; `glnTwistedNorm_scalarAdjust` is the pin's
  cancellation `glnTwistedNorm σ d (scalarGL μ⁻¹ * Q) = 1` when `glnTwistedNorm σ d Q` is the
  scalar `λ = ∏_{k<d} (map σ)^[k] μ`. The private `scalarGL` block (`scalarGL_mul`,
  `scalarGL_one`, `map_scalarGL`, `iterate_map_scalarGL`, `scalarGL_mul_comm`) is the scalar-unit
  bookkeeping the pin keeps private, kept private here.

  Schur uniqueness (`PieceSUA`). `mem_center_of_commute_span_top` and
  `exists_scalar_of_commute_span_top`: a unit commuting with a spanning set of matrices is a
  scalar (`GeneralLinearGroup.center_eq_range_scalar`, mathlib); `exists_scalar_of_conjRep_eq`
  turns two conjugators of the same representation into a scalar multiple. `IsConjugatorFamily`
  is the pointwise conjugacy family for a single generator twist,
  `conjugatorFamily_twoFactor` computes the defect of `σ ↦ Q σ * mapGLn σ (Q τ)`, and
  `exists_scalar_conjugatorCocycleDefect` says the family is a cocycle up to scalars.
  `algebraMapRange_hgal` and `algebraMapRange_hfix` are the two Galois facts about
  `⊤`-fixed points of `L →+* L` (that every such automorphism fixing `algebraMap K L`'s range is
  an alg-equiv, and, when `IsGalois K L`, that a point fixed by all of them lies in the range),
  and `descentConjugatorSupply_algebraMapRange_of_isConjugatorCocycle` wires them to the
  `DescentConjugatorSupply` of `Deformation/Charpoly.lean`.

  Source (pinned `aa2d8b3`):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean#L319-L903>;
  statement authority
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean>.

  Assumes: `Deformation/Charpoly.lean` of this port (`DescentConjugatorSupply`,
  `noSchurIndex_of_descentConjugatorSupply`, `entries_mem_of_forall_map_conj_eq`) and
  mathlib `v4.34.0`.

  Mathlib-first (2026-10-20, `rg` under `.lake/packages/mathlib/Mathlib`):
  * `Fintype (L ≃ₐ[K] L)` — **hit**, mathlib's `AlgEquiv.fintype` instance
    (`FieldTheory/Fixed.lean:323`), which the pin's blanket `import Mathlib` supplied; this module
    imports `Mathlib.FieldTheory.Fixed` for it. Without it every `∑ σ : L ≃ₐ[K] L` in the Poincaré
    sums fails to elaborate;
  * `linearIndependent_monoidHom` (`LinearAlgebra/LinearIndependent/Basic.lean:502`) — **hit**,
    imported and used for Dedekind independence in `eq_zero_of_forall_dotProduct_glnPoincareVec`;
  * `Submodule.exists_dual_map_eq_bot_of_lt_top` (`LinearAlgebra/Dual/Lemmas.lean:366`) and
    `Submodule.exists_fun_fin_finrank_span_eq` (`LinearAlgebra/Dimension/StrongRankCondition.lean:650`)
    — **hits**, used in `glnPoincareVec_span_eq_top` and `exists_glnPoincare_det_ne_zero`;
  * `Matrix.exists_mulVec_eq_zero_iff` (`LinearAlgebra/Matrix/ToLinearEquiv.lean:163`) — **hit**,
    the determinant-to-kernel step of `det_ne_zero_of_linearIndependent_cols`;
  * `GeneralLinearGroup.center_eq_range_scalar` — **hit**, used in `exists_scalar_of_commute_span_top`
    and in the private `scalarGL` block; `MulAut.conj` is the conjugation vocabulary but conjugates
    group elements, not representations, so `conjRep`/`IsConjugatorFamily` stay the pin's;
  * `Algebra.IsAlgebraic.algEquivEquivAlgHom` (`RingTheory/Algebraic/Basic.lean:525`) and
    `IsGalois.mem_range_algebraMap_iff_fixed` (`FieldTheory/Galois/Basic.lean:340`) — **hits**, the
    two ingredients of `algebraMapRange_hgal`/`algebraMapRange_hfix`;
  * Hilbert 90 for `GLₙ`: **negative**. Mathlib's `Hilbert90`
    (`RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`) states Noether's
    generalization for `G`-modules and Hilbert 90 for `Lˣ` (its `Hilbert90.aux_ne_zero` is the
    scalar analogue of the pin's `eq_zero_of_forall_dotProduct_glnPoincareVec`); there is no
    `GLₙ(L)` cocycle/coboundary API, so `IsGLnCocycle`, `IsGLnCoboundary`,
    `exists_isGLnCoboundary_of_isGLnCocycle` and `isGLnCocycle_iff_isGLnCoboundary` are proved here;
  * `glnPoincare`, `glnPoincareVec`, `glnTwistedNorm`, `scalarGL`, `IsConjugatorCocycle`,
    `IsConjugatorFamily` and their lemmas — **negative** (mathlib's `Algebra.norm_eq_prod_automorphisms`
    and `Algebra.trace_eq_sum_automorphisms` are the scalar norms/traces, not these matrix
    constructions), as are `mapGLn_one`/`mapGLn_mul` as statements (they are `map`-functoriality of
    the pin's `mapGLn`, whose mathlib carrier `Matrix.GeneralLinearGroup.map` is imported).

  Drift against `v4.34.0` — no statement, binder or name changed; 0 warnings:
  * `import Mathlib.FieldTheory.Fixed` and `Mathlib.FieldTheory.Galois.Basic` added (the
    `AlgEquiv.fintype` instance and `IsGalois`, both supplied in the pin by `import Mathlib`);
  * `simp [if_neg hij]` → `simp [ite_eq_right hij]` in `map_scalarGL` (the `if_neg` deprecation);
  * two `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` in `mem_center_of_commute_span_top`;
  * `convert hcomp using 1; rfl; rfl` → `convert hcomp using 1; rfl` in
    `eq_zero_of_forall_dotProduct_glnPoincareVec` (`convert` closes both goals at `v4.34.0`);
  * `exists_glnPoincare_det_ne_zero`: the matrix `fun i j => v j i` is bound as
    `set M : Matrix n n L := …` before the `glnPoincare_col` rewrite — at `v4.34.0` the rewrite's
    pattern is not type-correct at implicit transparency when the argument is the bare lambda.
    This is a proof edit; the declaration's statement is the pin's;
  * the pin's `p2m_*` scaffolding and `P2MW.S_…` wrapper namespace are dropped as in
    `Deformation/Charpoly.lean`, and `import Mathlib` / `import P2M.Util` are not carried.

  spec-pin: Theorems/Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean
  spec-pin: P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean
-/

import FLTForHuman.GaloisRep.Deformation.Charpoly
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Group

set_option autoImplicit false

universe u v

noncomputable section

open Matrix

namespace DeligneSerre

section Cocycle

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : Type*} [DecidableEq n] [Fintype n]

abbrev mapGLn (σ : L ≃ₐ[K] L) : GeneralLinearGroup n L →* GeneralLinearGroup n L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

omit [FiniteDimensional K L] in
@[scoped simp] theorem mapGLn_one (g : GeneralLinearGroup n L) : mapGLn (1 : L ≃ₐ[K] L) g = g := by
  apply Units.ext
  show (g : Matrix n n L).map ((1 : L ≃ₐ[K] L) : L →+* L) = (g : Matrix n n L)
  ext i j; simp

omit [FiniteDimensional K L] in
theorem mapGLn_mul (σ τ : L ≃ₐ[K] L) (g : GeneralLinearGroup n L) :
    mapGLn (σ * τ) g = mapGLn σ (mapGLn τ g) := by
  apply Units.ext
  show (g : Matrix n n L).map ((σ * τ : L ≃ₐ[K] L) : L →+* L) =
    ((g : Matrix n n L).map ((τ : L ≃ₐ[K] L) : L →+* L)).map ((σ : L ≃ₐ[K] L) : L →+* L)
  ext i j; simp

def IsGLnCocycle (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L) : Prop :=
  ∀ σ τ, c (σ * τ) = c σ * mapGLn σ (c τ)

def IsGLnCoboundary (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L) : Prop :=
  ∃ B : GeneralLinearGroup n L, ∀ σ, c σ = B * (mapGLn σ B)⁻¹

omit [FiniteDimensional K L] in
theorem isGLnCocycle_one_eq_one {c : (L ≃ₐ[K] L) → GeneralLinearGroup n L}
    (hc : IsGLnCocycle c) : c 1 = 1 := by
  have h := hc 1 1
  rw [mul_one, mapGLn_one] at h
  nth_rewrite 1 [← one_mul (c 1)] at h
  exact (mul_right_cancel h).symm

omit [FiniteDimensional K L] in
theorem IsGLnCoboundary.isGLnCocycle {c : (L ≃ₐ[K] L) → GeneralLinearGroup n L}
    (hc : IsGLnCoboundary c) : IsGLnCocycle c := by
  obtain ⟨B, hB⟩ := hc
  intro σ τ
  rw [hB, hB, hB, map_mul, map_inv, mapGLn_mul]
  group

end Cocycle

section Poincare

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L)

def glnPoincare (M : Matrix n n L) : Matrix n n L :=
  ∑ σ : L ≃ₐ[K] L, (c σ : Matrix n n L) * M.map (σ : L →+* L)

def glnPoincareVec (v : n → L) : n → L :=
  ∑ σ : L ≃ₐ[K] L, (c σ : Matrix n n L) *ᵥ (fun i => (σ : L →+* L) (v i))

theorem glnPoincare_col (M : Matrix n n L) (j : n) :
    (fun i => glnPoincare c M i j) = glnPoincareVec c (fun i => M i j) := by
  funext i
  show (∑ σ : L ≃ₐ[K] L, (c σ : Matrix n n L) * M.map (σ : L →+* L)) i j
    = (∑ σ : L ≃ₐ[K] L, (c σ : Matrix n n L) *ᵥ (fun k => (σ : L →+* L) (M k j))) i
  rw [Matrix.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_apply, Matrix.mulVec]
  simp only [dotProduct, Matrix.map_apply]

theorem glnPoincare_cocycle_fixed (hc : IsGLnCocycle c) (τ : L ≃ₐ[K] L) (M : Matrix n n L) :
    (c τ : Matrix n n L) * (glnPoincare c M).map (τ : L →+* L) = glnPoincare c M := by
  simp only [glnPoincare]

  rw [show ((∑ σ : L ≃ₐ[K] L, (c σ : Matrix n n L) * M.map (σ : L →+* L)).map (τ : L →+* L))
      = ∑ σ : L ≃ₐ[K] L, ((c σ : Matrix n n L) * M.map (σ : L →+* L)).map (τ : L →+* L) from
    map_sum (RingHom.mapMatrix (τ : L →+* L)) _ Finset.univ]
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (fun σ => τ * σ) (Group.mulLeft_bijective τ) _ _ (fun σ => ?_)

  have hmap : ((c σ : Matrix n n L) * M.map (σ : L →+* L)).map (τ : L →+* L)
      = ((c σ : Matrix n n L).map (τ : L →+* L)) * (M.map ((τ * σ : L ≃ₐ[K] L) : L →+* L)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    rfl
  rw [hmap, ← Matrix.mul_assoc]

  have hcoc' : (c (τ * σ) : Matrix n n L)
      = (c τ : Matrix n n L) * (c σ : Matrix n n L).map (τ : L →+* L) := by
    rw [hc τ σ, Units.val_mul]; rfl
  rw [← hcoc']

end Poincare

section Dedekind

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L)

theorem dotProduct_glnPoincareVec (lam v : n → L) :
    lam ⬝ᵥ glnPoincareVec c v
      = ∑ σ : L ≃ₐ[K] L, (lam ᵥ* (c σ : Matrix n n L)) ⬝ᵥ (fun i => (σ : L →+* L) (v i)) := by
  simp only [glnPoincareVec, dotProduct_sum, dotProduct_mulVec]

theorem eq_zero_of_forall_dotProduct_glnPoincareVec (hc : IsGLnCocycle c)
    {lam : n → L} (h : ∀ v, lam ⬝ᵥ glnPoincareVec c v = 0) : lam = 0 := by

  have hk : ∀ k, ∀ x : L, ∑ σ : L ≃ₐ[K] L,
      (lam ᵥ* (c σ : Matrix n n L)) k * (σ : L →+* L) x = 0 := by
    intro k x
    have hx := h (Pi.single k x)
    rw [dotProduct_glnPoincareVec] at hx
    refine .trans (Finset.sum_congr rfl fun σ _ => ?_) hx
    have hsingle : (fun i => (σ : L →+* L) ((Pi.single k x : n → L) i))
        = (Pi.single k ((σ : L →+* L) x) : n → L) := by
      funext i
      rcases eq_or_ne i k with rfl | hik
      · simp
      · simp [Pi.single_eq_of_ne hik]
    rw [hsingle, dotProduct_single]

  have hLI : LinearIndependent L (fun σ : L ≃ₐ[K] L => ((σ : L →+* L) : L → L)) := by
    have hbase := linearIndependent_monoidHom L L
    have hcomp := hbase.comp (fun σ : L ≃ₐ[K] L => ((σ : L →+* L) : L →* L))
      (fun σ τ heq => by ext x; exact DFunLike.congr_fun heq x)
    convert hcomp using 1
    rfl

  funext k
  have hcoef : ∀ σ : L ≃ₐ[K] L, (lam ᵥ* (c σ : Matrix n n L)) k = 0 := by
    intro σ
    have hsum : (∑ τ : L ≃ₐ[K] L,
        (lam ᵥ* (c τ : Matrix n n L)) k • ((τ : L →+* L) : L → L)) = 0 := by
      funext x
      simpa using hk k x
    have := linearIndependent_iff'.mp hLI Finset.univ
      (fun τ => (lam ᵥ* (c τ : Matrix n n L)) k) hsum σ (Finset.mem_univ σ)
    exact this

  have h1 := hcoef 1
  rw [isGLnCocycle_one_eq_one hc] at h1
  simpa using h1

end Dedekind

section Span

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L)

private theorem eq_sum_single (w : n → L) :
    w = ∑ i, w i • (Pi.single i 1 : n → L) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij.symm, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

private theorem exists_row_of_dual_ne_zero {f : Module.Dual L (n → L)} (hf : f ≠ 0) :
    ∃ lam : n → L, lam ≠ 0 ∧ ∀ v, f v = lam ⬝ᵥ v := by
  refine ⟨fun i => f (Pi.single i 1), ?_, fun v => ?_⟩
  · intro hcon
    apply hf
    refine LinearMap.ext fun v => ?_
    rw [eq_sum_single v, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : f (Pi.single i 1) = 0 := congrFun hcon i
    rw [map_smul, hi, smul_zero]
  · conv_lhs => rw [eq_sum_single v, map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct, mul_comm]

theorem glnPoincareVec_span_eq_top (hc : IsGLnCocycle c) :
    Submodule.span L (Set.range (glnPoincareVec c)) = ⊤ := by
  by_contra hcon

  have hlt : Submodule.span L (Set.range (glnPoincareVec c)) < ⊤ := lt_top_iff_ne_top.mpr hcon
  obtain ⟨f, hf, hker⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance

  obtain ⟨lam, hlam, hflam⟩ := exists_row_of_dual_ne_zero hf

  have hvan : ∀ v, lam ⬝ᵥ glnPoincareVec c v = 0 := by
    intro v
    rw [← hflam]
    have hmem : glnPoincareVec c v ∈ Submodule.span L (Set.range (glnPoincareVec c)) :=
      Submodule.subset_span ⟨v, rfl⟩
    have : f (glnPoincareVec c v) ∈ (⊥ : Submodule L L) := by
      rw [← hker]; exact Submodule.mem_map_of_mem hmem
    simpa using this

  exact hlam (eq_zero_of_forall_dotProduct_glnPoincareVec c hc hvan)

end Span

section Invertible

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L)

private theorem det_ne_zero_of_linearIndependent_cols {B : Matrix n n L}
    (hB : LinearIndependent L (fun j i => B i j)) : B.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  have hcomb : ∑ j, v j • (fun i => B i j) = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hv i
  exact hvne (funext fun j =>
    linearIndependent_iff'.mp hB Finset.univ v hcomb j (Finset.mem_univ j))

theorem exists_glnPoincare_det_ne_zero (hc : IsGLnCocycle c) :
    ∃ M : Matrix n n L, (glnPoincare c M).det ≠ 0 := by
  classical

  have hspan := glnPoincareVec_span_eq_top c hc
  have hdim : Module.finrank L (Submodule.span L (Set.range (glnPoincareVec c)))
      = Fintype.card n := by
    rw [hspan, finrank_top, Module.finrank_fintype_fun_eq_card]
  have : Module.Finite L
      (Submodule.span L (Set.range (glnPoincareVec c)) : Submodule L (n → L)) :=
    inferInstance
  obtain ⟨f, hfmem, _, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq L (Set.range (glnPoincareVec c))

  let e : n ≃ Fin (Module.finrank L (Submodule.span L (Set.range (glnPoincareVec c)))) :=
    (Fintype.equivFinOfCardEq rfl).trans (finCongr hdim.symm)

  have hchoice : ∀ j : n, ∃ v, glnPoincareVec c v = f (e j) := fun j => hfmem (e j)
  choose v hv using hchoice

  set M : Matrix n n L := fun i j => v j i with hM
  refine ⟨M, ?_⟩
  refine det_ne_zero_of_linearIndependent_cols ?_
  have hcols : ∀ j, (fun i => glnPoincare c M i j) = f (e j) := by
    intro j
    rw [glnPoincare_col]
    exact hv j
  rw [show (fun (j : n) (i : n) => glnPoincare c M i j) = f ∘ e from
    funext fun j => hcols j]
  exact hfLI.comp e e.injective

end Invertible

section Hilbert90

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : Type*} [DecidableEq n] [Fintype n]

theorem exists_isGLnCoboundary_of_isGLnCocycle
    (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L) (hc : IsGLnCocycle c) :
    IsGLnCoboundary c := by
  obtain ⟨M, hM⟩ := exists_glnPoincare_det_ne_zero c hc

  have hBunit : IsUnit (glnPoincare c M) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hM)
  set B : GeneralLinearGroup n L := hBunit.unit with hBdef
  refine ⟨B, fun σ => ?_⟩

  have hfix : (c σ : Matrix n n L) * (glnPoincare c M).map (σ : L →+* L) = glnPoincare c M :=
    glnPoincare_cocycle_fixed c hc σ M
  have hmapval : (mapGLn σ B : Matrix n n L) = (glnPoincare c M).map (σ : L →+* L) := by
    show (B : Matrix n n L).map (σ : L →+* L) = _
    rw [hBdef, hBunit.unit_spec]
  have hmul : (c σ * mapGLn σ B : GeneralLinearGroup n L) = B := by
    apply Units.ext
    simp only [Units.val_mul, hBdef, hBunit.unit_spec]
    rw [hmapval]; exact hfix
  rw [eq_mul_inv_iff_mul_eq]
  exact hmul

theorem isGLnCocycle_iff_isGLnCoboundary
    (c : (L ≃ₐ[K] L) → GeneralLinearGroup n L) :
    IsGLnCocycle c ↔ IsGLnCoboundary c :=
  ⟨exists_isGLnCoboundary_of_isGLnCocycle c, IsGLnCoboundary.isGLnCocycle⟩

end Hilbert90

section PGLnAdjust

variable {L : Type*} [Field L] {n : Type*} [DecidableEq n] [Fintype n]

def glnTwistedNorm (σ : L →+* L) : ℕ → GeneralLinearGroup n L → GeneralLinearGroup n L
  | 0, _ => 1
  | (d + 1), Q => glnTwistedNorm σ d Q * (Matrix.GeneralLinearGroup.map σ)^[d] Q

@[scoped simp] theorem glnTwistedNorm_zero (σ : L →+* L) (Q : GeneralLinearGroup n L) :
    glnTwistedNorm σ 0 Q = 1 := rfl

theorem glnTwistedNorm_succ (σ : L →+* L) (d : ℕ) (Q : GeneralLinearGroup n L) :
    glnTwistedNorm σ (d + 1) Q
      = glnTwistedNorm σ d Q * (Matrix.GeneralLinearGroup.map σ)^[d] Q := rfl

private def scalarGL (μ : Lˣ) : GeneralLinearGroup n L := μ • (1 : GeneralLinearGroup n L)

private theorem scalarGL_mul (μ ν : Lˣ) :
    (scalarGL (n := n) μ) * (scalarGL ν) = scalarGL (μ * ν) := by
  apply Units.ext
  simp only [scalarGL, Units.val_mul]
  show ((μ : L) • (1 : Matrix n n L)) * ((ν : L) • (1 : Matrix n n L))
    = ((μ : L) * (ν : L)) • (1 : Matrix n n L)
  rw [smul_mul_smul_comm, one_mul]

private theorem scalarGL_one : (scalarGL (n := n) (1 : Lˣ)) = 1 := by
  apply Units.ext
  simp only [scalarGL]
  show ((1 : Lˣ) : L) • (1 : Matrix n n L) = 1
  simp

private theorem map_scalarGL (σ : L →+* L) (μ : Lˣ) :
    Matrix.GeneralLinearGroup.map (n := n) σ (scalarGL μ)
      = scalarGL (Units.map (σ : L →* L) μ) := by
  apply Units.ext
  show ((scalarGL μ : GeneralLinearGroup n L) : Matrix n n L).map σ = _
  ext i j
  simp only [scalarGL, Matrix.map_apply]
  show σ (((μ : L) • (1 : Matrix n n L)) i j)
    = (((Units.map (σ : L →* L) μ : Lˣ) : L) • (1 : Matrix n n L)) i j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Units.coe_map,
    MonoidHom.coe_coe]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [ite_eq_right hij]

private theorem iterate_map_scalarGL (σ : L →+* L) (k : ℕ) (μ : Lˣ) :
    (Matrix.GeneralLinearGroup.map (n := n) σ)^[k] (scalarGL μ)
      = scalarGL ((Units.map (σ : L →* L))^[k] μ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.iterate_succ', Function.comp_apply,
      Function.comp_apply, ih, map_scalarGL]

private theorem scalarGL_mul_comm (μ : Lˣ) (Q : GeneralLinearGroup n L) :
    scalarGL μ * Q = Q * scalarGL μ := by
  apply Units.ext
  simp only [scalarGL, Units.val_mul]
  show ((μ : L) • (1 : Matrix n n L)) * (Q : Matrix n n L)
    = (Q : Matrix n n L) * ((μ : L) • (1 : Matrix n n L))
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem glnTwistedNorm_scalarGL (σ : L →+* L) (d : ℕ) (μ : Lˣ) :
    glnTwistedNorm (n := n) σ d (scalarGL μ)
      = scalarGL (∏ k ∈ Finset.range d, (Units.map (σ : L →* L))^[k] μ) := by
  induction d with
  | zero => simp [scalarGL_one]
  | succ d ih =>
    rw [glnTwistedNorm_succ, Finset.prod_range_succ, ih, iterate_map_scalarGL, scalarGL_mul]

theorem glnTwistedNorm_scalarAdjust (σ : L →+* L) (d : ℕ) (Q : GeneralLinearGroup n L)
    (lam μ : Lˣ) (hQ : glnTwistedNorm σ d Q = scalarGL lam)
    (hμ : ∏ k ∈ Finset.range d, (Units.map (σ : L →* L))^[k] μ = lam) :
    glnTwistedNorm σ d (scalarGL μ⁻¹ * Q) = 1 := by

  have hsplit : ∀ d, glnTwistedNorm σ d (scalarGL μ⁻¹ * Q)
      = glnTwistedNorm (n := n) σ d (scalarGL μ⁻¹) * glnTwistedNorm σ d Q := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      simp only [glnTwistedNorm_succ]
      rw [ih, iterate_map_mul, mul_assoc, mul_assoc]
      congr 1
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      rw [iterate_map_scalarGL, scalarGL_mul_comm]
  rw [hsplit, glnTwistedNorm_scalarGL, hQ]
  have hinv : (∏ k ∈ Finset.range d, (Units.map (σ : L →* L))^[k] μ⁻¹) = lam⁻¹ := by
    rw [← hμ, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp
  rw [hinv, scalarGL_mul, inv_mul_cancel, scalarGL_one]

end PGLnAdjust

section Wire

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable {G : Type*} [Group G]

def IsConjugatorCocycle (φ : G →* GeneralLinearGroup n L)
    (Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L) : Prop :=
  IsGLnCocycle Q ∧ ∀ σ g, ((Q σ)⁻¹ * φ g * Q σ : Matrix n n L)
    = (φ g : Matrix n n L).map (σ : L →+* L)

theorem exists_galFixed_conj_of_isConjugatorCocycle
    (φ : G →* GeneralLinearGroup n L) (Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L)
    (hQ : IsConjugatorCocycle φ Q) :
    ∃ B : GeneralLinearGroup n L, ∀ σ : L ≃ₐ[K] L, ∀ g,
      (B⁻¹ * φ g * B : Matrix n n L)
        = ((B⁻¹ * φ g * B : GeneralLinearGroup n L) : Matrix n n L).map (σ : L →+* L) := by
  obtain ⟨B, hB⟩ := exists_isGLnCoboundary_of_isGLnCocycle Q hQ.1
  refine ⟨B, fun σ g => ?_⟩

  have hconjGL : (Q σ)⁻¹ * φ g * Q σ = mapGLn σ (φ g) := by
    apply Units.ext
    exact hQ.2 σ g
  have key : mapGLn σ (B⁻¹ * φ g * B) = B⁻¹ * φ g * B := by
    rw [map_mul, map_mul, map_inv, ← hconjGL, hB σ]
    group

  have hkey : ((B⁻¹ * φ g * B : GeneralLinearGroup n L) : Matrix n n L).map (σ : L →+* L)
      = (B⁻¹ * φ g * B : Matrix n n L) := by
    have := congrArg (fun u : GeneralLinearGroup n L => (u : Matrix n n L)) key
    simpa [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply] using this
  exact hkey.symm

theorem descentConjugatorSupply_of_isConjugatorCocycle
    (φ : G →* GeneralLinearGroup n L) (k : Subring L)
    (hgal : ∀ σ : L →+* L, (∀ x ∈ k, σ x = x) → ∃ τ : L ≃ₐ[K] L, (τ : L →+* L) = σ)
    (hfix : ∀ x : L, (∀ σ : L →+* L, (∀ y ∈ k, σ y = y) → σ x = x) → x ∈ k)
    (Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L) (hQ : IsConjugatorCocycle φ Q) :
    DescentConjugatorSupply φ k := by
  intro _hperσ

  obtain ⟨B, hB⟩ := exists_galFixed_conj_of_isConjugatorCocycle φ Q hQ
  refine ⟨B, entries_mem_of_forall_map_conj_eq φ k B (fun σ hσ g => ?_) hfix⟩
  obtain ⟨τ, hτ⟩ := hgal σ hσ
  rw [← hτ]
  exact hB τ g

end Wire

end DeligneSerre


open Matrix

namespace DeligneSerre

section SchurUniqueness

variable {L : Type*} [Field L] {n : Type*} [DecidableEq n] [Fintype n]
variable {G : Type*} [Group G]

theorem mem_center_of_commute_span_top {S : Set (Matrix n n L)}
    (hS : Submodule.span L S = ⊤) (M : GeneralLinearGroup n L)
    (hM : ∀ X ∈ S, X * (M : Matrix n n L) = (M : Matrix n n L) * X) :
    M ∈ Subgroup.center (GeneralLinearGroup n L) := by

  have hcomm : ∀ X : Matrix n n L, X * (M : Matrix n n L) = (M : Matrix n n L) * X := by
    have hle : Submodule.span L S ≤
        { carrier := {X | X * (M : Matrix n n L) = (M : Matrix n n L) * X}
          add_mem' := fun {X Y} hX hY => by
            simp only [Set.mem_ofPred_eq] at hX hY ⊢; rw [add_mul, mul_add, hX, hY]
          zero_mem' := by simp
          smul_mem' := fun a X hX => by
            simp only [Set.mem_ofPred_eq] at hX ⊢
            rw [smul_mul_assoc, mul_smul_comm, hX] } :=
      Submodule.span_le.mpr hM
    intro X; exact hle (hS ▸ Submodule.mem_top)

  refine Subgroup.mem_center_iff.mpr fun h => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact hcomm (h : Matrix n n L)

theorem exists_scalar_of_commute_span_top {S : Set (Matrix n n L)}
    (hS : Submodule.span L S = ⊤) (M : GeneralLinearGroup n L)
    (hM : ∀ X ∈ S, X * (M : Matrix n n L) = (M : Matrix n n L) * X) :
    ∃ c : Lˣ, M = GeneralLinearGroup.scalar n c := by
  have hctr := mem_center_of_commute_span_top hS M hM
  rw [GeneralLinearGroup.center_eq_range_scalar] at hctr
  obtain ⟨c, hc⟩ := hctr
  exact ⟨c, hc.symm⟩

theorem exists_scalar_of_conjRep_eq (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (Q Q' : GeneralLinearGroup n L)
    (h : ∀ g, Q⁻¹ * φ g * Q = Q'⁻¹ * φ g * Q') :
    ∃ c : Lˣ, Q' = GeneralLinearGroup.scalar n c * Q := by

  have hcomm : ∀ g, (Q' * Q⁻¹) * φ g = φ g * (Q' * Q⁻¹) := fun g => by
    calc Q' * Q⁻¹ * φ g
        = Q' * (Q⁻¹ * φ g * Q) * Q⁻¹ := by group
      _ = Q' * (Q'⁻¹ * φ g * Q') * Q⁻¹ := by rw [h g]
      _ = φ g * (Q' * Q⁻¹) := by group

  obtain ⟨c, hc⟩ := exists_scalar_of_commute_span_top hspan (Q' * Q⁻¹)
    (fun X ⟨g, hg⟩ => hg ▸ by
      have := congrArg Units.val (hcomm g).symm
      simpa only [Units.val_mul] using this)
  exact ⟨c, by rw [← hc]; group⟩

end SchurUniqueness

section PGLnCocycle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable {G : Type*} [Group G]

def IsConjugatorFamily (φ : G →* GeneralLinearGroup n L)
    (Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L) : Prop :=
  ∀ σ g, ((Q σ)⁻¹ * φ g * Q σ : Matrix n n L) = (φ g : Matrix n n L).map (σ : L →+* L)

theorem isConjugatorFamily_gln {φ : G →* GeneralLinearGroup n L}
    {Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L} (hQ : IsConjugatorFamily φ Q) (σ : L ≃ₐ[K] L)
    (g : G) : (Q σ)⁻¹ * φ g * Q σ = mapGLn σ (φ g) :=
  Units.ext (hQ σ g)

theorem conjugatorFamily_twoFactor (φ : G →* GeneralLinearGroup n L)
    (Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L) (hQ : IsConjugatorFamily φ Q) (σ τ : L ≃ₐ[K] L)
    (g : G) :
    (Q σ * mapGLn σ (Q τ))⁻¹ * φ g * (Q σ * mapGLn σ (Q τ)) = mapGLn (σ * τ) (φ g) := by
  rw [mapGLn_mul, ← isConjugatorFamily_gln hQ τ g, map_mul, map_mul, map_inv,
    ← isConjugatorFamily_gln hQ σ g]
  group

theorem exists_scalar_conjugatorCocycleDefect (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L) (hQ : IsConjugatorFamily φ Q)
    (σ τ : L ≃ₐ[K] L) :
    ∃ c : Lˣ, Q (σ * τ) = GeneralLinearGroup.scalar n c * (Q σ * mapGLn σ (Q τ)) := by
  refine exists_scalar_of_conjRep_eq φ hspan (Q σ * mapGLn σ (Q τ)) (Q (σ * τ)) (fun g => ?_)

  rw [conjugatorFamily_twoFactor φ Q hQ σ τ g, isConjugatorFamily_gln hQ (σ * τ) g]

end PGLnCocycle

section GaloisBookkeeping

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem algebraMapRange_hgal :
    ∀ σ : L →+* L, (∀ x ∈ (algebraMap K L).range, σ x = x) →
      ∃ τ : L ≃ₐ[K] L, (τ : L →+* L) = σ := by
  intro σ hσ

  have hcom : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a := fun a =>
    hσ (algebraMap K L a) ⟨a, rfl⟩
  let σ' : L →ₐ[K] L := { σ with commutes' := hcom }

  refine ⟨(Algebra.IsAlgebraic.algEquivEquivAlgHom K L).symm σ', ?_⟩
  rfl

theorem algebraMapRange_hfix [IsGalois K L] :
    ∀ x : L, (∀ σ : L →+* L, (∀ y ∈ (algebraMap K L).range, σ y = y) → σ x = x) →
      x ∈ (algebraMap K L).range := by
  intro x hx

  have hxfix : ∀ τ : L ≃ₐ[K] L, τ x = x := fun τ =>
    hx (τ : L →+* L) (fun y ⟨a, ha⟩ => ha ▸ τ.commutes a)
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) x).mpr hxfix
  exact ⟨a, ha⟩

variable {n : Type*} [DecidableEq n] [Fintype n] {G : Type*} [Group G]

theorem descentConjugatorSupply_algebraMapRange_of_isConjugatorCocycle [IsGalois K L]
    (φ : G →* GeneralLinearGroup n L)
    (Q : (L ≃ₐ[K] L) → GeneralLinearGroup n L) (hQ : IsConjugatorCocycle φ Q) :
    DescentConjugatorSupply φ (algebraMap K L).range :=
  descentConjugatorSupply_of_isConjugatorCocycle φ (algebraMap K L).range
    algebraMapRange_hgal algebraMapRange_hfix Q hQ

end GaloisBookkeeping

end DeligneSerre

end
