/-
  The finite-field descent: the Brauer–Nesbitt/trace bridge, norm-one normalisation, and the
  headline `Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`.

  Piece three of the pin node of that name (pinned `aa2d8b3`), taken whole: pin lines 906–1692,
  the `section PieceGD` and `section PieceKF` of the `S_` file plus its `theorem solution`
  (re-cut by piece group, §4 of the work order).

  What it establishes. `PieceGD` is the bridge to the already ported Brauer–Nesbitt theorem: the
  trace determinants of matrices (`Matrix.trace_eq_of_charpoly_eq`, `Matrix.det_eq_of_charpoly_eq`,
  `Matrix.trace_eq_of_forall_charpoly_eq`), the trace of the matrix representation
  (`BrauerNesbitt.trace_matrixRepresentation'`) and the transfer of a spanning hypothesis to the
  coordinate-space representation (`span_range_matrixRepresentation_eq_top`). Feeding the equal
  traces to `BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq` (imported from
  `FLTForHuman/Algebra/BrauerNesbittRepresentation.lean`) and reading the intertwiner off as a
  conjugating unit gives `exists_conj_eq_of_span_eq_top_of_charpoly_eq` and its trace form
  `exists_conj_eq_of_span_eq_top_of_trace_eq'`; `span_range_map_eq_top_of_bijective` and
  `exists_conj_eq_galoisTwist_of_span_eq_top` add the Galois-twist step (a bijective `σ` with
  coefficientwise-fixed charpoly).

  `PieceKF` is the finite-field half. Twisted-norm calculus (`coe_glnMap`,
  `iterate_glnMap_coe`, `glnTwistedNorm_add`, `glnTwistedNorm_succ_left`,
  `glnTwistedNorm_add_right_of_eq_one`, `glnTwistedNorm_mod_of_eq_one`,
  `glnTwistedNorm_eq_of_modEq_of_eq_one`, `glnTwistedNorm_conj`), scalar bookkeeping
  (`coe_glnScalar`, `glnScalar_mul_comm`, `glnMap_scalar`, `iterate_glnMap_scalar`,
  `glnTwistedNorm_scalar_mul`), the cyclic cocycle (`cyclicConjugatorCocycle` built from the
  generator of `Gal(L/K)` and its twisted norms, with `isGLnCocycle_cyclicConjugatorCocycle` and
  `isConjugatorCocycle_cyclicConjugatorCocycle`), and norm-one normalisation: a twisted norm
  equal to a fixed scalar forces the scalar to be `σ₀`-fixed
  (`scalar_fixed_of_glnTwistedNorm_eq_scalar`), a `σ₀`-fixed element lies in the range of
  `algebraMap K L` (`mem_algebraMapRange_of_fixed_of_generator`), Hilbert-90-for-units
  (`FiniteField.unitsMap_norm_surjective`, mathlib) supplies the norm-one correction
  (`exists_units_prod_iterate_eq`), and `exists_normOne_conjugator` produces the conjugator with
  trivial twisted norm; `exists_isConjugatorCocycle_of_conjugator_at_generator` then builds the
  conjugator cocycle, and `exists_galGenerator_of_finite` produces a generator of `Gal(L/K)` from
  Frobenius. The two `SubfieldDescentInputs` clauses become
  `brauerNesbittClause_of_finite_of_spanTop` and `noSchurIndexClause_of_finite_of_spanTop`, with
  `subfieldDescentInputs_of_finite_of_spanTop` assembling them and
  `lemme613_realizable_of_finite_of_spanTop` the descent itself; the module closes with the
  wrapper's headline at its root name.

  Source (pinned `aa2d8b3`):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean#L906-L1692>
  and
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean>.

  Assumes: `Deformation/Charpoly.lean` (`SubfieldDescentInputs`,
  `lemma613_of_subfieldDescentInputs`, `DescentConjugatorSupply`,
  `noSchurIndex_of_descentConjugatorSupply`), `Deformation/Cocycle.lean` (`IsConjugatorCocycle`,
  `exists_galFixed_conj_of_isConjugatorCocycle`, `exists_scalar_of_commute_span_top`,
  `mapGLn`, `glnTwistedNorm`), `FLTForHuman/Algebra/BrauerNesbittRepresentation.lean`
  (`BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq`, imported, not restated) and
  `FLTForHuman/GaloisRep/Defs/MatrixRepresentation.lean` (`Deformation.matrixRepresentation` and
  its `_apply` lemma, imported, not restated — the pin's `namespace Deformation` prelude is a copy
  of the `Def_` file). `Matrix.trace_eq_of_charpoly_eq` is stated here at the pin's own root name
  `Matrix.trace_eq_of_charpoly_eq`; the port's `GaloisRep/RepConj.lean` carries a *private*
  `RepConjAux.trace_eq_of_charpoly_eq` with the sibling file's binders
  (`S_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean:130`), which this module
  does not touch — nothing is promoted, and the pin's variant is stated verbatim (work order §3).

  Mathlib-first (2026-10-20, `rg` under `.lake/packages/mathlib/Mathlib`):
  * `Matrix.trace_eq_of_charpoly_eq`, `Matrix.det_eq_of_charpoly_eq`,
    `Matrix.trace_eq_of_forall_charpoly_eq` — **negative** as statements; the proofs are the pin's
    and use mathlib's `Matrix.trace_eq_neg_charpoly_coeff` and `Matrix.det_eq_sign_charpoly_coeff`
    (`LinearAlgebra/Matrix/Charpoly/Coeff.lean:139,151`);
  * `glnScalar_mul_comm` — **hit**, mathlib's `GeneralLinearGroup.scalar_commute`
    (`LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean:88`); the proof is that lemma;
  * `glnMap_scalar` — **hit**, mathlib's `GeneralLinearGroup.map_scalar`
    (`.../GeneralLinearGroup/Defs.lean:243`); the proof is `GeneralLinearGroup.map_scalar σ c`;
  * `coe_glnScalar` — **hit**, mathlib's `GeneralLinearGroup.coe_scalar` (definitional; the pin's
    `rfl` already is it);
  * `exists_galGenerator_of_finite` — **hits**: `FiniteField.frobeniusAlgEquivOfAlgebraic`
    (`FieldTheory/Finite/Basic.lean:363`), `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic` and
    `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow` (`.../Finite/Basic.lean`, used);
  * `exists_units_prod_iterate_eq` — **hits**: `FiniteField.unitsMap_norm_surjective`
    (`FieldTheory/Finite/GaloisField.lean:236`), `Algebra.norm_eq_prod_automorphisms`,
    `Fin.prod_univ_eq_prod_range` (mathlib, used);
  * `mem_algebraMapRange_of_fixed_of_generator` — **hit** through
    `IsGalois.mem_range_algebraMap_iff_fixed` (`FieldTheory/Galois/Basic.lean:340`) and
    `Algebra.IsAlgebraic.algEquivEquivAlgHom` (`RingTheory/Algebraic/Basic.lean:525`);
  * the Brauer–Nesbitt bridge (`trace_matrixRepresentation'`,
    `span_range_matrixRepresentation_eq_top`, `exists_conj_eq_of_span_eq_top_of_charpoly_eq`,
    `exists_conj_eq_of_span_eq_top_of_trace_eq'`, `span_range_map_eq_top_of_bijective`,
    `exists_conj_eq_galoisTwist_of_span_eq_top`) — **negative** in mathlib (it has no Brauer–Nesbitt
    trace theorem at all, see the header of `Algebra/BrauerNesbittRepresentation.lean`); the pin's
    trace form is a wrapper around the ported node plus the matrix/coordinate dictionary, so the
    node is imported and only the wrapper is restated;
  * `glnTwistedNorm_*`, `cyclicConjugatorCocycle`, `scalar_fixed_of_glnTwistedNorm_eq_scalar`,
    `exists_normOne_conjugator`, `exists_isConjugatorCocycle_of_conjugator_at_generator`,
    the two descent clauses, `subfieldDescentInputs_of_finite_of_spanTop` and
    `lemme613_realizable_of_finite_of_spanTop` — **negative** (finite-field norm-one normalisation
    of a `GLₙ`-cocycle; mathlib has `Algebra.norm` and `IsGalois` facts but no such statement).

  Drift against `v4.34.0` — no statement, binder or name changed; 0 warnings:
  * four `haveI` → `have` (`Nontrivial (n → k)` twice, `Finite K`, `Fintype K`) — the
    `linter.style.haveILetI` warning; the instances are still found from the local hypotheses and
    the statements are untouched;
  * `span_range_map_eq_top_of_bijective`: the pin's `refine ⟨fun i j => (Function.surjInv …) (M i j),
    Matrix.ext fun i j => by simp [Matrix.map_apply, Function.surjInv_eq …]⟩` is written
    `ext i j; show σ (Function.surjInv hσ.surjective (M i j)) = M i j; exact Function.surjInv_eq …`
    because at `v4.34.0` the `Matrix.map_apply` rewrite is not type-correct at implicit
    transparency for a bare-lambda matrix (playbook §7's transparency shape); proof only;
  * `glnScalar_mul_comm` and `glnMap_scalar` proofs replaced by the mathlib lemmas above
    (`GeneralLinearGroup.scalar_commute`, `GeneralLinearGroup.map_scalar`);
  * imports: `Mathlib.FieldTheory.Finite.Basic`/`.GaloisField` and `Mathlib.FieldTheory.Galois.Basic`
    for the Frobenius/norm and `IsGalois` API (the pin's `import Mathlib`);
  * the pin's `p2m_*` scaffolding and `P2MW.S_…` wrapper namespace are dropped as in
    `Deformation/Charpoly.lean`; the pin's `theorem solution` is declared at the wrapper's root
    name `Representation.exists_conj_eq_map_…` (the `Analysis/Fourier/PoissonSummationPi.lean`
    precedent); its statement is the pin's `solution` statement (equal checker hash), and the
    `solution` name itself is not duplicated.

  spec-pin: Theorems/Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean
  spec-pin: P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean
-/

import FLTForHuman.Algebra.BrauerNesbittRepresentation
import FLTForHuman.GaloisRep.Deformation.Cocycle
import FLTForHuman.GaloisRep.Defs.MatrixRepresentation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.Group

set_option autoImplicit false

universe u v

noncomputable section

open Module LinearMap Matrix

namespace Matrix

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

theorem trace_eq_of_charpoly_eq (A B : Matrix n n R) (h : A.charpoly = B.charpoly) :
    A.trace = B.trace := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

theorem det_eq_of_charpoly_eq (A B : Matrix n n R) (h : A.charpoly = B.charpoly) :
    A.det = B.det := by
  rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, h]

theorem trace_eq_of_forall_charpoly_eq {G : Type*} {k : Type*} [CommRing k]
    (ρ₁ ρ₂ : G → Matrix n n k)
    (h : ∀ g, (ρ₁ g).charpoly = (ρ₂ g).charpoly) :
    ∀ g, (ρ₁ g).trace = (ρ₂ g).trace :=
  fun g => trace_eq_of_charpoly_eq _ _ (h g)

end Matrix

namespace BrauerNesbitt

open BrauerNesbitt

variable {k : Type u} [Field k] {G : Type u} [Group G]
variable {n : Type} [Fintype n] [DecidableEq n]

open Deformation

theorem trace_matrixRepresentation' (ρ : G →* GL n k) (g : G) :
    LinearMap.trace k (n → k) (matrixRepresentation ρ g) = Matrix.trace (ρ g).val := by
  rw [matrixRepresentation_apply, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq]

theorem span_range_matrixRepresentation_eq_top (ρ : G →* GL n k)
    (hspan : Submodule.span k (Set.range fun g => (ρ g).val) = ⊤) :
    Submodule.span k (Set.range ⇑(matrixRepresentation ρ)) = ⊤ := by

  have step : ∀ X ∈ Submodule.span k (Set.range fun g => (ρ g).val),
      Matrix.toLin' X ∈ Submodule.span k (Set.range ⇑(matrixRepresentation ρ)) := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      refine Submodule.subset_span ⟨g, ?_⟩
      rw [matrixRepresentation_apply, Matrix.toLin'_apply']
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  rw [Submodule.eq_top_iff']
  intro f
  rw [← Matrix.toLin'_toMatrix' f]
  exact step _ (hspan ▸ Submodule.mem_top)

end BrauerNesbitt

namespace BrauerNesbitt

open BrauerNesbitt

variable {k : Type u} [Field k] {G : Type u} [Group G]
variable {n : Type} [Fintype n] [DecidableEq n]

open Deformation

theorem exists_conj_eq_of_span_eq_top_of_charpoly_eq [Nonempty n]
    (ρ₁ ρ₂ : G →* GL n k)
    (hspan₁ : Submodule.span k (Set.range fun g => (ρ₁ g).val) = ⊤)
    (hspan₂ : Submodule.span k (Set.range fun g => (ρ₂ g).val) = ⊤)
    (hchar : ∀ g, ((ρ₁ g).val : Matrix n n k).charpoly = ((ρ₂ g).val).charpoly) :
    ∃ Q : GL n k, ∀ g, (Q⁻¹ * ρ₂ g * Q).val = (ρ₁ g).val := by
  classical

  have htr : ∀ g, Matrix.trace ((ρ₁ g).val : Matrix n n k) = Matrix.trace (ρ₂ g).val :=
    Matrix.trace_eq_of_forall_charpoly_eq (fun g => (ρ₁ g).val) (fun g => (ρ₂ g).val) hchar

  have hspan₁' := span_range_matrixRepresentation_eq_top ρ₁ hspan₁
  have hspan₂' := span_range_matrixRepresentation_eq_top ρ₂ hspan₂
  have htr' : ∀ g, LinearMap.trace k (n → k) (matrixRepresentation ρ₁ g)
      = LinearMap.trace k (n → k) (matrixRepresentation ρ₂ g) := fun g => by
    rw [trace_matrixRepresentation', trace_matrixRepresentation', htr]

  have : Nontrivial (n → k) := Function.nontrivial
  obtain ⟨e, he⟩ := exists_linearEquiv_of_span_range_eq_top_of_trace_eq
    (matrixRepresentation ρ₁) (matrixRepresentation ρ₂) hspan₁' hspan₂' htr'

  set E : Matrix n n k := LinearMap.toMatrix' (e : (n → k) →ₗ[k] (n → k)) with hE
  set E' : Matrix n n k := LinearMap.toMatrix' (e.symm : (n → k) →ₗ[k] (n → k)) with hE'
  have hEE' : E * E' = 1 := by
    rw [hE, hE', ← LinearMap.toMatrix'_comp]; simp [LinearMap.toMatrix'_id]
  have hE'E : E' * E = 1 := by
    rw [hE, hE', ← LinearMap.toMatrix'_comp]; simp [LinearMap.toMatrix'_id]
  set Q : GL n k := ⟨E, E', hEE', hE'E⟩ with hQ
  refine ⟨Q, fun g => ?_⟩

  have hcomm : E * (ρ₁ g).val = (ρ₂ g).val * E := by
    have hcomp : (e : (n → k) →ₗ[k] (n → k)) ∘ₗ matrixRepresentation ρ₁ g
        = matrixRepresentation ρ₂ g ∘ₗ (e : (n → k) →ₗ[k] (n → k)) :=
      LinearMap.ext fun v => he g v
    have := congrArg LinearMap.toMatrix' hcomp
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, matrixRepresentation_apply,
      matrixRepresentation_apply, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  show ((Q⁻¹).val * (ρ₂ g).val * Q.val : Matrix n n k) = (ρ₁ g).val
  have hQval : (Q.val : Matrix n n k) = E := rfl
  have hQinv : ((Q⁻¹).val : Matrix n n k) = E' := rfl
  rw [hQval, hQinv, mul_assoc, ← hcomm, ← mul_assoc, hE'E, one_mul]

theorem exists_conj_eq_of_span_eq_top_of_trace_eq' [Nonempty n]
    (ρ₁ ρ₂ : G →* GL n k)
    (hspan₁ : Submodule.span k (Set.range fun g => (ρ₁ g).val) = ⊤)
    (hspan₂ : Submodule.span k (Set.range fun g => (ρ₂ g).val) = ⊤)
    (htr : ∀ g, Matrix.trace ((ρ₁ g).val : Matrix n n k) = Matrix.trace (ρ₂ g).val) :
    ∃ Q : GL n k, ∀ g, (Q⁻¹ * ρ₂ g * Q).val = (ρ₁ g).val := by
  classical
  have hspan₁' := span_range_matrixRepresentation_eq_top ρ₁ hspan₁
  have hspan₂' := span_range_matrixRepresentation_eq_top ρ₂ hspan₂
  have htr' : ∀ g, LinearMap.trace k (n → k) (matrixRepresentation ρ₁ g)
      = LinearMap.trace k (n → k) (matrixRepresentation ρ₂ g) := fun g => by
    rw [trace_matrixRepresentation', trace_matrixRepresentation', htr]
  have : Nontrivial (n → k) := Function.nontrivial
  obtain ⟨e, he⟩ := exists_linearEquiv_of_span_range_eq_top_of_trace_eq
    (matrixRepresentation ρ₁) (matrixRepresentation ρ₂) hspan₁' hspan₂' htr'
  set E : Matrix n n k := LinearMap.toMatrix' (e : (n → k) →ₗ[k] (n → k)) with hE
  set E' : Matrix n n k := LinearMap.toMatrix' (e.symm : (n → k) →ₗ[k] (n → k)) with hE'
  have hEE' : E * E' = 1 := by
    rw [hE, hE', ← LinearMap.toMatrix'_comp]; simp [LinearMap.toMatrix'_id]
  have hE'E : E' * E = 1 := by
    rw [hE, hE', ← LinearMap.toMatrix'_comp]; simp [LinearMap.toMatrix'_id]
  set Q : GL n k := ⟨E, E', hEE', hE'E⟩
  refine ⟨Q, fun g => ?_⟩
  have hcomm : E * (ρ₁ g).val = (ρ₂ g).val * E := by
    have hcomp : (e : (n → k) →ₗ[k] (n → k)) ∘ₗ matrixRepresentation ρ₁ g
        = matrixRepresentation ρ₂ g ∘ₗ (e : (n → k) →ₗ[k] (n → k)) :=
      LinearMap.ext fun v => he g v
    have := congrArg LinearMap.toMatrix' hcomp
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, matrixRepresentation_apply,
      matrixRepresentation_apply, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  show ((Q⁻¹).val * (ρ₂ g).val * Q.val : Matrix n n k) = (ρ₁ g).val
  rw [show (Q.val : Matrix n n k) = E from rfl,
    show ((Q⁻¹).val : Matrix n n k) = E' from rfl, mul_assoc, ← hcomm, ← mul_assoc, hE'E, one_mul]

end BrauerNesbitt

namespace BrauerNesbitt

open BrauerNesbitt

variable {k' : Type u} [Field k'] {G : Type u} [Group G]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem span_range_map_eq_top_of_bijective (φ : G →* GL n k') (σ : k' →+* k')
    (hσ : Function.Bijective σ)
    (hspan : Submodule.span k' (Set.range fun g => (φ g).val) = ⊤) :
    Submodule.span k' (Set.range fun g => ((φ g).val : Matrix n n k').map σ) = ⊤ := by

  rw [Submodule.eq_top_iff']
  intro M

  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Matrix n n k', M₀.map σ = M := by
    refine ⟨fun i j => (Function.surjInv hσ.surjective) (M i j), ?_⟩
    ext i j
    show σ (Function.surjInv hσ.surjective (M i j)) = M i j
    exact Function.surjInv_eq hσ.surjective (M i j)

  have hM₀mem : M₀ ∈ Submodule.span k' (Set.range fun g => (φ g).val) := hspan ▸ Submodule.mem_top
  rw [← hM₀]
  clear hM₀ hspan
  induction hM₀mem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    have h0 : (0 : Matrix n n k').map ⇑σ = 0 :=
      Matrix.ext fun i j => by simp [Matrix.map_apply]
    rw [h0]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have hadd : (x + y).map ⇑σ = x.map ⇑σ + y.map ⇑σ :=
      Matrix.ext fun i j => by simp [Matrix.map_apply, map_add]
    rw [hadd]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>

    have hsmul : (a • x).map ⇑σ = σ a • x.map ⇑σ :=
      Matrix.ext fun i j => by simp [Matrix.map_apply, smul_eq_mul, map_mul]
    rw [hsmul]; exact Submodule.smul_mem _ _ hx

theorem exists_conj_eq_galoisTwist_of_span_eq_top [Nonempty n]
    (φ : G →* GL n k') (σ : k' →+* k') (hσ : Function.Bijective σ)
    (hspan : Submodule.span k' (Set.range fun g => (φ g).val) = ⊤)
    (hfix : ∀ g i, σ (((φ g).val : Matrix n n k').charpoly.coeff i)
        = ((φ g).val).charpoly.coeff i) :
    ∃ Q : GL n k', ∀ g,
      (Q⁻¹ * φ g * Q).val = ((φ g).val : Matrix n n k').map σ := by
  classical

  let φσ : G →* GL n k' := (Matrix.GeneralLinearGroup.map σ).comp φ
  have hφσval : ∀ g, (φσ g).val = ((φ g).val : Matrix n n k').map σ := fun g => rfl

  have hchar : ∀ g, ((φ g).val : Matrix n n k').charpoly = ((φσ g).val).charpoly := by
    intro g
    rw [hφσval, Matrix.charpoly_map]
    exact (Polynomial.ext fun i => by rw [Polynomial.coeff_map]; exact hfix g i).symm

  have hspanσ : Submodule.span k' (Set.range fun g => (φσ g).val) = ⊤ := by
    have hext : (fun g => (φσ g).val) = fun g => ((φ g).val : Matrix n n k').map σ :=
      funext hφσval
    rw [hext]
    exact span_range_map_eq_top_of_bijective φ σ hσ hspan

  obtain ⟨Q, hQ⟩ := exists_conj_eq_of_span_eq_top_of_charpoly_eq φ φσ hspan hspanσ hchar

  refine ⟨Q⁻¹, fun g => ?_⟩
  have hQ' : Q⁻¹ * φσ g * Q = φ g := Units.ext (hQ g)
  have hflip : Q⁻¹⁻¹ * φ g * Q⁻¹ = φσ g := by
    rw [inv_inv, ← hQ']; group
  rw [show (Q⁻¹⁻¹ * φ g * Q⁻¹).val = ((Q⁻¹⁻¹ * φ g * Q⁻¹ : GL n k') : Matrix n n k') from rfl,
    hflip, hφσval]

end BrauerNesbitt


open Matrix

namespace DeligneSerre

section TwistedNormCalculus

variable {L : Type*} [Field L] {n : Type*} [DecidableEq n] [Fintype n]

theorem coe_glnMap (σ : L →+* L) (U : GeneralLinearGroup n L) :
    ((Matrix.GeneralLinearGroup.map σ U : GeneralLinearGroup n L) : Matrix n n L)
      = (U : Matrix n n L).map ⇑σ :=
  rfl

theorem iterate_glnMap_coe (σ : L →+* L) (j : ℕ) (U : GeneralLinearGroup n L) :
    (((Matrix.GeneralLinearGroup.map σ)^[j] U : GeneralLinearGroup n L) : Matrix n n L)
      = (U : Matrix n n L).map ((⇑σ)^[j]) := by
  induction j generalizing U with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih (Matrix.GeneralLinearGroup.map σ U), coe_glnMap,
      Matrix.map_map, ← Function.iterate_succ ⇑σ j]

theorem glnTwistedNorm_add (σ : L →+* L) (a b : ℕ) (Q : GeneralLinearGroup n L) :
    glnTwistedNorm σ (a + b) Q
      = glnTwistedNorm σ a Q
        * (Matrix.GeneralLinearGroup.map σ)^[a] (glnTwistedNorm σ b Q) := by
  induction b with
  | zero => simp [glnTwistedNorm_zero]
  | succ b ih =>
    have h1 : glnTwistedNorm σ (a + (b + 1)) Q
        = glnTwistedNorm σ a Q * (Matrix.GeneralLinearGroup.map σ)^[a] (glnTwistedNorm σ b Q)
          * (Matrix.GeneralLinearGroup.map σ)^[a + b] Q := by
      show glnTwistedNorm σ ((a + b) + 1) Q = _
      rw [glnTwistedNorm_succ, ih]
    have h2 : (Matrix.GeneralLinearGroup.map σ)^[a] (glnTwistedNorm σ (b + 1) Q)
        = (Matrix.GeneralLinearGroup.map σ)^[a] (glnTwistedNorm σ b Q)
          * (Matrix.GeneralLinearGroup.map σ)^[a + b] Q := by
      rw [glnTwistedNorm_succ, iterate_map_mul, ← Function.iterate_add_apply]
    rw [h1, h2, mul_assoc]

theorem glnTwistedNorm_succ_left (σ : L →+* L) (j : ℕ) (Q : GeneralLinearGroup n L) :
    glnTwistedNorm σ (j + 1) Q
      = Q * Matrix.GeneralLinearGroup.map σ (glnTwistedNorm σ j Q) := by
  induction j with
  | zero => simp [glnTwistedNorm_succ]
  | succ j ih =>
    calc glnTwistedNorm σ (j + 1 + 1) Q
        = glnTwistedNorm σ (j + 1) Q * (Matrix.GeneralLinearGroup.map σ)^[j + 1] Q :=
          glnTwistedNorm_succ σ (j + 1) Q
      _ = Q * Matrix.GeneralLinearGroup.map σ (glnTwistedNorm σ j Q)
            * Matrix.GeneralLinearGroup.map σ ((Matrix.GeneralLinearGroup.map σ)^[j] Q) := by
          rw [ih, Function.iterate_succ_apply']
      _ = Q * Matrix.GeneralLinearGroup.map σ (glnTwistedNorm σ (j + 1) Q) := by
          rw [glnTwistedNorm_succ, map_mul, mul_assoc]

theorem glnTwistedNorm_add_right_of_eq_one (σ : L →+* L) {d : ℕ}
    (Q : GeneralLinearGroup n L) (hQ : glnTwistedNorm σ d Q = 1) (m : ℕ) :
    glnTwistedNorm σ (m + d) Q = glnTwistedNorm σ m Q := by
  rw [glnTwistedNorm_add, hQ, iterate_map_one, mul_one]

theorem glnTwistedNorm_mod_of_eq_one (σ : L →+* L) {d : ℕ}
    (Q : GeneralLinearGroup n L) (hQ : glnTwistedNorm σ d Q = 1) (m : ℕ) :
    glnTwistedNorm σ m Q = glnTwistedNorm σ (m % d) Q := by
  conv_lhs => rw [← Nat.mod_add_div m d]
  generalize m / d = q
  induction q with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ q ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, glnTwistedNorm_add_right_of_eq_one σ Q hQ, ih]

theorem glnTwistedNorm_eq_of_modEq_of_eq_one (σ : L →+* L) {d : ℕ}
    (Q : GeneralLinearGroup n L) (hQ : glnTwistedNorm σ d Q = 1) {a b : ℕ}
    (hab : a ≡ b [MOD d]) :
    glnTwistedNorm σ a Q = glnTwistedNorm σ b Q := by
  have h : a % d = b % d := hab
  rw [glnTwistedNorm_mod_of_eq_one σ Q hQ a, glnTwistedNorm_mod_of_eq_one σ Q hQ b, h]

theorem glnTwistedNorm_conj {G : Type*} [Group G] (σ : L →+* L)
    (φ : G →* GeneralLinearGroup n L) (Q : GeneralLinearGroup n L)
    (hQ : ∀ g, Q⁻¹ * φ g * Q = Matrix.GeneralLinearGroup.map σ (φ g)) (j : ℕ) (g : G) :
    (glnTwistedNorm σ j Q)⁻¹ * φ g * glnTwistedNorm σ j Q
      = (Matrix.GeneralLinearGroup.map σ)^[j] (φ g) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc (glnTwistedNorm σ (j + 1) Q)⁻¹ * φ g * glnTwistedNorm σ (j + 1) Q
        = ((Matrix.GeneralLinearGroup.map σ)^[j] Q)⁻¹
            * ((glnTwistedNorm σ j Q)⁻¹ * φ g * glnTwistedNorm σ j Q)
            * (Matrix.GeneralLinearGroup.map σ)^[j] Q := by
          rw [glnTwistedNorm_succ]; group
      _ = ((Matrix.GeneralLinearGroup.map σ)^[j] Q)⁻¹
            * (Matrix.GeneralLinearGroup.map σ)^[j] (φ g)
            * (Matrix.GeneralLinearGroup.map σ)^[j] Q := by rw [ih]
      _ = (Matrix.GeneralLinearGroup.map σ)^[j] (Q⁻¹ * φ g * Q) := by
          rw [iterate_map_mul, iterate_map_mul, iterate_map_inv]
      _ = (Matrix.GeneralLinearGroup.map σ)^[j] (Matrix.GeneralLinearGroup.map σ (φ g)) := by
          rw [hQ g]
      _ = (Matrix.GeneralLinearGroup.map σ)^[j + 1] (φ g) := by
          rw [← Function.iterate_succ_apply]

end TwistedNormCalculus

section ScalarBookkeeping

variable {L : Type*} [Field L] {n : Type*} [DecidableEq n] [Fintype n]

theorem coe_glnScalar (c : Lˣ) :
    ((GeneralLinearGroup.scalar n c : GeneralLinearGroup n L) : Matrix n n L)
      = Matrix.scalar n (c : L) :=
  rfl

theorem glnScalar_mul_comm (c : Lˣ) (X : GeneralLinearGroup n L) :
    GeneralLinearGroup.scalar n c * X = X * GeneralLinearGroup.scalar n c :=
  GeneralLinearGroup.scalar_commute c X

theorem glnMap_scalar (σ : L →+* L) (c : Lˣ) :
    Matrix.GeneralLinearGroup.map σ (GeneralLinearGroup.scalar n c)
      = GeneralLinearGroup.scalar n (Units.map (σ : L →* L) c) :=
  GeneralLinearGroup.map_scalar σ c

theorem iterate_glnMap_scalar (σ : L →+* L) (k : ℕ) (c : Lˣ) :
    (Matrix.GeneralLinearGroup.map σ)^[k] (GeneralLinearGroup.scalar n c)
      = GeneralLinearGroup.scalar n ((Units.map (σ : L →* L))^[k] c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, glnMap_scalar]

theorem glnTwistedNorm_scalar_mul (σ : L →+* L) (d : ℕ) (c : Lˣ)
    (Q : GeneralLinearGroup n L) :
    glnTwistedNorm σ d (GeneralLinearGroup.scalar n c * Q)
      = GeneralLinearGroup.scalar n
          (∏ k ∈ Finset.range d, (Units.map (σ : L →* L))^[k] c)
        * glnTwistedNorm σ d Q := by
  induction d with
  | zero => simp [glnTwistedNorm_zero]
  | succ d ih =>
    have hL : glnTwistedNorm σ (d + 1) (GeneralLinearGroup.scalar n c * Q)
        = GeneralLinearGroup.scalar n
            (∏ k ∈ Finset.range d, (Units.map (σ : L →* L))^[k] c)
          * glnTwistedNorm σ d Q
          * ((Matrix.GeneralLinearGroup.map σ)^[d] (GeneralLinearGroup.scalar n c)
            * (Matrix.GeneralLinearGroup.map σ)^[d] Q) := by
      rw [glnTwistedNorm_succ, ih, iterate_map_mul]
    have hR : glnTwistedNorm σ (d + 1) Q
        = glnTwistedNorm σ d Q * (Matrix.GeneralLinearGroup.map σ)^[d] Q :=
      glnTwistedNorm_succ σ d Q
    rw [hL, iterate_glnMap_scalar, hR, Finset.prod_range_succ, map_mul]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← glnScalar_mul_comm, mul_assoc]

end ScalarBookkeeping

section CyclicCocycle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {n : Type*} [DecidableEq n] [Fintype n] {G : Type*} [Group G]

theorem coe_ringHom_algEquiv (σ₀ : L ≃ₐ[K] L) :
    ⇑((σ₀ : L ≃ₐ[K] L) : L →+* L) = ⇑σ₀ :=
  rfl

theorem coe_monoidHom_ringHom_algEquiv (σ₀ : L ≃ₐ[K] L) :
    ⇑((((σ₀ : L ≃ₐ[K] L) : L →+* L)) : L →* L) = ⇑σ₀ :=
  rfl

theorem coe_ringHom_algEquiv_pow (σ₀ : L ≃ₐ[K] L) (a : ℕ) :
    ⇑((σ₀ ^ a : L ≃ₐ[K] L) : L →+* L) = (⇑((σ₀ : L ≃ₐ[K] L) : L →+* L))^[a] := by
  rw [coe_ringHom_algEquiv, coe_ringHom_algEquiv, AlgEquiv.coe_pow]

theorem mapGLn_pow_eq_iterate (σ₀ : L ≃ₐ[K] L) (a : ℕ) (U : GeneralLinearGroup n L) :
    mapGLn (σ₀ ^ a) U
      = (Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L))^[a] U := by
  apply Units.ext
  rw [iterate_glnMap_coe]
  show (U : Matrix n n L).map ⇑((σ₀ ^ a : L ≃ₐ[K] L) : L →+* L) = _
  rw [coe_ringHom_algEquiv_pow]

noncomputable def cyclicConjugatorCocycle (σ₀ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ) (Q : GeneralLinearGroup n L) :
    (L ≃ₐ[K] L) → GeneralLinearGroup n L :=
  fun τ => glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (Classical.choose (hgen τ)) Q

theorem cyclicConjugatorCocycle_apply (σ₀ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ) (Q : GeneralLinearGroup n L)
    (τ : L ≃ₐ[K] L) :
    cyclicConjugatorCocycle σ₀ hgen Q τ
      = glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (Classical.choose (hgen τ)) Q :=
  rfl

theorem isGLnCocycle_cyclicConjugatorCocycle (σ₀ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ) (Q : GeneralLinearGroup n L)
    (hQnorm : glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q = 1) :
    IsGLnCocycle (cyclicConjugatorCocycle σ₀ hgen Q) := by
  intro σ τ
  have hσ : σ₀ ^ Classical.choose (hgen σ) = σ := Classical.choose_spec (hgen σ)
  have hτ : σ₀ ^ Classical.choose (hgen τ) = τ := Classical.choose_spec (hgen τ)
  have hστ : σ₀ ^ Classical.choose (hgen (σ * τ)) = σ * τ := Classical.choose_spec (hgen (σ * τ))
  have hpow : σ₀ ^ Classical.choose (hgen (σ * τ))
      = σ₀ ^ (Classical.choose (hgen σ) + Classical.choose (hgen τ)) := by
    rw [pow_add, hσ, hτ, hστ]
  have hmod : Classical.choose (hgen (σ * τ))
      ≡ Classical.choose (hgen σ) + Classical.choose (hgen τ) [MOD orderOf σ₀] :=
    pow_eq_pow_iff_modEq.mp hpow
  have hmap : (Matrix.GeneralLinearGroup.map
        ((σ₀ : L ≃ₐ[K] L) : L →+* L))^[Classical.choose (hgen σ)]
        (glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (Classical.choose (hgen τ)) Q)
      = mapGLn σ
        (glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (Classical.choose (hgen τ)) Q) := by
    rw [← mapGLn_pow_eq_iterate, hσ]
  show glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (Classical.choose (hgen (σ * τ))) Q
      = glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (Classical.choose (hgen σ)) Q
        * mapGLn σ
          (glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (Classical.choose (hgen τ)) Q)
  rw [glnTwistedNorm_eq_of_modEq_of_eq_one _ Q hQnorm hmod, glnTwistedNorm_add, hmap]

theorem isConjugatorCocycle_cyclicConjugatorCocycle (σ₀ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ)
    (φ : G →* GeneralLinearGroup n L) (Q : GeneralLinearGroup n L)
    (hconj : ∀ g, Q⁻¹ * φ g * Q
      = Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L) (φ g))
    (hQnorm : glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q = 1) :
    IsConjugatorCocycle φ (cyclicConjugatorCocycle σ₀ hgen Q) := by
  refine ⟨isGLnCocycle_cyclicConjugatorCocycle σ₀ hgen Q hQnorm, fun τ g => ?_⟩
  have hτ : σ₀ ^ Classical.choose (hgen τ) = τ := Classical.choose_spec (hgen τ)
  have hGL : (cyclicConjugatorCocycle σ₀ hgen Q τ)⁻¹ * φ g * cyclicConjugatorCocycle σ₀ hgen Q τ
      = (Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L))^[Classical.choose (hgen τ)]
          (φ g) :=
    glnTwistedNorm_conj _ φ Q hconj _ g
  have hval := congrArg (Units.val (α := Matrix n n L)) hGL
  rw [iterate_glnMap_coe] at hval
  conv_rhs => rw [← hτ]
  rw [coe_ringHom_algEquiv_pow]
  simpa only [Units.val_mul] using hval

end CyclicCocycle

section NormOneNormalisation

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Finite L]
variable {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n] {G : Type*} [Group G]

omit [Finite L] in

theorem scalar_fixed_of_glnTwistedNorm_eq_scalar (σ₀ : L ≃ₐ[K] L) {d : ℕ}
    (hσd : σ₀ ^ d = 1) (Q : GeneralLinearGroup n L) (lam : Lˣ)
    (hN : glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) d Q
      = GeneralLinearGroup.scalar n lam) :
    σ₀ (lam : L) = (lam : L) := by
  have hQfix : (Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L))^[d] Q = Q := by
    rw [← mapGLn_pow_eq_iterate, hσd, mapGLn_one]
  have h1 : glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (d + 1) Q
      = GeneralLinearGroup.scalar n lam * Q := by
    rw [glnTwistedNorm_succ, hN, hQfix]
  have h2 : glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (d + 1) Q
      = Q * GeneralLinearGroup.scalar n
          (Units.map (((σ₀ : L ≃ₐ[K] L) : L →+* L) : L →* L) lam) := by
    rw [glnTwistedNorm_succ_left, hN, glnMap_scalar]
  have h3 : Q * GeneralLinearGroup.scalar n lam
      = Q * GeneralLinearGroup.scalar n
          (Units.map (((σ₀ : L ≃ₐ[K] L) : L →+* L) : L →* L) lam) := by
    rw [← glnScalar_mul_comm, ← h1, h2]
  have h4 : GeneralLinearGroup.scalar n lam
      = GeneralLinearGroup.scalar n
          (Units.map (((σ₀ : L ≃ₐ[K] L) : L →+* L) : L →* L) lam) :=
    mul_left_cancel h3
  obtain ⟨i⟩ := ‹Nonempty n›
  have h5 := congrArg (fun U : GeneralLinearGroup n L => (U : Matrix n n L) i i) h4
  simp only [coe_glnScalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Units.coe_map,
    MonoidHom.coe_coe, RingHom.coe_coe] at h5
  exact h5.symm

theorem mem_algebraMapRange_of_fixed_of_generator (σ₀ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ) (x : L) (hx : σ₀ x = x) :
    x ∈ (algebraMap K L).range := by
  have hpowfix : ∀ b : ℕ, (σ₀ ^ b) x = x := by
    intro b
    induction b with
    | zero => simp
    | succ b ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  refine algebraMapRange_hfix x (fun σ hσ => ?_)
  obtain ⟨τ, hτ⟩ := algebraMapRange_hgal σ hσ
  obtain ⟨a, ha⟩ := hgen τ
  rw [← hτ, ← ha]
  exact hpowfix a

omit [Finite L] in

theorem coe_iterate_unitsMap (f : L →* L) (k : ℕ) (μ : Lˣ) :
    (((Units.map f)^[k] μ : Lˣ) : L) = (⇑f)^[k] (μ : L) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (((Units.map f)^[k + 1] μ : Lˣ) : L)
        = ((Units.map f ((Units.map f)^[k] μ) : Lˣ) : L) := by
          rw [Function.iterate_succ_apply']
      _ = f (((Units.map f)^[k] μ : Lˣ) : L) := Units.coe_map f _
      _ = f ((⇑f)^[k] (μ : L)) := by rw [ih]
      _ = (⇑f)^[k + 1] (μ : L) := (Function.iterate_succ_apply' (⇑f) k (μ : L)).symm

theorem exists_units_prod_iterate_eq (σ₀ : L ≃ₐ[K] L)
    (hbij : Function.Bijective fun j : Fin (orderOf σ₀) => σ₀ ^ (j : ℕ))
    (lam : Lˣ) (hlam : (lam : L) ∈ (algebraMap K L).range) :
    ∃ μ : Lˣ, ∏ k ∈ Finset.range (orderOf σ₀),
        (Units.map (((σ₀ : L ≃ₐ[K] L) : L →+* L) : L →* L))^[k] μ = lam := by
  obtain ⟨c, hc⟩ := hlam
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact lam.ne_zero hc.symm
  obtain ⟨μ, hμ⟩ := FiniteField.unitsMap_norm_surjective K L (Units.mk0 c hc0)
  have hμval : Algebra.norm K (μ : L) = c := by
    have h := congrArg Units.val hμ
    simpa using h
  refine ⟨μ, Units.ext ?_⟩
  have hcoeprod : ((∏ k ∈ Finset.range (orderOf σ₀),
        (Units.map (((σ₀ : L ≃ₐ[K] L) : L →+* L) : L →* L))^[k] μ : Lˣ) : L)
      = ∏ k ∈ Finset.range (orderOf σ₀), (σ₀ ^ k) (μ : L) := by
    rw [← Units.coeHom_apply, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.coeHom_apply, coe_iterate_unitsMap, coe_monoidHom_ringHom_algEquiv,
      AlgEquiv.coe_pow]
  calc ((∏ k ∈ Finset.range (orderOf σ₀),
        (Units.map (((σ₀ : L ≃ₐ[K] L) : L →+* L) : L →* L))^[k] μ : Lˣ) : L)
      = ∏ k ∈ Finset.range (orderOf σ₀), (σ₀ ^ k) (μ : L) := hcoeprod
    _ = ∏ j : Fin (orderOf σ₀), (σ₀ ^ (j : ℕ)) (μ : L) :=
        (Fin.prod_univ_eq_prod_range (fun k => (σ₀ ^ k) (μ : L)) (orderOf σ₀)).symm
    _ = ∏ τ : L ≃ₐ[K] L, τ (μ : L) := hbij.prod_comp (fun τ => τ (μ : L))
    _ = algebraMap K L (Algebra.norm K (μ : L)) := (Algebra.norm_eq_prod_automorphisms K _).symm
    _ = (lam : L) := by rw [hμval, hc]

theorem exists_normOne_conjugator (σ₀ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ)
    (hbij : Function.Bijective fun j : Fin (orderOf σ₀) => σ₀ ^ (j : ℕ))
    (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (Q₁ : GeneralLinearGroup n L)
    (hconj : ∀ g, Q₁⁻¹ * φ g * Q₁
      = Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L) (φ g)) :
    ∃ Q : GeneralLinearGroup n L,
      (∀ g, Q⁻¹ * φ g * Q
        = Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L) (φ g)) ∧
      glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q = 1 := by
  have hσd : σ₀ ^ orderOf σ₀ = 1 := pow_orderOf_eq_one σ₀

  have hcommGL : ∀ g, φ g * glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁
      = glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁ * φ g := by
    intro g
    have hGL : (glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁)⁻¹ * φ g
        * glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁ = φ g := by
      rw [glnTwistedNorm_conj _ φ Q₁ hconj (orderOf σ₀) g, ← mapGLn_pow_eq_iterate, hσd,
        mapGLn_one]
    calc φ g * glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁
        = glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁
            * ((glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁)⁻¹ * φ g
              * glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁) := by group
      _ = glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁ * φ g := by rw [hGL]
  have hcomm : ∀ X ∈ Set.range fun g => (φ g : Matrix n n L),
      X * (glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁ : Matrix n n L)
        = (glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁ : Matrix n n L) * X := by
    rintro X ⟨g, rfl⟩
    simpa only [Units.val_mul] using congrArg Units.val (hcommGL g)

  obtain ⟨lam, hlam⟩ := exists_scalar_of_commute_span_top hspan
    (glnTwistedNorm ((σ₀ : L ≃ₐ[K] L) : L →+* L) (orderOf σ₀) Q₁) hcomm

  have hfix : σ₀ (lam : L) = (lam : L) :=
    scalar_fixed_of_glnTwistedNorm_eq_scalar σ₀ hσd Q₁ lam hlam
  have hmem : (lam : L) ∈ (algebraMap K L).range :=
    mem_algebraMapRange_of_fixed_of_generator σ₀ hgen (lam : L) hfix
  obtain ⟨μ, hμ⟩ := exists_units_prod_iterate_eq σ₀ hbij lam hmem

  refine ⟨GeneralLinearGroup.scalar n μ⁻¹ * Q₁, fun g => ?_, ?_⟩
  · have hinner : (GeneralLinearGroup.scalar n μ⁻¹)⁻¹ * φ g * GeneralLinearGroup.scalar n μ⁻¹
        = φ g := by
      have h := glnScalar_mul_comm μ⁻¹ (φ g)
      calc (GeneralLinearGroup.scalar n μ⁻¹)⁻¹ * φ g * GeneralLinearGroup.scalar n μ⁻¹
          = (GeneralLinearGroup.scalar n μ⁻¹)⁻¹ * (φ g * GeneralLinearGroup.scalar n μ⁻¹) := by
            group
        _ = (GeneralLinearGroup.scalar n μ⁻¹)⁻¹ * (GeneralLinearGroup.scalar n μ⁻¹ * φ g) := by
            rw [← h]
        _ = φ g := by group
    calc (GeneralLinearGroup.scalar n μ⁻¹ * Q₁)⁻¹ * φ g
          * (GeneralLinearGroup.scalar n μ⁻¹ * Q₁)
        = Q₁⁻¹ * ((GeneralLinearGroup.scalar n μ⁻¹)⁻¹ * φ g * GeneralLinearGroup.scalar n μ⁻¹)
            * Q₁ := by group
      _ = Q₁⁻¹ * φ g * Q₁ := by rw [hinner]
      _ = Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L) (φ g) := hconj g
  · have hprodinv : (∏ k ∈ Finset.range (orderOf σ₀),
        (Units.map (((σ₀ : L ≃ₐ[K] L) : L →+* L) : L →* L))^[k] μ⁻¹) = lam⁻¹ := by
      rw [← hμ, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => iterate_map_inv _ k μ
    rw [glnTwistedNorm_scalar_mul, hlam, hprodinv, ← map_mul, inv_mul_cancel, map_one]

theorem exists_isConjugatorCocycle_of_conjugator_at_generator (σ₀ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ)
    (hbij : Function.Bijective fun j : Fin (orderOf σ₀) => σ₀ ^ (j : ℕ))
    (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (Q₁ : GeneralLinearGroup n L)
    (hconj : ∀ g, Q₁⁻¹ * φ g * Q₁
      = Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L) (φ g)) :
    ∃ c : (L ≃ₐ[K] L) → GeneralLinearGroup n L, IsConjugatorCocycle φ c := by
  obtain ⟨Q, hQconj, hQnorm⟩ := exists_normOne_conjugator σ₀ hgen hbij φ hspan Q₁ hconj
  exact ⟨cyclicConjugatorCocycle σ₀ hgen Q,
    isConjugatorCocycle_cyclicConjugatorCocycle σ₀ hgen φ Q hQconj hQnorm⟩

theorem exists_galGenerator_of_finite :
    ∃ σ₀ : L ≃ₐ[K] L, (∀ τ : L ≃ₐ[K] L, ∃ a : ℕ, σ₀ ^ a = τ) ∧
      Function.Bijective fun j : Fin (orderOf σ₀) => σ₀ ^ (j : ℕ) := by
  have : Finite K := Finite.of_injective _ (algebraMap K L).injective
  have : Fintype K := Fintype.ofFinite K
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic K L, fun τ => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 τ
    exact ⟨j.1, hj⟩
  · have hord : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L :=
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K L
    rw [hord]
    exact FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L

end NormOneNormalisation

section FiniteFieldDescent

variable {K : Type*} [Field K] {L : Type u} [Field L] [Algebra K L] [Finite L]
variable {n : Type} [DecidableEq n] [Fintype n] [Nonempty n] {G : Type u} [Group G]

theorem brauerNesbittClause_of_finite_of_spanTop
    (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (k : Subring L) :
    ∀ σ : L →+* L, (∀ x ∈ k, σ x = x) →
      (∀ g, ((φ g : Matrix n n L).map σ).charpoly = (φ g : Matrix n n L).charpoly) →
      ∃ Q : GeneralLinearGroup n L, ∀ g,
        (Q⁻¹ * φ g * Q : Matrix n n L) = (φ g : Matrix n n L).map σ := by
  intro σ _hσk hcp
  have hσbij : Function.Bijective ⇑σ := Finite.injective_iff_bijective.mp σ.injective
  have hfixcoeff : ∀ g i, σ ((φ g : Matrix n n L).charpoly.coeff i)
      = (φ g : Matrix n n L).charpoly.coeff i := by
    intro g i
    have h := hcp g
    rw [Matrix.charpoly_map] at h
    have h' := congrArg (fun p => Polynomial.coeff p i) h
    simpa [Polynomial.coeff_map] using h'
  obtain ⟨Q, hQ⟩ := BrauerNesbitt.exists_conj_eq_galoisTwist_of_span_eq_top φ σ hσbij hspan
    hfixcoeff
  exact ⟨Q, fun g => by simpa only [Units.val_mul] using hQ g⟩

theorem exists_isConjugatorCocycle_of_finite_of_spanTop
    (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (hcoeff : ∀ g i, (φ g : Matrix n n L).charpoly.coeff i ∈ (algebraMap K L).range) :
    ∃ c : (L ≃ₐ[K] L) → GeneralLinearGroup n L, IsConjugatorCocycle φ c := by
  obtain ⟨σ₀, hgen, hbij⟩ := exists_galGenerator_of_finite (K := K) (L := L)
  have hσbij : Function.Bijective ⇑((σ₀ : L ≃ₐ[K] L) : L →+* L) := σ₀.bijective
  have hfixcoeff : ∀ g i, ((σ₀ : L ≃ₐ[K] L) : L →+* L) ((φ g : Matrix n n L).charpoly.coeff i)
      = (φ g : Matrix n n L).charpoly.coeff i := by
    intro g i
    obtain ⟨a, ha⟩ := hcoeff g i
    rw [← ha]
    exact σ₀.commutes a
  obtain ⟨Q₁, hQ₁⟩ := BrauerNesbitt.exists_conj_eq_galoisTwist_of_span_eq_top φ
    ((σ₀ : L ≃ₐ[K] L) : L →+* L) hσbij hspan hfixcoeff
  have hconj : ∀ g, Q₁⁻¹ * φ g * Q₁
      = Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L) (φ g) := by
    intro g
    apply Units.ext
    rw [coe_glnMap]
    simpa only [Units.val_mul] using hQ₁ g
  exact exists_isConjugatorCocycle_of_conjugator_at_generator σ₀ hgen hbij φ hspan Q₁ hconj

theorem noSchurIndexClause_of_finite_of_spanTop
    (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤) :
    (∀ σ : L →+* L, (∀ x ∈ (algebraMap K L).range, σ x = x) →
        ∃ Q : GeneralLinearGroup n L, ∀ g,
          (Q⁻¹ * φ g * Q : Matrix n n L) = (φ g : Matrix n n L).map σ) →
      ∃ ρ : G →* GeneralLinearGroup n ((algebraMap K L).range),
      ∃ Q : GeneralLinearGroup n L,
        ∀ g, (Q⁻¹ * φ g * Q : Matrix n n L)
          = (ρ g : Matrix n n ((algebraMap K L).range)).map ((algebraMap K L).range.subtype) := by
  intro hper
  obtain ⟨σ₀, hgen, hbij⟩ := exists_galGenerator_of_finite (K := K) (L := L)
  have hσ₀fix : ∀ x ∈ (algebraMap K L).range, ((σ₀ : L ≃ₐ[K] L) : L →+* L) x = x := by
    rintro x ⟨a, rfl⟩
    exact σ₀.commutes a
  obtain ⟨Q₁, hQ₁⟩ := hper ((σ₀ : L ≃ₐ[K] L) : L →+* L) hσ₀fix
  have hconj : ∀ g, Q₁⁻¹ * φ g * Q₁
      = Matrix.GeneralLinearGroup.map ((σ₀ : L ≃ₐ[K] L) : L →+* L) (φ g) := by
    intro g
    apply Units.ext
    rw [coe_glnMap]
    simpa only [Units.val_mul] using hQ₁ g
  obtain ⟨c, hc⟩ := exists_isConjugatorCocycle_of_conjugator_at_generator σ₀ hgen hbij φ hspan
    Q₁ hconj
  have hsupply : DescentConjugatorSupply φ (algebraMap K L).range :=
    descentConjugatorSupply_algebraMapRange_of_isConjugatorCocycle φ c hc
  exact noSchurIndex_of_descentConjugatorSupply φ (algebraMap K L).range hsupply hper

theorem subfieldDescentInputs_of_finite_of_spanTop
    (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤) :
    SubfieldDescentInputs φ (algebraMap K L).range where
  brauerNesbitt := brauerNesbittClause_of_finite_of_spanTop φ hspan _
  noSchurIndex := noSchurIndexClause_of_finite_of_spanTop φ hspan

theorem lemme613_realizable_of_finite_of_spanTop
    (φ : G →* GeneralLinearGroup n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (hcoeff : ∀ g i, (φ g : Matrix n n L).charpoly.coeff i ∈ (algebraMap K L).range) :
    ∃ ρ : G →* GeneralLinearGroup n ((algebraMap K L).range),
    ∃ Q : GeneralLinearGroup n L,
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n L)
        = (ρ g : Matrix n n ((algebraMap K L).range)).map ((algebraMap K L).range.subtype) :=
  lemma613_of_subfieldDescentInputs φ (algebraMap K L).range hcoeff
    (subfieldDescentInputs_of_finite_of_spanTop φ hspan)

end FiniteFieldDescent

end DeligneSerre

namespace Representation

/-- A matrix representation `φ` over a finite field extension `L/K`, spanning `Mₙ(L)` and with
characteristic-polynomial coefficients in `K`, is conjugate to the base change of a
representation defined over `(algebraMap K L).range` — the `Theorems/` wrapper's statement,
verbatim. -/
theorem exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top
    {K : Type v} [Field K] {L : Type u} [Field L] [Algebra K L] [Finite L]
    {n : Type} [DecidableEq n] [Fintype n] [Nonempty n] {G : Type u} [Group G]
    (φ : G →* GL n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (hcoeff : ∀ g i, (φ g : Matrix n n L).charpoly.coeff i ∈ (algebraMap K L).range) :
    ∃ ρ : G →* GL n ((algebraMap K L).range), ∃ Q : GL n L,
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n L)
        = (ρ g : Matrix n n ((algebraMap K L).range)).map ((algebraMap K L).range.subtype) :=
  DeligneSerre.lemme613_realizable_of_finite_of_spanTop φ hspan hcoeff

end Representation

end
