/-
  Semisimple descent of a two-dimensional mod-`p` representation — the residual-realization
  row of the `ModularCurve` set (MC-5, story M7):
  `ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite`.

  What it establishes. Let `Ω` be algebraically closed, `k` a finite field embedded in `Ω`
  by `ι : k →+* Ω`, and `ρ : Gal(L/K) →* (V ≃ₗ[Ω] V)` a two-dimensional `Ω`-representation
  of the Galois group which is irreducible, has finite image, and whose trace and
  determinant at every `σ` lie in the image of `ι`. Then there is a `k`-vector space `V₀`
  of `k`-dimension two and a representation `ρ₀ : Gal(L/K) →* (V₀ ≃ₗ[k] V₀)` such that

  * `ρ₀` again has cyclotomic determinant (`ModularCurve.CyclotomicDeterminant M p`, D7);
  * `ker ρ ≤ ker ρ₀`;
  * the `ι`-images of the trace and the determinant of `ρ₀ σ` are the trace and the
    determinant of `ρ σ`;
  * every `ρ₀`-stable `k`-subspace `W` of `V₀` admits a `ρ₀`-stable complement `W'`
    (`IsCompl W W'`) — this is the semisimplicity the name refers to.

  The route is the pin's: transfer `ρ` to a matrix representation `φ` over the
  intermediate field `E = k(a)`, where `a` is an eigenvalue of some non-scalar `ρ g₀`
  (finite image gives `a ^ n = 1`, so `a` is integral and `E/k` is finite); the trace and
  determinant hypotheses put the characteristic-polynomial coefficients of every `φ g` in
  `(algebraMap k E).range`, so the finite-image descent `exists_conj_eq_map_…` realizes
  `φ` over the subring `R = (algebraMap k E).range ≅ k` up to a single conjugating unit
  `Q`; reading `Q` back into `Ω` and pairing with the `k`-spanning lemma — which is where
  the complement comes from — closes all six conjuncts.

  Imported, not restated: `ModularCurve.CyclotomicDeterminant`
  (`ModularCurve/Defs/ResidualRealization.lean`, D7, the pin's
  `Definitions/Def_ModularCurve_ResidualRealization.lean`) and the three premise nodes
  `Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue`
  (`RepresentationTheory/SubfieldBasis.lean`),
  `Representation.span_range_eq_top_of_isIrreducible`
  (`RepresentationTheory/Burnside.lean`) and
  `Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
  (`GaloisRep/Deformation/FiniteDescent.lean`).

  Transcribed verbatim from the pin's node
  `ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite` —
  `Theorems/Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean`
  (the statement authority) and
  `P2M/Sol/S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean`
  (403 pin lines, pinned `aa2d8b3`): its `theorem solution` tail is the public headline
  below, and its `P2mWs11Glue` engine (the three sections `SpanDescent`/`Stable`/`Main`,
  pin lines 17–378) is carried whole into `ModularCurve.ResidualDescentAux`. The pin's
  namespace is renamed (`P2mWs11Glue` → `ResidualDescentAux`), the `P2M.Util` prelude
  (`p2m_reactivate`, `p2m_exact_reverting`) and `import Mathlib` are dropped in favour of
  the specific imports below, every engine declaration is `private` (the wire has a
  statement for the headline only, and the pin's `main` and `solution` share it), and the
  pin's `set_option maxHeartbeats 6400000` / `synthInstance.maxHeartbeats 800000` are
  **not** carried: the whole node elaborates at the port's cap. The `@[scoped simp]` on
  the pin's `entryLM_apply` is dropped with it (the proof uses the equation explicitly).

  Proof-level deviations, all of them forced by a linter that may not be suppressed here
  (nothing below touches a statement, a hypothesis or the order of the pin's assembly):

  1. `haveI` → `have` and `letI` → `let`. `linter.style.haveILetI` (on by default at
     `v4.34.0`) flags every `haveI`/`letI` in a proposition goal. In Lean 4 `have`/`let`
     register local instances themselves, so the instances the rest of the pin's proof
     consumes are still found; the whole file is silent at
     `-DmaxHeartbeats=200000` after the change;
  2. `LinearEquiv.ofLinear` → `LinearEquiv.ofLinearMap` (`ofLinear` is `@[deprecated]`
     since `2026-06-23`; the two have the same signature and the same `f g h₁ h₂` argument
     order, so the pin's two inverse laws are passed unchanged);
  3. `omit [Fintype n] [DecidableEq n] in` on `entryLM_apply` — the pin's
     `linter.unusedSectionVars` case (the equation is `rfl` and needs neither instance);
  4. one `have _hp := hp` at the head of the pin's `main`: the pin never consumes the
     characteristic-`p` hypothesis `hp`, and `linter.unusedVariables` is on, so it is
     referenced once under an underscore name; and in `hmaster` the pin's
     `simp only [Units.val_mul, Matrix.map_mul, ← hφ, hmE]` is `simp only [Matrix.map_mul]`
     — `linter.unusedSimpArgs` reports all three other arguments as removable (they are
     `rfl`-level here: `hφ` and `hmE` are both `fun g => rfl`), and the following
     `congr 2` still closes the goal.

  Mathlib-first audit (one line per declaration of the pin's engine, then the headline):

  * `entryLM`, `entryLM_apply` — searched `Matrix`/`LinearMap` for the evaluation map
    `Matrix n n L →ₗ[L] L`: mathlib has `Matrix.dotProduct`/`Matrix.mulVecLin` and the
    dual-basis API, not this coordinate functional; transcribed (its two axioms are
    `rfl`, as in the pin);
  * `span_eq_top_of_span_map_eq_top` — searched `span_map`/`Submodule.span_image`/
    `exists_le_ker_of_lt_top`: mathlib has the ingredients (`Submodule.span_image`,
    `Submodule.exists_le_ker_of_lt_top`, `Matrix.matrix_eq_sum_single`) but nothing that
    pulls a `K`-span back through `M ↦ M.map f`; the pin's argument is transcribed;
  * `stabilizerSubmodule` — searched `Submodule`/`Matrix.mulVec` for "matrices preserving
    a subspace": mathlib has `LinearMap`-level stabilizers, not the `mulVec` set as a
    `Submodule K (Matrix n n K)`; transcribed;
  * `eq_bot_or_eq_top_of_span_eq_top` — searched `IsSimpleModule`/`IsIrreducible` for the
    matrix-algebra form of Schur's lemma: mathlib's is the module-theoretic version
    (`IsSimpleModule`), the `span = ⊤ ⟹ (⊥ or ⊤)` coordinate statement is the pin's;
    transcribed;
  * `conjEquiv`, `conjEquiv_apply` — searched `conj`/`mulLeft`/`mulRight`: mathlib has
    `LinearMap.mulLeft`/`mulRight`, `Matrix.GeneralLinearGroup` and conjugation of
    matrices by units as a `MulAction` (`Matrix.GeneralLinearGroup.toLin`), not this
    `N ↦ Q⁻¹ N Q` `LinearEquiv`; the pin's two-field `LinearEquiv.ofLinear` is transcribed
    as `LinearEquiv.ofLinearMap` (its v4.34 name — `ofLinear` is deprecated, and a
    deprecation warning is not allowed here);
  * `main` — searched for the whole statement: no mathlib statement (it is the pin's
    assembly of the three premises); transcribed, keeping the pin's order of assembly
    (`exists_basis_…`, then `span_range_…`, then `exists_conj_eq_map_…` last);
  * the public headline `ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite`
    — repeats `main`'s statement with the wrapper's binders and is `main` applied, as the
    pin's `solution` is.

  Assumes: mathlib `v4.34.0`; the D7 definition module
  `ModularCurve/Defs/ResidualRealization.lean` (`ModularCurve.CyclotomicDeterminant`,
  imported, not restated) and the three premise modules above (imported, not restated).

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean#L17-L378

  spec-pin: Theorems/Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean
-/
import FLTForHuman.ModularCurve.Defs.ResidualRealization
import FLTForHuman.RepresentationTheory.SubfieldBasis
import FLTForHuman.RepresentationTheory.Burnside
import FLTForHuman.GaloisRep.Deformation.FiniteDescent
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Module

namespace ModularCurve

namespace ResidualDescentAux

section SpanDescent

variable {K L : Type*} [Field K] [Field L] {n : Type*} [Fintype n] [DecidableEq n]

private def entryLM (L : Type*) [Field L] {n : Type*} (i j : n) : Matrix n n L →ₗ[L] L where
  toFun N := N i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
private theorem entryLM_apply (i j : n) (N : Matrix n n L) : entryLM L i j N = N i j := rfl

private theorem span_eq_top_of_span_map_eq_top (f : K →+* L) (S : Set (Matrix n n K))
    (h : Submodule.span L ((fun M : Matrix n n K => M.map f) '' S) = ⊤) :
    Submodule.span K S = ⊤ := by
  by_contra hne
  obtain ⟨ℓ, hℓ0, hℓ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)

  have hℓsum : ∀ M : Matrix n n K, ℓ M = ∑ i, ∑ j, M i j * ℓ (Matrix.single i j 1) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

  let ℓ' : Matrix n n L →ₗ[L] L := ∑ i, ∑ j, f (ℓ (Matrix.single i j 1)) • entryLM L i j
  have hℓ' : ∀ M : Matrix n n K, ℓ' (M.map f) = f (ℓ M) := by
    intro M
    rw [hℓsum, map_sum]
    simp only [ℓ', LinearMap.sum_apply, LinearMap.smul_apply, entryLM_apply, Matrix.map_apply,
      smul_eq_mul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hker : (⊤ : Submodule L (Matrix n n L)) ≤ LinearMap.ker ℓ' := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hℓ', LinearMap.mem_ker.mp (hℓ (Submodule.subset_span hM)),
      map_zero]
  have hc : ∀ i j, ℓ (Matrix.single i j 1) = 0 := by
    intro i j
    have h1 : ℓ' ((Matrix.single i j (1 : K)).map f) = 0 := hker Submodule.mem_top
    rw [hℓ'] at h1
    exact (map_eq_zero_iff f f.injective).mp h1
  apply hℓ0
  ext M
  rw [hℓsum]
  simp [hc]

end SpanDescent

section Stable

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

private def stabilizerSubmodule (W : Submodule K (n → K)) : Submodule K (Matrix n n K) where
  carrier := {N | ∀ v ∈ W, N.mulVec v ∈ W}
  add_mem' {A B} hA hB v hv := by rw [Matrix.add_mulVec]; exact W.add_mem (hA v hv) (hB v hv)
  zero_mem' v hv := by rw [Matrix.zero_mulVec]; exact W.zero_mem
  smul_mem' c A hA v hv := by
    have h : (c • A).mulVec v = c • A.mulVec v := by
      ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [h]; exact W.smul_mem c (hA v hv)

private theorem eq_bot_or_eq_top_of_span_eq_top {ι : Type*} (S : ι → Matrix n n K)
    (hS : Submodule.span K (Set.range S) = ⊤) (W : Submodule K (n → K))
    (hW : ∀ i, ∀ v ∈ W, (S i).mulVec v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  have hall : ∀ N : Matrix n n K, ∀ v ∈ W, N.mulVec v ∈ W := by
    have : (⊤ : Submodule K (Matrix n n K)) ≤ stabilizerSubmodule W := by
      rw [← hS, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hW i
    exact fun N => this Submodule.mem_top
  rcases eq_or_ne W ⊥ with h | h
  · exact Or.inl h
  right
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp h
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc
    exact hw0 (funext fun j => not_not.mp ((not_exists.mp hc) j))

  have hbasis : ∀ i, (Pi.single i 1 : n → K) ∈ W := by
    intro i
    have h1 : (Matrix.single i j (w j)⁻¹).mulVec w ∈ W := hall _ w hwW
    rw [Matrix.single_mulVec, inv_mul_cancel₀ hj] at h1
    exact h1
  rw [eq_top_iff]
  intro v _
  rw [← (Pi.basisFun K n).sum_repr v]
  exact W.sum_mem fun i _ => W.smul_mem _ (by rw [Pi.basisFun_apply]; exact hbasis i)

end Stable

section Main

private def conjEquiv {L : Type*} [Field L] {n : Type*} [Fintype n] [DecidableEq n] (Q : GL n L) :
    Matrix n n L ≃ₗ[L] Matrix n n L :=
  LinearEquiv.ofLinearMap
    ((LinearMap.mulLeft L ((Q⁻¹ : GL n L) : Matrix n n L)).comp (LinearMap.mulRight L (Q : Matrix n n L)))
    ((LinearMap.mulLeft L (Q : Matrix n n L)).comp (LinearMap.mulRight L ((Q⁻¹ : GL n L) : Matrix n n L)))
    (by
      ext N : 1
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one])
    (by
      ext N : 1
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])

private theorem conjEquiv_apply {L : Type*} [Field L] {n : Type*} [Fintype n] [DecidableEq n] (Q : GL n L)
    (N : Matrix n n L) : conjEquiv Q N = ((Q⁻¹ : GL n L) : Matrix n n L) * N * (Q : Matrix n n L) := by
  simp [conjEquiv, Matrix.mul_assoc]

private theorem main {K L : Type} [Field K] [Field L] [Algebra K L] (M p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (V : Type) [AddCommGroup V] [Module Ω V] (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[Ω] V))
    (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2) (hfin : Finite ρ.range)
    (hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range)
    (hcyc : ModularCurve.CyclotomicDeterminant M p ρ) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀)
      (ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      ModularCurve.CyclotomicDeterminant M p ρ₀ ∧
      ρ.ker ≤ ρ₀.ker ∧
      (∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) ∧
      (∀ W : Submodule k V₀, (∀ σ, ∀ v ∈ W, ρ₀ σ v ∈ W) →
        ∃ W' : Submodule k V₀, (∀ σ, ∀ v ∈ W', ρ₀ σ v ∈ W') ∧ IsCompl W W') := by
  classical
  -- The pin's proof never consumes the characteristic-`p` hypothesis `hp`; it is part of the
  -- statement's shape only. Reference it so the unused-variables linter stays quiet.
  have _hp := hp
  have : FiniteDimensional Ω V := .of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV

  let ρ' : Representation Ω (L ≃ₐ[K] L) V :=
    { toFun := fun g => (ρ g).toLinearMap
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g h => by simp [LinearEquiv.coe_toLinearMap_mul] }
  have hρ' : ∀ g, ρ' g = (ρ g).toLinearMap := fun g => rfl
  have : Nontrivial (Subrepresentation ρ') := ⟨⊥, ⊤, fun hbt => by
    have h1 : (⊥ : Subrepresentation ρ').toSubmodule = (⊤ : Subrepresentation ρ').toSubmodule := by rw [hbt]
    exact bot_ne_top (h1 : (⊥ : Submodule Ω V) = ⊤)⟩
  have : ρ'.IsIrreducible := by
    refine ⟨fun W => ?_⟩
    rcases hirr W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv) with h0 | h0
    · left; exact Subrepresentation.toSubmodule_injective h0
    · right; exact Subrepresentation.toSubmodule_injective h0
  have hspanΩ : Submodule.span Ω (Set.range ρ') = ⊤ :=
    Representation.span_range_eq_top_of_isIrreducible ρ'

  obtain ⟨g₀, hg₀⟩ : ∃ g₀, ∀ c : Ω, (ρ g₀).toLinearMap ≠ c • LinearMap.id := by
    by_contra hall
    have hall' : ∀ g, ∃ c : Ω, (ρ g).toLinearMap = c • LinearMap.id := fun g => by
      by_contra hg
      exact hall ⟨g, fun c hc => hg ⟨c, hc⟩⟩
    obtain ⟨v, hv0⟩ := exists_ne (0 : V)
    have hW : ∀ σ, ∀ x ∈ (Ω ∙ v), ρ σ x ∈ (Ω ∙ v) := by
      intro σ x hx
      obtain ⟨c, hc⟩ := hall' σ
      have : ρ σ x = c • x := by
        rw [← LinearEquiv.coe_coe, hc]; rfl
      rw [this]
      exact Submodule.smul_mem _ c hx
    rcases hirr _ hW with h0 | h0
    · exact hv0 (Submodule.span_singleton_eq_bot.mp h0)
    · have h1 := finrank_span_singleton (K := Ω) hv0
      rw [h0, finrank_top, hV] at h1
      exact absurd h1 (by norm_num)
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (ρ g₀).toLinearMap
  obtain ⟨n, hn, hρn⟩ : ∃ n, 0 < n ∧ ρ g₀ ^ n = 1 := by
    have := hfin
    have hfo : IsOfFinOrder (⟨ρ g₀, g₀, rfl⟩ : ρ.range) := isOfFinOrder_of_finite _
    obtain ⟨n, hn, h1⟩ := hfo.exists_pow_eq_one
    exact ⟨n, hn, by simpa using congrArg Subtype.val h1⟩
  have han : a ^ n = 1 := by
    obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
    have hgv : ρ g₀ v = a • v := hv.apply_eq_smul
    have key : ∀ m : ℕ, (ρ g₀ ^ m) v = a ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, LinearEquiv.mul_apply, hgv, map_smul, ih, smul_smul, pow_succ']
    have h1 : v = a ^ n • v := by
      have := key n
      rwa [hρn] at this
    have h2 : (a ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv.2)

  let : Algebra k Ω := ι.toAlgebra
  have hιalg : ∀ x : k, algebraMap k Ω x = ι x := fun x => rfl
  have hint : IsIntegral k a := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', ?_⟩
    simp [han]
  let E : IntermediateField k Ω := IntermediateField.adjoin k {a}
  have : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional hint
  have : Finite E := Module.finite_of_finite k
  have haE : a ∈ E.toSubfield := IntermediateField.mem_adjoin_simple_self k a
  have hιE : ∀ y, y ∈ ι.range → y ∈ E.toSubfield := by
    rintro _ ⟨x, rfl⟩
    exact E.algebraMap_mem x

  obtain ⟨b, hb⟩ :=
    Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue E.toSubfield ρ hV
      hirr (fun σ => hιE _ (htr σ)) (fun σ => hιE _ (hdet σ)) g₀ a haE ha (hg₀ a)
  let Amat : (L ≃ₐ[K] L) → Matrix (Fin 2) (Fin 2) Ω := fun g => LinearMap.toMatrix b b (ρ g).toLinearMap
  have hAmat : ∀ g, Amat g = LinearMap.toMatrix b b (ρ g).toLinearMap := fun g => rfl
  let mE : (L ≃ₐ[K] L) → Matrix (Fin 2) (Fin 2) E := fun g => Matrix.of fun i j => ⟨Amat g i j, hb g i j⟩
  have hmE : ∀ g, (mE g).map (algebraMap E Ω) = Amat g := fun g => rfl
  have hAmul : ∀ g h, Amat (g * h) = Amat g * Amat h := fun g h => by
    simp only [hAmat, map_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]
  have hinjmap : Function.Injective fun N : Matrix (Fin 2) (Fin 2) E => N.map (algebraMap E Ω) :=
    Matrix.map_injective (algebraMap E Ω).injective
  have hmEmul : ∀ g h, mE (g * h) = mE g * mE h := fun g h =>
    hinjmap (by simp only [Matrix.map_mul, hmE, hAmul])
  have hdetE : ∀ g, (mE g).det ≠ 0 := by
    intro g h0
    have h1 := congrArg (algebraMap E Ω) h0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmE, map_zero, hAmat, LinearMap.det_toMatrix,
      ← LinearEquiv.coe_det] at h1
    exact (LinearEquiv.det (ρ g)).ne_zero h1
  let φ : (L ≃ₐ[K] L) →* GL (Fin 2) E :=
    MonoidHom.mk' (fun g => Matrix.GeneralLinearGroup.mkOfDetNeZero (mE g) (hdetE g))
      (fun g h => Units.ext (hmEmul g h))
  have hφ : ∀ g, ((φ g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = mE g := fun g => rfl

  have hspanE : Submodule.span E (Set.range fun g => (φ g : Matrix (Fin 2) (Fin 2) E)) = ⊤ := by
    apply span_eq_top_of_span_map_eq_top (algebraMap E Ω)
    have hset : (fun N : Matrix (Fin 2) (Fin 2) E => N.map (algebraMap E Ω)) ''
        Set.range (fun g => (φ g : Matrix (Fin 2) (Fin 2) E)) =
        (LinearMap.toMatrix b b).toLinearMap '' Set.range ρ' := by
      ext N
      simp only [Set.mem_image, Set.mem_range, hφ, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨ρ' g, ⟨g, rfl⟩, (hmE g).symm ▸ rfl⟩
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨mE g, ⟨g, rfl⟩, hmE g⟩
    rw [hset, Submodule.span_image, hspanΩ, Submodule.map_top, LinearEquiv.range]

  have htrE : ∀ g, (mE g).trace ∈ (algebraMap k E).range := by
    intro g
    obtain ⟨x, hx⟩ := htr g
    refine ⟨x, (algebraMap E Ω).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hιalg, hx, LinearMap.trace_eq_matrix_trace Ω b, ← hAmat, ← hmE,
      AddMonoidHom.map_trace]
  have hdetE' : ∀ g, (mE g).det ∈ (algebraMap k E).range := by
    intro g
    obtain ⟨x, hx⟩ := hdet g
    refine ⟨x, (algebraMap E Ω).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hιalg, hx, ← LinearMap.det_toMatrix b, ← hAmat, ← hmE,
      RingHom.map_det, RingHom.mapMatrix_apply]
  have hcoeff : ∀ g i, ((φ g : Matrix (Fin 2) (Fin 2) E)).charpoly.coeff i ∈ (algebraMap k E).range := by
    intro g i
    rw [hφ]
    by_cases hi : i < 3
    · rw [Matrix.charpoly_fin_two]
      interval_cases i
      · simpa using hdetE' g
      · simpa using Subring.neg_mem _ (htrE g)
      · simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · exact Subring.zero_mem _
      · rw [Matrix.charpoly_natDegree_eq_dim]
        simp only [Fintype.card_fin]
        omega
  obtain ⟨ρ₁, Q, hQ⟩ :=
    Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top
      (K := k) (L := E) φ hspanE hcoeff

  let R : Subring E := (algebraMap k E).range
  have hRinj : Function.Injective (algebraMap k E).rangeRestrict := fun x y hxy =>
    (algebraMap k E).injective (congrArg Subtype.val hxy)
  let e : k ≃+* R := RingEquiv.ofBijective (algebraMap k E).rangeRestrict
    ⟨hRinj, (algebraMap k E).rangeRestrict_surjective⟩
  have he : ∀ r : R, algebraMap k E (e.symm.toRingHom r) = (r : E) := by
    intro r
    have : ((e (e.symm r) : R) : E) = (r : E) := by rw [e.apply_symm_apply]
    exact this
  let ρ₀' : (L ≃ₐ[K] L) →* GL (Fin 2) k := (Matrix.GeneralLinearGroup.map e.symm.toRingHom).comp ρ₁
  have hρ₀' : ∀ g, ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).map (algebraMap k E) =
      ((ρ₁ g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map R.subtype := by
    intro g
    refine Matrix.ext fun i j => ?_
    simp only [ρ₀', MonoidHom.comp_apply, Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply]
    exact he _

  let P : GL (Fin 2) Ω := Matrix.GeneralLinearGroup.map (algebraMap E Ω) Q
  have hmaster : ∀ g, ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).map ι =
      ((P⁻¹ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) * Amat g * (P : Matrix (Fin 2) (Fin 2) Ω) := by
    intro g
    have h1 : ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).map ι =
        ((((ρ₁ g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map R.subtype).map (algebraMap E Ω)) := by
      rw [← hρ₀', Matrix.map_map]
      congr 1
    rw [h1, ← hQ g]
    simp only [Matrix.map_mul]
    congr 2
  let V₀ := Fin 2 → k
  let ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V₀).toMonoidHom.comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp ρ₀'
  have hρ₀ : ∀ g, (ρ₀ g).toLinearMap = Matrix.toLin' ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) :=
    fun g => rfl
  have hρ₀apply : ∀ g (v : V₀), ρ₀ g v = ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v := by
    intro g v
    rw [← LinearEquiv.coe_coe, hρ₀, Matrix.toLin'_apply]

  have htr₀ : ∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap := by
    intro σ
    rw [hρ₀, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', AddMonoidHom.map_trace, hmaster, Matrix.trace_units_conj', hAmat,
      ← LinearMap.trace_eq_matrix_trace]
  have hdet₀ : ∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap := by
    intro σ
    rw [hρ₀, LinearMap.det_toLin', RingHom.map_det, RingHom.mapMatrix_apply, hmaster,
      Matrix.det_units_conj', hAmat, LinearMap.det_toMatrix]
  refine ⟨V₀, inferInstance, inferInstance, ρ₀, by simp [V₀], ?_, ?_, htr₀, hdet₀, ?_⟩
  ·
    intro ℓ hℓ hℓN A hA σ hσ
    apply ι.injective
    rw [hdet₀, map_natCast]
    exact hcyc ℓ hℓ hℓN A hA σ hσ
  ·
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    have h1 : Amat σ = 1 := by
      rw [hAmat, hσ]
      exact LinearMap.toMatrix_id b
    have h2 : ((ρ₀' σ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).map ι = (1 : Matrix (Fin 2) (Fin 2) k).map ι := by
      rw [hmaster, h1, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero ι) (map_one ι)]
    have h3 : ρ₀' σ = 1 := Units.ext (by
      have := Matrix.map_injective ι.injective h2
      simpa using this)
    show ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V₀).toMonoidHom.comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom) (ρ₀' σ) = 1
    rw [h3, map_one]
  ·
    have hspank : Submodule.span k (Set.range fun g => ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) = ⊤ := by
      apply span_eq_top_of_span_map_eq_top (algebraMap k E)

      have hset : (fun N : Matrix (Fin 2) (Fin 2) k => N.map (algebraMap k E)) ''
          Set.range (fun g => ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) =
          (conjEquiv Q).toLinearMap '' Set.range (fun g => (φ g : Matrix (Fin 2) (Fin 2) E)) := by
        ext N
        simp only [Set.mem_image, Set.mem_range, LinearEquiv.coe_coe, conjEquiv_apply]
        constructor
        · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
          exact ⟨_, ⟨g, rfl⟩, by rw [hQ g, hρ₀']⟩
        · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
          exact ⟨_, ⟨g, rfl⟩, by rw [hρ₀', ← hQ g]⟩
      rw [hset, Submodule.span_image, hspanE, Submodule.map_top, LinearEquiv.range]
    intro W hW
    have hW' : ∀ g, ∀ v ∈ W, ((ρ₀' g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v ∈ W := by
      intro g v hv
      rw [← hρ₀apply]
      exact hW g v hv
    rcases eq_bot_or_eq_top_of_span_eq_top _ hspank W hW' with rfl | rfl
    · exact ⟨⊤, fun _ _ _ => Submodule.mem_top, isCompl_bot_top⟩
    · exact ⟨⊥, fun σ v hv => by rw [(Submodule.mem_bot k).mp hv, map_zero]; exact Submodule.zero_mem _,
        isCompl_top_bot⟩

end Main

end ResidualDescentAux

theorem exists_semisimple_descent_of_trace_det_mem_range_finite
    {K L : Type} [Field K] [Field L] [Algebra K L] (M p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (V : Type) [AddCommGroup V] [Module Ω V] (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[Ω] V))
    (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2) (hfin : Finite ρ.range)
    (hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range)
    (hcyc : ModularCurve.CyclotomicDeterminant M p ρ) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀)
      (ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      ModularCurve.CyclotomicDeterminant M p ρ₀ ∧
      ρ.ker ≤ ρ₀.ker ∧
      (∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) ∧
      (∀ W : Submodule k V₀, (∀ σ, ∀ v ∈ W, ρ₀ σ v ∈ W) →
        ∃ W' : Submodule k V₀, (∀ σ, ∀ v ∈ W', ρ₀ σ v ∈ W') ∧ IsCompl W W') :=
  ResidualDescentAux.main M p Ω k ι V ρ hp hV hfin hirr htr hdet hcyc

end ModularCurve

end
