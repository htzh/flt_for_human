/-
  The local-finite-type engine of the `K`-finite-family theorem: evaluation
  matrices, finite translate sets, coefficient spans, slice spans and averaged
  intertwiners.

  This is the generic representation-theoretic half of
  `AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous`
  (ported as the kernel `AutomorphicForm.ArchKFiniteFamily.Engine.exists_…`). It
  mentions neither the adèles nor `GL₂`: everything is stated over an abstract
  monoid/group `G`, an abstract monoid `Q` and complex-valued functions.

  * `EvalMatrix` — a finite matrix of evaluations of a family
    `v : Fin n → X → 𝕜`; `linearIndependent 𝕜 v` holds iff some evaluation
    matrix has nonzero determinant (`exists_det_evalMatrix_ne_zero`,
    `linearIndependent_iff_exists_det_evalMatrix_ne_zero`).
  * `UniformRank` — `TranslatesFinite Q f` (the set-indexed translate-span
    finiteness), the translate linear map `rt`, and the Baire/finite-rank core
    `exists_isOpen_subset_forall_det_ne_zero_and_mem_span`.
  * `CoefficientSpan` — the coefficient span of a matrix-valued family `ρ`, its
    finite dimensionality, and the intertwiner-law inclusion
    `span_le_coeffSpan_of_intertwiner`.
  * `SliceSpan` / `SliceCoefficients` — slices of a family and the finite
    expansion of a `π`-span-valued slice, and the membership of the slice
    coefficients in the coefficient span.
  * `AveragedIntertwiner` — averaging a multiplicative matrix law against a
    probability Haar measure on a compact group, producing an invertible
    intertwiner `avg μ ρ s₀ s`.
  * `TranslationCoordinates` — the matrix coordinates `Mm`/`Nm`, their
    multiplication law, continuity, and the finite-coordinate conclusion.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:28–490`
  and `:792–1081` (pinned `aa2d8b3`), the seven generic namespaces of the pin's
  nine-namespace chapter. The later two of these precede the adèlic
  `ArchimedeanIsometryGroup` at the pin's fork. The pin declares every
  namespace `private`; here the engine is the shared cross-theory one and is
  public, so the statements are verbatim and every declaration lands as a
  promotion (the `RepTheory/TypeReproducer.lean` precedent). The pin's
  `p2m_reactivate` plumbing and its `#print` diagnostics are not transcribed.

  Two landed reuse edges are deliberately *not* substituted — the carriers
  differ, so the pin's private forms are kept and the pairs are reported as
  reconciliation candidates (WORKORDER-KF1 §3):
  * `UniformRank.TranslatesFinite` is the set-indexed twin of the public
    `AutomorphicForm.RightTranslatesSpanFinite` (`Adelic/ArchKFinite.lean`),
    which is subgroup-indexed.
  * `UniformRank.rt`/`rt_apply` (and `TranslationCoordinates.Mm`/`Nm`) have
    binder variants in `RepTheory/TypeReproducer.lean` and
    `AutomorphicForm/Adelic/PeterssonSlabPairing.lean`; the pin's forms are kept.
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's `haveI` walls feed instance search (`FiniteDimensional`, `BaireSpace`,
-- `Nonempty`); they are instances, not hypotheses, so the style linter is suppressed.
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Topology

namespace EvalMatrix

variable {𝕜 : Type*} [Field 𝕜] {X : Type*}

-- pin: evalMatrix (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:32)
def evalMatrix {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => v j (x i)

omit [Field 𝕜] in
-- pin: evalMatrix_apply (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:36)
theorem evalMatrix_apply {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X) (i j : Fin n) :
    evalMatrix v x i j = v j (x i) := rfl

-- pin: exists_det_evalMatrix_ne_zero (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:39)
theorem exists_det_evalMatrix_ne_zero :
    ∀ {n : ℕ} (v : Fin n → X → 𝕜), LinearIndependent 𝕜 v →
      ∃ x : Fin n → X, (evalMatrix v x).det ≠ 0
  | 0, _, _ => ⟨Fin.elim0, by rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  | n + 1, v, hv => by
    obtain ⟨x', hx'⟩ :=
      exists_det_evalMatrix_ne_zero (fun j => v j.succ) (hv.comp Fin.succ (Fin.succ_injective n))

    let e : Fin (n + 1) → 𝕜 := fun j =>
      (-1) ^ (j : ℕ) * (Matrix.of fun (i : Fin n) (j' : Fin n) => v (j.succAbove j') (x' i)).det
    have hminor : ∀ (y : X) (j : Fin (n + 1)),
        (evalMatrix v (Fin.cons y x')).submatrix Fin.succ j.succAbove
          = Matrix.of fun (i : Fin n) (j' : Fin n) => v (j.succAbove j') (x' i) := by
      intro y j
      ext i j'
      simp [evalMatrix, Matrix.submatrix, Fin.cons_succ]
    have hexp : ∀ y : X, (evalMatrix v (Fin.cons y x')).det = ∑ j, e j * v j y := by
      intro y
      rw [Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hminor y j]
      simp only [e, evalMatrix_apply, Fin.cons_zero]
      ring
    have he0 : e 0 ≠ 0 := by
      have h0 : (Matrix.of fun (i : Fin n) (j' : Fin n) => v ((0 : Fin (n + 1)).succAbove j') (x' i))
          = evalMatrix (fun j => v j.succ) x' := by
        ext i j'
        simp [evalMatrix]
      simp only [e, Fin.val_zero, pow_zero, one_mul, h0]
      exact hx'
    by_cases hy : ∃ y : X, (evalMatrix v (Fin.cons y x')).det ≠ 0
    · obtain ⟨y, hy⟩ := hy
      exact ⟨Fin.cons y x', hy⟩
    · exfalso
      have hzero : ∀ y : X, (evalMatrix v (Fin.cons y x')).det = 0 :=
        fun y => by_contra fun h => hy ⟨y, h⟩
      have hsum : ∑ j, e j • v j = 0 := by
        funext y
        have := hexp y
        rw [hzero y] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact this.symm
      exact he0 (Fintype.linearIndependent_iff.mp hv e hsum 0)

-- pin: linearIndependent_of_det_evalMatrix_ne_zero (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:83)
theorem linearIndependent_of_det_evalMatrix_ne_zero {n : ℕ} (v : Fin n → X → 𝕜)
    (x : Fin n → X) (h : (evalMatrix v x).det ≠ 0) : LinearIndependent 𝕜 v := by
  have hrows : LinearIndependent 𝕜 (fun j => (evalMatrix v x).transpose j) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (by rwa [Matrix.det_transpose])
  let f : (X → 𝕜) →ₗ[𝕜] (Fin n → 𝕜) := LinearMap.pi fun i => LinearMap.proj (x i)
  have hcomp : (⇑f ∘ v) = fun j => (evalMatrix v x).transpose j := by
    funext j i
    rfl
  exact LinearIndependent.of_comp f (by rw [hcomp]; exact hrows)

-- pin: linearIndependent_iff_exists_det_evalMatrix_ne_zero (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:93)
theorem linearIndependent_iff_exists_det_evalMatrix_ne_zero {n : ℕ} (v : Fin n → X → 𝕜) :
    LinearIndependent 𝕜 v ↔ ∃ x : Fin n → X, (evalMatrix v x).det ≠ 0 :=
  ⟨exists_det_evalMatrix_ne_zero v, fun ⟨x, hx⟩ => linearIndependent_of_det_evalMatrix_ne_zero v x hx⟩

-- pin: eq_sum_inv_evalMatrix_mulVec_smul (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:97)
theorem eq_sum_inv_evalMatrix_mulVec_smul {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X)
    (hx : (evalMatrix v x).det ≠ 0) (g : X → 𝕜) (hg : g ∈ Submodule.span 𝕜 (Set.range v)) :
    g = ∑ j, ((evalMatrix v x)⁻¹.mulVec (fun i => g (x i))) j • v j := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := 𝕜)).mp hg
  have hvals : (fun i => (∑ j, c j • v j) (x i)) = (evalMatrix v x).mulVec c := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      evalMatrix_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hinv : (evalMatrix v x)⁻¹.mulVec ((evalMatrix v x).mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  rw [hvals, hinv]

end EvalMatrix

namespace UniformRank

open scoped Pointwise

variable {G : Type*} [Monoid G]

-- pin: TranslatesFinite (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:118)
def TranslatesFinite (Q : Set G) (f : G → ℂ) : Prop :=
  ∃ t : Finset (G → ℂ), ∀ k ∈ Q, (fun g => f (g * k)) ∈ Submodule.span ℂ (t : Set (G → ℂ))

-- pin: rt (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:121)
def rt (x : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun φ := fun g => φ (g * x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- pin: rt_apply (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:126)
theorem rt_apply (x : G) (φ : G → ℂ) (g : G) : rt x φ g = φ (g * x) := rfl

-- pin: rt_translate (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:128)
theorem rt_translate (a b : G) (f : G → ℂ) :
    rt a (fun g => f (g * b)) = fun g => f (g * (a * b)) := by
  funext g
  show f (g * a * b) = f (g * (a * b))
  rw [mul_assoc]

-- pin: exists_finset_subset_forall_mem_span (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:134)
theorem exists_finset_subset_forall_mem_span (Q : Set G) (f : G → ℂ)
    (h : TranslatesFinite Q f) :
    ∃ B : Finset G, (↑B : Set G) ⊆ Q ∧
      ∀ k ∈ Q, (fun g => f (g * k)) ∈
        Submodule.span ℂ ((fun b : G => fun g => f (g * b)) '' (↑B : Set G)) := by
  classical
  obtain ⟨t, ht⟩ := h

  set X : Set (G → ℂ) := (fun b : G => fun g => f (g * b)) '' Q with hX
  have hle : Submodule.span ℂ X ≤ Submodule.span ℂ (t : Set (G → ℂ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact ht k hk
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (t : Set (G → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ t.finite_toSet
  haveI hW : FiniteDimensional ℂ (Submodule.span ℂ X) := Submodule.finiteDimensional_of_le hle
  have hfg : (Submodule.span ℂ X).FG := (Submodule.fg_iff_finiteDimensional _).mpr hW
  obtain ⟨s, hs⟩ := hfg

  have hmem : ∀ v ∈ s, ∃ T : Finset (G → ℂ), (↑T : Set (G → ℂ)) ⊆ X ∧
      v ∈ Submodule.span ℂ (T : Set (G → ℂ)) := by
    intro v hv
    have hvX : v ∈ Submodule.span ℂ X := by
      rw [← hs]
      exact Submodule.subset_span hv
    exact Submodule.mem_span_finite_of_mem_span hvX
  choose T hTX hvT using hmem
  set U : Finset (G → ℂ) := s.attach.biUnion (fun v => T v.1 v.2) with hU
  have hUX : (↑U : Set (G → ℂ)) ⊆ X := by
    intro y hy
    rw [Finset.mem_coe, hU, Finset.mem_biUnion] at hy
    obtain ⟨v, -, hyv⟩ := hy
    exact hTX v.1 v.2 (Finset.mem_coe.mpr hyv)
  have hWU : Submodule.span ℂ X ≤ Submodule.span ℂ (U : Set (G → ℂ)) := by
    rw [← hs, Submodule.span_le]
    intro v hv
    have hv' : v ∈ s := hv
    refine Submodule.span_mono ?_ (hvT v hv')
    intro y hy
    rw [Finset.mem_coe, hU, Finset.mem_biUnion]
    exact ⟨⟨v, hv'⟩, Finset.mem_attach _ _, Finset.mem_coe.mp hy⟩

  have hUX' : (↑U : Set (G → ℂ)) ⊆ (fun b : G => fun g => f (g * b)) '' Q := hUX
  obtain ⟨B, hBQ, hBU⟩ := Finset.subset_set_image_iff.mp hUX'
  refine ⟨B, hBQ, fun k hk => ?_⟩
  have hkX : (fun g => f (g * k)) ∈ Submodule.span ℂ X := Submodule.subset_span ⟨k, hk, rfl⟩
  have h1 := hWU hkX
  rwa [← hBU, Finset.coe_image] at h1

-- pin: translatesFinite_mul (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:183)
theorem translatesFinite_mul (Q₁ Q₂ : Set G) (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (f : G → ℂ) (h₁ : TranslatesFinite Q₁ f) (h₂ : TranslatesFinite Q₂ f) :
    TranslatesFinite (Q₁ * Q₂) f := by
  classical
  obtain ⟨A, hAQ, hA⟩ := exists_finset_subset_forall_mem_span Q₁ f h₁
  obtain ⟨B, hBQ, hB⟩ := exists_finset_subset_forall_mem_span Q₂ f h₂

  refine ⟨(A ×ˢ B).image fun p : G × G => fun g => f (g * (p.1 * p.2)), ?_⟩
  intro k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hk
  set t : Finset (G → ℂ) := (A ×ˢ B).image fun p : G × G => fun g => f (g * (p.1 * p.2)) with ht
  have hgen : ∀ a' ∈ A, ∀ b' ∈ B,
      (fun g => f (g * (a' * b'))) ∈ Submodule.span ℂ (t : Set (G → ℂ)) := by
    intro a' ha' b' hb'
    apply Submodule.subset_span
    rw [ht, Finset.coe_image]
    exact ⟨(a', b'), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨ha', hb'⟩), rfl⟩

  have hstep : ∀ b' ∈ B, rt a (fun g => f (g * b')) ∈ Submodule.span ℂ (t : Set (G → ℂ)) := by
    intro b' hb'
    have e : rt a (fun g => f (g * b')) = rt b' (fun g => f (g * a)) := by
      rw [rt_translate, rt_translate, hcomm a ha b' (hBQ hb')]
    rw [e]

    have hRa := hA a ha
    have h2 : rt b' (fun g => f (g * a)) ∈
        Submodule.span ℂ ((rt b') '' ((fun a' : G => fun g => f (g * a')) '' (↑A : Set G))) := by
      rw [Submodule.span_image]
      exact Submodule.mem_map_of_mem hRa
    refine Submodule.span_le.mpr ?_ h2
    rintro _ ⟨_, ⟨a', ha', rfl⟩, rfl⟩
    rw [rt_translate, ← hcomm a' (hAQ ha') b' (hBQ hb')]
    exact hgen a' ha' b' hb'

  rw [← rt_translate a b f]
  have h3 : rt a (fun g => f (g * b)) ∈
      Submodule.span ℂ ((rt a) '' ((fun b' : G => fun g => f (g * b')) '' (↑B : Set G))) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map_of_mem (hB b hb)
  refine Submodule.span_le.mpr ?_ h3
  rintro _ ⟨_, ⟨b', hb', rfl⟩, rfl⟩
  exact hstep b' hb'

-- pin: exists_isOpen_subset_forall_det_ne_zero_and_mem_span (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:227)
theorem exists_isOpen_subset_forall_det_ne_zero_and_mem_span (Q : Set G) (u : ℂ → G → ℂ)
    (hfin : ∀ s, TranslatesFinite Q (u s)) (hc : ∀ g, Continuous fun s => u s g)
    (U₀ : Set ℂ) (hU₀ : IsOpen U₀) (hne : U₀.Nonempty) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ U₀ ∧
      ∃ (r : ℕ) (κ : Fin r → G) (x : Fin r → G), (∀ j, κ j ∈ Q) ∧
        (∀ s ∈ U, (Matrix.of fun i j => u s (x i * κ j)).det ≠ 0) ∧
        ∀ s ∈ U, ∀ k ∈ Q,
          (fun g => u s (g * k)) ∈ Submodule.span ℂ (Set.range fun j => fun g => u s (g * κ j)) := by
  classical

  have hcontdet : ∀ {n : ℕ} (κ : Fin n → G) (x : Fin n → G),
      Continuous fun s : ℂ => (Matrix.of fun i j => u s (x i * κ j)).det := by
    intro n κ x
    have hprod : ∀ σ : Equiv.Perm (Fin n), Continuous fun s : ℂ => ∏ i, u s (x (σ i) * κ i) :=
      fun σ => continuous_finsetProd _ fun i _ => hc (x (σ i) * κ i)
    simp only [Matrix.det_apply, Matrix.of_apply]
    exact continuous_finsetSum _ fun σ _ => (hprod σ).const_smul _

  have hbound : ∀ s, ∃ n : ℕ, ∀ κ : Fin (n + 1) → G, (∀ j, κ j ∈ Q) → ∀ x : Fin (n + 1) → G,
      (Matrix.of fun i j => u s (x i * κ j)).det = 0 := by
    intro s
    obtain ⟨t, ht⟩ := hfin s
    refine ⟨t.card, fun κ hκ x => ?_⟩
    by_contra hdet
    have hind : LinearIndependent ℂ (fun j => fun g => u s (g * κ j)) :=
      EvalMatrix.linearIndependent_of_det_evalMatrix_ne_zero _ x hdet
    have hmem : ∀ j, (fun g => u s (g * κ j)) ∈ Submodule.span ℂ (t : Set (G → ℂ)) :=
      fun j => ht (κ j) (hκ j)
    have hind' : LinearIndependent ℂ
        (fun j => (⟨_, hmem j⟩ : Submodule.span ℂ (t : Set (G → ℂ)))) :=
      LinearIndependent.of_comp (Submodule.span ℂ (t : Set (G → ℂ))).subtype hind
    have h1 := hind'.fintype_card_le_finrank
    have h2 : Module.finrank ℂ (Submodule.span ℂ (t : Set (G → ℂ))) ≤ t.card :=
      finrank_span_finset_le_card (R := ℂ) t
    rw [Fintype.card_fin] at h1
    omega

  haveI : BaireSpace U₀ := hU₀.baireSpace
  haveI : Nonempty U₀ := hne.to_subtype
  let F : ℕ → Set U₀ := fun m =>
    ⋂ (κ : Fin (m + 1) → G) (_ : ∀ j, κ j ∈ Q) (x : Fin (m + 1) → G),
      {s : U₀ | (Matrix.of fun i j => u s.1 (x i * κ j)).det = 0}
  have hF : ∀ m, IsClosed (F m) := fun m =>
    isClosed_iInter fun κ => isClosed_iInter fun _ => isClosed_iInter fun x =>
      isClosed_eq ((hcontdet κ x).comp continuous_subtype_val) continuous_const
  have hcover : ⋃ m, F m = Set.univ := by
    refine Set.eq_univ_of_forall fun s => ?_
    obtain ⟨n, hn⟩ := hbound s.1
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iInter.mpr fun κ => Set.mem_iInter.mpr fun hκ =>
      Set.mem_iInter.mpr fun x => hn κ hκ x⟩
  obtain ⟨m, s₀, hs₀⟩ := nonempty_interior_of_iUnion_of_closed hF hcover
  have hU₁open : IsOpen (Subtype.val '' interior (F m)) :=
    hU₀.isOpenMap_subtype_val _ isOpen_interior
  have hU₁sub : Subtype.val '' interior (F m) ⊆ U₀ := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hU₁rank : ∀ s ∈ Subtype.val '' interior (F m), ∀ κ : Fin (m + 1) → G, (∀ j, κ j ∈ Q) →
      ∀ x : Fin (m + 1) → G, (Matrix.of fun i j => u s (x i * κ j)).det = 0 := by
    rintro _ ⟨s, hs, rfl⟩ κ hκ x
    have hsF : s ∈ F m := interior_subset hs
    exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hsF κ) hκ) x

  let A : ℕ → Prop := fun n => ∃ s ∈ Subtype.val '' interior (F m), ∃ κ : Fin n → G,
    (∀ j, κ j ∈ Q) ∧ ∃ x : Fin n → G, (Matrix.of fun i j => u s (x i * κ j)).det ≠ 0
  have hA0 : A 0 :=
    ⟨s₀.1, ⟨s₀, hs₀, rfl⟩, Fin.elim0, fun j => Fin.elim0 j, Fin.elim0, by
      rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  obtain ⟨r, hAr, hnot⟩ : ∃ r, A r ∧ ¬ A (r + 1) := by
    refine ⟨Nat.findGreatest A m, Nat.findGreatest_spec (P := A) (Nat.zero_le m) hA0, ?_⟩
    by_cases h : Nat.findGreatest A m + 1 ≤ m
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h
    · have hrm : Nat.findGreatest A m = m := by
        have := Nat.findGreatest_le (P := A) m
        omega
      rw [hrm]
      rintro ⟨s, hs, κ, hκ, x, hdet⟩
      exact hdet (hU₁rank s hs κ hκ x)
  obtain ⟨s₁, hs₁, κ, hκ, x, hdet₁⟩ := hAr

  refine ⟨Subtype.val '' interior (F m) ∩ {s | (Matrix.of fun i j => u s (x i * κ j)).det ≠ 0},
    hU₁open.inter (isOpen_ne_fun (hcontdet κ x) continuous_const), ⟨s₁, hs₁, hdet₁⟩,
    fun s hs => hU₁sub hs.1, r, κ, x, hκ, fun s hs => hs.2, ?_⟩
  intro s hs k hk
  by_contra hnotmem
  apply hnot
  have hind : LinearIndependent ℂ (fun j => fun g => u s (g * κ j)) :=
    EvalMatrix.linearIndependent_of_det_evalMatrix_ne_zero _ x hs.2
  have hind' : LinearIndependent ℂ
      (Fin.cons (fun g => u s (g * k)) (fun j => fun g => u s (g * κ j)) : Fin (r + 1) → G → ℂ) :=
    linearIndependent_finCons.mpr ⟨hind, hnotmem⟩
  have hfam : (fun j => fun g => u s (g * (Fin.cons k κ : Fin (r + 1) → G) j))
      = (Fin.cons (fun g => u s (g * k)) (fun j => fun g => u s (g * κ j)) : Fin (r + 1) → G → ℂ) := by
    funext j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  obtain ⟨x', hx'⟩ := EvalMatrix.exists_det_evalMatrix_ne_zero
    (fun j => fun g => u s (g * (Fin.cons k κ : Fin (r + 1) → G) j)) (by rw [hfam]; exact hind')
  exact ⟨s, hs.1, Fin.cons k κ, fun j => by refine Fin.cases ?_ (fun j' => ?_) j <;> simp [hk, hκ],
    x', hx'⟩

end UniformRank

namespace CoefficientSpan

variable {Q : Type*} [Monoid Q]

-- pin: coeffSpan (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:335)
def coeffSpan {r : ℕ} (ρ : Q → Matrix (Fin r) (Fin r) ℂ) : Submodule ℂ (Q → ℂ) :=
  Submodule.span ℂ (Set.range fun p : Fin r × Fin r => fun q => ρ q p.1 p.2)

omit [Monoid Q] in

-- pin: finiteDimensional_coeffSpan (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:340)
theorem finiteDimensional_coeffSpan {r : ℕ} (ρ : Q → Matrix (Fin r) (Fin r) ℂ) :
    FiniteDimensional ℂ (coeffSpan ρ) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range _)

-- pin: span_le_coeffSpan_of_translate (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:344)
theorem span_le_coeffSpan_of_translate {r : ℕ} (b : Fin r → Q → ℂ)
    (ρ : Q → Matrix (Fin r) (Fin r) ℂ)
    (hlaw : ∀ (q x : Q) (j : Fin r), b j (x * q) = ∑ i, ρ q i j * b i x) :
    Submodule.span ℂ (Set.range b) ≤ coeffSpan ρ := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hb : b j = ∑ i, b i 1 • (fun q => ρ q i j) := by
    funext q
    have h := hlaw q 1 j
    rw [one_mul] at h
    rw [h, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hb]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

omit [Monoid Q] in

-- pin: coeffSpan_le_of_intertwiner (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:362)
theorem coeffSpan_le_of_intertwiner {r : ℕ} (ρ ρ₀ : Q → Matrix (Fin r) (Fin r) ℂ)
    (T : Matrix (Fin r) (Fin r) ℂ) (hT : IsUnit T) (hconj : ∀ q, T * ρ q = ρ₀ q * T) :
    coeffSpan ρ ≤ coeffSpan ρ₀ := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hρ : ∀ q, ρ q = T⁻¹ * (ρ₀ q * T) := fun q => by
    rw [← hconj q, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul T hdet, Matrix.one_mul]
  unfold coeffSpan
  rw [Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  have hcoeff : (fun q => ρ q i j)
      = ∑ a, ∑ c, (T⁻¹ i a * T c j) • (fun q => ρ₀ q a c) := by
    funext q
    simp only [hρ q, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  show (fun q => ρ q i j)
      ∈ Submodule.span ℂ (Set.range fun p : Fin r × Fin r => fun q => ρ₀ q p.1 p.2)
  rw [hcoeff]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, c), rfl⟩)

-- pin: span_le_coeffSpan_of_intertwiner (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:382)
theorem span_le_coeffSpan_of_intertwiner {r : ℕ} (b : Fin r → Q → ℂ)
    (ρ ρ₀ : Q → Matrix (Fin r) (Fin r) ℂ)
    (hlaw : ∀ (q x : Q) (j : Fin r), b j (x * q) = ∑ i, ρ q i j * b i x)
    (T : Matrix (Fin r) (Fin r) ℂ) (hT : IsUnit T) (hconj : ∀ q, T * ρ q = ρ₀ q * T) :
    Submodule.span ℂ (Set.range b) ≤ coeffSpan ρ₀ :=
  (span_le_coeffSpan_of_translate b ρ hlaw).trans (coeffSpan_le_of_intertwiner ρ ρ₀ T hT hconj)

end CoefficientSpan

namespace SliceSpan

variable {G : Type*} [Mul G] {Q : Type*}

-- pin: finiteDimensional_pi_const (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:398)
theorem finiteDimensional_pi_const {ι : Type*} [Finite ι] {X : Type*} [AddCommGroup X]
    [Module ℂ X] (W₀ : Submodule ℂ X) [FiniteDimensional ℂ W₀] :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : ι => W₀) :=
  Module.Finite.iff_fg.mpr (Submodule.fg_pi fun _ => Module.Finite.iff_fg.mp inferInstance)

-- pin: slices (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:403)
def slices (ι : Q → G) (reps : Finset G) (f : G → ℂ) : reps → Q → ℂ :=
  fun c q => f (ι q * c)

-- pin: exists_forall_mem_exists_forall_eq_sum (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:406)
theorem exists_forall_mem_exists_forall_eq_sum (ι : Q → G) (reps : Finset G) (H : Set G)
    (K : Set G) (hcover : ∀ k ∈ K, ∃ q : Q, ∃ c ∈ reps, ∃ h ∈ H, k = ι q * c * h)
    (u : ℂ → G → ℂ) (U : Set ℂ) (hinv : ∀ s ∈ U, ∀ g : G, ∀ h ∈ H, u s (g * h) = u s g)
    (V : Submodule ℂ (reps → Q → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ s ∈ U, slices ι reps (u s) ∈ V) :
    ∃ (n : ℕ) (σ : Fin n → ℂ), (∀ i, σ i ∈ U) ∧
      ∀ s ∈ U, ∃ a : Fin n → ℂ, ∀ k ∈ K, u s k = ∑ i, a i * u (σ i) k := by
  classical
  let f : U → (reps → Q → ℂ) := fun s => slices ι reps (u s.1)
  have hle : Submodule.span ℂ (Set.range f) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact hV s.1 s.2
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
    Submodule.finiteDimensional_of_le hle
  obtain ⟨t, htf, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := ℂ) (Set.range f)).mp
    ((Module.Finite.iff_fg (R := ℂ)).mp inferInstance)
  choose par hpar using htf
  let pick : t → U := fun w => par w.2
  have hpick : ∀ w : t, slices ι reps (u (pick w).1) = w.1 := fun w => hpar w.2
  let e := t.equivFin
  refine ⟨t.card, fun i => (pick (e.symm i)).1, fun i => (pick (e.symm i)).2, fun s hs => ?_⟩
  have hsub : Submodule.span ℂ (t : Set (reps → Q → ℂ))
      ≤ Submodule.span ℂ (Set.range fun i => slices ι reps (u (pick (e.symm i)).1)) := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨i, hi⟩ : ∃ i, e.symm i = ⟨v, hv⟩ := ⟨e ⟨v, hv⟩, e.symm_apply_apply _⟩
    refine Submodule.subset_span ⟨i, ?_⟩
    show slices ι reps (u (pick (e.symm i)).1) = v
    rw [hi]
    exact hpick ⟨v, hv⟩
  have h1 : slices ι reps (u s) ∈ Submodule.span ℂ (Set.range f) :=
    Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
  rw [hspan] at h1
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hsub h1)
  refine ⟨a, fun k hk => ?_⟩
  obtain ⟨q, c, hc, h, hh, rfl⟩ := hcover k hk
  rw [hinv s hs _ h hh]
  simp only [fun i => hinv _ (pick (e.symm i)).2 (ι q * c) h hh]
  have hcq := congrFun (congrFun ha ⟨c, hc⟩) q
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, slices] at hcq
  exact hcq.symm

end SliceSpan

namespace SliceCoefficients

variable {G : Type*} [Monoid G] {Q : Type*} [Monoid Q]

-- pin: slices_mem_pi_coeffSpan (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:458)
theorem slices_mem_pi_coeffSpan {r : ℕ} (ι : Q →* G) (reps : Finset G)
    (hcomm : ∀ (q : Q), ∀ c ∈ reps, ι q * c = c * ι q)
    (u : ℂ → G → ℂ) (κ : Fin r → Q) (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ)
    (ρ₀ : Q → Matrix (Fin r) (Fin r) ℂ) (U W : Set ℂ) (hWU : W ⊆ U)
    (hspan : ∀ s ∈ U, ∀ q : Q, (fun g => u s (g * ι q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => u s (g * ι (κ j))))
    (hlaw : ∀ s ∈ U, ∀ (q : Q) (g : G) (j : Fin r),
      u s (g * ι q * ι (κ j)) = ∑ i, ρ s q i j * u s (g * ι (κ i)))
    (hT : ∀ s ∈ W, ∃ T : Matrix (Fin r) (Fin r) ℂ, IsUnit T ∧ ∀ q : Q, T * ρ s q = ρ₀ q * T) :
    ∀ s ∈ W, SliceSpan.slices (⇑ι) reps (u s) ∈
      Submodule.pi Set.univ (fun _ : reps => CoefficientSpan.coeffSpan ρ₀) := by
  intro s hs
  obtain ⟨T, hTu, hconj⟩ := hT s hs
  rw [Submodule.mem_pi]
  intro c _
  show (fun x : Q => u s (ι x * (c : G))) ∈ CoefficientSpan.coeffSpan ρ₀
  refine CoefficientSpan.span_le_coeffSpan_of_intertwiner
    (fun j x => u s (ι x * (c : G) * ι (κ j))) (ρ s) ρ₀ ?_ T hTu hconj ?_
  · intro q x j
    show u s (ι (x * q) * (c : G) * ι (κ j)) = ∑ i, ρ s q i j * u s (ι x * (c : G) * ι (κ i))
    rw [map_mul, mul_assoc (ι x) (ι q) (c : G), hcomm q c c.2, ← mul_assoc]
    exact hlaw s (hWU hs) q (ι x * (c : G)) j
  · obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hspan s (hWU hs) 1)
    have hfun : (fun x : Q => u s (ι x * (c : G)))
        = ∑ j, d j • (fun x : Q => u s (ι x * (c : G) * ι (κ j))) := by
      funext x
      have h := congrFun hd (ι x * (c : G))
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_one, mul_one] at h ⊢
      exact h.symm
    rw [hfun]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end SliceCoefficients

namespace AveragedIntertwiner

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

section Body

variable {r : ℕ} {U : Set ℂ} {ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ}

omit [Group Q] [IsTopologicalGroup Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
-- pin: continuous_of_mem (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:802)
theorem continuous_of_mem
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s : ℂ} (hs : s ∈ U) :
    Continuous (ρ s) := by
  have h : ContinuousOn ((fun p : ℂ × Q => ρ p.1 p.2) ∘ fun q : Q => (s, q)) Set.univ :=
    hρ_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun q _ => ⟨hs, Set.mem_univ q⟩)
  exact continuousOn_univ.mp h

-- pin: kern (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:810)
noncomputable def kern (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ) (s₀ s : ℂ) (q : Q) :
    Matrix (Fin r) (Fin r) ℂ :=
  ρ s₀ q * ρ s q⁻¹

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
-- pin: continuous_kern (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:815)
theorem continuous_kern
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ s : ℂ}
    (hs₀ : s₀ ∈ U) (hs : s ∈ U) : Continuous (kern ρ s₀ s) := by
  unfold kern
  exact (continuous_of_mem hρ_cont hs₀).matrix_mul ((continuous_of_mem hρ_cont hs).comp continuous_inv)

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
-- pin: continuousOn_kern (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:822)
theorem continuousOn_kern
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (i j : Fin r) : ContinuousOn (fun p : ℂ × Q => kern ρ s₀ p.1 p.2 i j) (U ×ˢ Set.univ) := by
  have h1 : ContinuousOn (fun p : ℂ × Q => ρ s₀ p.2) (U ×ˢ Set.univ) :=
    ((continuous_of_mem hρ_cont hs₀).comp continuous_snd).continuousOn
  have h2 : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2⁻¹) (U ×ˢ Set.univ) :=
    hρ_cont.comp (continuous_fst.prodMk continuous_snd.inv).continuousOn
      (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  rw [continuousOn_iff_continuous_domRestrict] at h1 h2 ⊢
  exact (h1.matrix_mul h2).matrix_elem i j

variable (μ : Measure Q) [IsProbabilityMeasure μ]

-- pin: integrable_kern (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:835)
theorem integrable_kern
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ s : ℂ}
    (hs₀ : s₀ ∈ U) (hs : s ∈ U) (i j : Fin r) : Integrable (fun q => kern ρ s₀ s q i j) μ := by
  rw [← integrableOn_univ]
  exact ((continuous_kern hρ_cont hs₀ hs).matrix_elem i j).continuousOn.integrableOn_compact'
    isCompact_univ MeasurableSet.univ

-- pin: avg (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:842)
noncomputable def avg (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ) (s₀ s : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∫ q, kern ρ s₀ s q i j ∂μ

omit [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [BorelSpace Q] in
-- pin: avg_self (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:847)
theorem avg_self (hρ_one : ∀ s ∈ U, ρ s 1 = 1)
    (hρ_mul : ∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q') {s₀ : ℂ} (hs₀ : s₀ ∈ U) :
    avg μ ρ s₀ s₀ = 1 := by
  have h : ∀ q : Q, kern ρ s₀ s₀ q = 1 := fun q => by
    rw [kern, ← hρ_mul s₀ hs₀, mul_inv_cancel, hρ_one s₀ hs₀]
  ext i j
  simp only [avg, Matrix.of_apply, h, integral_const, probReal_univ, one_smul]

-- pin: avg_mul (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:855)
theorem avg_mul [μ.IsMulLeftInvariant]
    (hρ_mul : ∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q')
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ s : ℂ}
    (hs₀ : s₀ ∈ U) (hs : s ∈ U) (q' : Q) : avg μ ρ s₀ s * ρ s q' = ρ s₀ q' * avg μ ρ s₀ s := by
  ext i j
  have hL : (avg μ ρ s₀ s * ρ s q') i j = ∫ q, (kern ρ s₀ s q * ρ s q') i j ∂μ := by
    simp only [Matrix.mul_apply, avg, Matrix.of_apply]
    rw [integral_finsetSum _ (fun k _ => (integrable_kern μ hρ_cont hs₀ hs i k).mul_const (ρ s q' k j))]
    simp only [integral_mul_const]
  have hR : (ρ s₀ q' * avg μ ρ s₀ s) i j = ∫ q, (ρ s₀ q' * kern ρ s₀ s q) i j ∂μ := by
    simp only [Matrix.mul_apply, avg, Matrix.of_apply]
    rw [integral_finsetSum _ (fun k _ => (integrable_kern μ hρ_cont hs₀ hs k j).const_mul (ρ s₀ q' i k))]
    simp only [integral_const_mul]
  have h1 : ∀ q : Q, kern ρ s₀ s q * ρ s q' = ρ s₀ q * ρ s (q⁻¹ * q') := fun q => by
    rw [kern, mul_assoc, hρ_mul s hs]
  have h2 : ∀ q : Q, ρ s₀ q' * kern ρ s₀ s q = ρ s₀ (q' * q) * ρ s q⁻¹ := fun q => by
    rw [kern, ← mul_assoc, hρ_mul s₀ hs₀]
  rw [hL, hR]
  simp only [h1, h2]
  calc ∫ q, (ρ s₀ q * ρ s (q⁻¹ * q')) i j ∂μ
      = ∫ q, (ρ s₀ (q' * q) * ρ s ((q' * q)⁻¹ * q')) i j ∂μ :=
        (integral_mul_left_eq_self (μ := μ) (fun q => (ρ s₀ q * ρ s (q⁻¹ * q')) i j) q').symm
    _ = ∫ q, (ρ s₀ (q' * q) * ρ s q⁻¹) i j ∂μ := by
        congr 1
        funext q
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

-- pin: continuousAt_avg (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:882)
theorem continuousAt_avg (hU : IsOpen U)
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ U) : ContinuousAt (fun s => avg μ ρ s₀ s) s₀ := by
  obtain ⟨N, hN_nhds, hNU, hN_cpt⟩ := local_compact_nhds (hU.mem_nhds hs₀)
  refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  simp only [avg, Matrix.of_apply]
  have hK := continuousOn_kern hρ_cont hs₀ i j
  obtain ⟨C, hC⟩ :=
    (hN_cpt.prod isCompact_univ).exists_bound_of_continuousOn
      (hK.mono (Set.prod_mono hNU Set.Subset.rfl))
  refine continuousAt_of_dominated (F := fun s q => kern ρ s₀ s q i j) (bound := fun _ => C)
    ?_ ?_ (integrable_const C) ?_
  · filter_upwards [hU.mem_nhds hs₀] with s hs
    exact ((continuous_kern hρ_cont hs₀ hs).matrix_elem i j).aestronglyMeasurable
  · filter_upwards [hN_nhds] with s hs
    exact ae_of_all μ fun q => hC (s, q) ⟨hs, Set.mem_univ q⟩
  · refine ae_of_all μ fun q => ?_
    have hat : ContinuousAt (fun p : ℂ × Q => kern ρ s₀ p.1 p.2 i j) (s₀, q) :=
      hK.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hs₀, Set.mem_univ q⟩)
    have hf : ContinuousAt (fun s : ℂ => (s, q)) s₀ := (continuous_id.prodMk continuous_const).continuousAt
    exact ContinuousAt.comp (g := fun p : ℂ × Q => kern ρ s₀ p.1 p.2 i j) (f := fun s : ℂ => (s, q))
      (x := s₀) hat hf

end Body

-- pin: exists_isOpen_forall_exists_isUnit_mul_eq_mul (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:908)
theorem exists_isOpen_forall_exists_isUnit_mul_eq_mul
    (μ : Measure Q) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (r : ℕ) (U : Set ℂ) (hU : IsOpen U) (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ)
    (hρ_one : ∀ s ∈ U, ρ s 1 = 1)
    (hρ_mul : ∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q')
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) :
    ∀ s₀ ∈ U, ∃ U' : Set ℂ, IsOpen U' ∧ s₀ ∈ U' ∧ U' ⊆ U ∧
      ∀ s ∈ U', ∃ T : Matrix (Fin r) (Fin r) ℂ, IsUnit T ∧ ∀ q : Q, T * ρ s q = ρ s₀ q * T := by
  intro s₀ hs₀
  have hdet : ContinuousAt (fun s => (avg μ ρ s₀ s).det) s₀ :=
    (continuous_id.matrix_det).continuousAt.comp (continuousAt_avg μ hU hρ_cont hs₀)
  have h1 : (avg μ ρ s₀ s₀).det ≠ 0 := by
    rw [avg_self μ hρ_one hρ_mul hs₀, Matrix.det_one]
    exact one_ne_zero
  have hUev : ∀ᶠ s in nhds s₀, s ∈ U := Filter.eventually_mem_set.2 (hU.mem_nhds hs₀)
  have hev : {s : ℂ | s ∈ U ∧ (avg μ ρ s₀ s).det ≠ 0} ∈ nhds s₀ := hUev.and (hdet.eventually_ne h1)
  obtain ⟨V, hV, hV_open, hs₀V⟩ := mem_nhds_iff.mp hev
  refine ⟨V, hV_open, hs₀V, fun s hs => ?_, fun s hs => ?_⟩
  · have hs' : s ∈ U ∧ (avg μ ρ s₀ s).det ≠ 0 := hV hs
    exact hs'.1
  · have hs' : s ∈ U ∧ (avg μ ρ s₀ s).det ≠ 0 := hV hs
    refine ⟨avg μ ρ s₀ s, ?_, fun q => avg_mul μ hρ_mul hρ_cont hs₀ hs'.1 q⟩
    exact (Matrix.isUnit_iff_isUnit_det (avg μ ρ s₀ s)).2 (isUnit_iff_ne_zero.2 hs'.2)

end AveragedIntertwiner

namespace TranslationCoordinates

section Algebra

variable {G : Type*} [Monoid G] {Q : Type*} [Monoid Q] {r : ℕ}

-- pin: Mm (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:941)
noncomputable def Mm (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G) (s : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => u s (x i * ι (κ j))

-- pin: Nm (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:945)
noncomputable def Nm (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G) (s : ℂ)
    (q : Q) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k j => u s (x k * ι q * ι (κ j))

variable (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G) {s : ℂ}

-- pin: Nm_one (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:951)
theorem Nm_one (s : ℂ) : Nm ι u κ x s 1 = Mm ι u κ x s := by
  ext k j
  simp only [Nm, Mm, Matrix.of_apply, map_one, mul_one]

-- pin: eval_sum (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:955)
theorem eval_sum (e : Fin r → ℂ) :
    (fun k => ∑ i, e i * u s (x k * ι (κ i))) = (Mm ι u κ x s).mulVec e := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Mm, Matrix.of_apply, mul_comm]

-- pin: inv_mulVec_mulVec (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:960)
theorem inv_mulVec_mulVec (hdet : (Mm ι u κ x s).det ≠ 0) (e : Fin r → ℂ) :
    (Mm ι u κ x s)⁻¹.mulVec ((Mm ι u κ x s).mulVec e) = e := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

-- pin: coeff_unique (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:965)
theorem coeff_unique (hdet : (Mm ι u κ x s).det ≠ 0) {c d : Fin r → ℂ}
    (h : ∀ g : G, ∑ i, c i * u s (g * ι (κ i)) = ∑ i, d i * u s (g * ι (κ i))) : c = d := by
  have hM : (Mm ι u κ x s).mulVec c = (Mm ι u κ x s).mulVec d := by
    rw [← eval_sum ι u κ x, ← eval_sum ι u κ x]
    funext k
    exact h (x k)
  calc c = (Mm ι u κ x s)⁻¹.mulVec ((Mm ι u κ x s).mulVec c) := (inv_mulVec_mulVec ι u κ x hdet c).symm
    _ = (Mm ι u κ x s)⁻¹.mulVec ((Mm ι u κ x s).mulVec d) := by rw [hM]
    _ = d := inv_mulVec_mulVec ι u κ x hdet d

-- pin: law (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:975)
theorem law (hdet : (Mm ι u κ x s).det ≠ 0)
    (hspan : ∀ q : Q, (fun g => u s (g * ι q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => u s (g * ι (κ j))))
    (q : Q) (g : G) (j : Fin r) :
    u s (g * ι q * ι (κ j)) = ∑ i, ((Mm ι u κ x s)⁻¹ * Nm ι u κ x s q) i j * u s (g * ι (κ i)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hspan (q * κ j))
  have hc' : ∀ g' : G, u s (g' * ι q * ι (κ j)) = ∑ i, c i * u s (g' * ι (κ i)) := by
    intro g'
    have h := congrFun hc g'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul, ← mul_assoc] at h
    exact h.symm
  have hcol : c = fun i => ((Mm ι u κ x s)⁻¹ * Nm ι u κ x s q) i j := by
    have h1 : (Mm ι u κ x s).mulVec c = fun k => u s (x k * ι q * ι (κ j)) := by
      rw [← eval_sum ι u κ x]
      funext k
      exact (hc' (x k)).symm
    rw [← inv_mulVec_mulVec ι u κ x hdet c, h1]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Nm, Matrix.of_apply]
  rw [hc' g, hcol]

-- pin: mul_of_laws (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:996)
theorem mul_of_laws (hdet : (Mm ι u κ x s).det ≠ 0) (q q' : Q)
    {A B C : Matrix (Fin r) (Fin r) ℂ}
    (hA : ∀ (g : G) (j : Fin r), u s (g * ι q * ι (κ j)) = ∑ i, A i j * u s (g * ι (κ i)))
    (hB : ∀ (g : G) (j : Fin r), u s (g * ι q' * ι (κ j)) = ∑ i, B i j * u s (g * ι (κ i)))
    (hC : ∀ (g : G) (j : Fin r), u s (g * ι (q * q') * ι (κ j)) = ∑ i, C i j * u s (g * ι (κ i))) :
    C = A * B := by
  ext i j
  have hcol : (fun i => C i j) = fun i => (A * B) i j := by
    refine coeff_unique ι u κ x hdet fun g => ?_
    show ∑ i, C i j * u s (g * ι (κ i)) = ∑ i, (A * B) i j * u s (g * ι (κ i))
    rw [← hC g j, map_mul, ← mul_assoc, hB (g * ι q) j]
    simp only [hA g, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  exact congrFun hcol i

end Algebra

section Continuity

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
variable {Q : Type*} [Monoid Q] [TopologicalSpace Q] {r : ℕ}
variable (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G)

omit [ContinuousMul G] [TopologicalSpace Q] in
-- pin: continuous_Mm (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:1022)
theorem continuous_Mm (hu : Continuous fun p : ℂ × G => u p.1 p.2) :
    Continuous fun s : ℂ => Mm ι u κ x s := by
  refine continuous_matrix fun i j => ?_
  simp only [Mm, Matrix.of_apply]
  exact hu.comp (continuous_id.prodMk continuous_const)

-- pin: continuous_Nm (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:1028)
theorem continuous_Nm (hι : Continuous ι) (hu : Continuous fun p : ℂ × G => u p.1 p.2) :
    Continuous fun p : ℂ × Q => Nm ι u κ x p.1 p.2 := by
  refine continuous_matrix fun k j => ?_
  simp only [Nm, Matrix.of_apply]
  have h : Continuous fun p : ℂ × Q => x k * ι p.2 * ι (κ j) :=
    (continuous_const.mul (hι.comp continuous_snd)).mul continuous_const
  exact hu.comp (continuous_fst.prodMk h)

end Continuity

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
variable {Q : Type*} [Monoid Q] [TopologicalSpace Q]

-- pin: exists_forall_one_and_mul_and_continuousOn_and_eq_sum (S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:1042)
theorem exists_forall_one_and_mul_and_continuousOn_and_eq_sum
    (ι : Q →* G) (hι : Continuous ι) (u : ℂ → G → ℂ) (hu : Continuous fun p : ℂ × G => u p.1 p.2)
    (U : Set ℂ) (r : ℕ) (κ : Fin r → Q) (x : Fin r → G)
    (hdet : ∀ s ∈ U, (Matrix.of fun i j => u s (x i * ι (κ j))).det ≠ 0)
    (hspan : ∀ s ∈ U, ∀ q : Q, (fun g => u s (g * ι q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => u s (g * ι (κ j)))) :
    ∃ ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ,
      (∀ s ∈ U, ρ s 1 = 1) ∧
      (∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q') ∧
      ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ) ∧
      ∀ s ∈ U, ∀ (q : Q) (g : G) (j : Fin r),
        u s (g * ι q * ι (κ j)) = ∑ i, ρ s q i j * u s (g * ι (κ i)) := by
  have hdetM : ∀ s ∈ U, (Mm ι u κ x s).det ≠ 0 := hdet
  refine ⟨fun s q => (Mm ι u κ x s)⁻¹ * Nm ι u κ x s q, ?_, ?_, ?_, ?_⟩
  · intro s hs
    show (Mm ι u κ x s)⁻¹ * Nm ι u κ x s 1 = 1
    rw [Nm_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdetM s hs))]
  · intro s hs q q'
    show (Mm ι u κ x s)⁻¹ * Nm ι u κ x s (q * q') =
      (Mm ι u κ x s)⁻¹ * Nm ι u κ x s q * ((Mm ι u κ x s)⁻¹ * Nm ι u κ x s q')
    exact mul_of_laws ι u κ x (hdetM s hs) q q' (law ι u κ x (hdetM s hs) (hspan s hs) q)
      (law ι u κ x (hdetM s hs) (hspan s hs) q') (law ι u κ x (hdetM s hs) (hspan s hs) (q * q'))
  · show ContinuousOn (fun p : ℂ × Q => (Mm ι u κ x p.1)⁻¹ * Nm ι u κ x p.1 p.2) (U ×ˢ Set.univ)
    have hN := continuous_Nm ι u κ x hι hu
    have hM := continuous_Mm ι u κ x hu
    have hinv : ContinuousOn (fun s : ℂ => (Mm ι u κ x s)⁻¹) U := by
      intro s hs
      apply ContinuousAt.continuousWithinAt
      have hR : ContinuousAt (Ring.inverse : ℂ → ℂ) (Mm ι u κ x s).det := by
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ (hdetM s hs)
      exact ContinuousAt.comp (f := fun s => Mm ι u κ x s) (x := s) (continuousAt_matrix_inv _ hR)
        hM.continuousAt
    have h1 : ContinuousOn (fun p : ℂ × Q => (Mm ι u κ x p.1)⁻¹) (U ×ˢ Set.univ) :=
      hinv.comp continuous_fst.continuousOn fun p hp => hp.1
    exact h1.mul hN.continuousOn
  · intro s hs q g j
    exact law ι u κ x (hdetM s hs) (hspan s hs) q g j

end TranslationCoordinates

end
