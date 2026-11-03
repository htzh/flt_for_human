/-
  The span of a differentiable family of flat sections.

  A family of flat sections that depends differentiably on `s` is, at each `s`, a finite complex-linear
  combination of flat sections that are *constant in their `K`-argument*:

    `exists_flat_isInducedSection_sum_eq_of_differentiable_family`: there are `n`, differentiable
    `c : Fin n → ℂ → ℂ` and flat sections `ψ : Fin n → ℂ → AdelicGL2 → ℂ` with the same
    `IsArchKFinite`/`IsKfSmooth`/continuity/holomorphy properties and with

      `ψ i s k = ψ i s' k`   whenever `k` is integral with every `glArch`-component a row isometry,

    such that `φ s g = ∑ i, c i s * ψ i s g`.

  The engine is linear algebra: an `n × n` determinant of evaluation functionals
  (`EvalMatrix`) witnesses that the translates of a finite set of functions have finite rank, and the
  matrix of coefficients is inverted once. This module transcribes the pin's block; the engine itself
  lives in the port's `RepTheory/TranslateSpan.lean` at the pin's names and is imported, not re-proved.

  Transcribed from the pin `S_` file and its `Theorems/` wrapper (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family.lean`
  * `Theorems/Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family.lean`

  The pin's namespace `FlatFamilyDecomposition` is the subject name and is kept. The pin's `S_` file
  imports three mathlib linear-algebra modules; this module names the same three.

  **Visibility follows the pin's**: a `private` prelude of thirteen helpers and the one public headline.

  **Wiring.** `spec/check_port.py` owns the public declaration here: the wrapper and the `S_` file are
  the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.ArchKFiniteFamilyTheorems
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisenstein
import FLTForHuman.AutomorphicForm.Adelic.AdelicIwasawa
import FLTForHuman.RepTheory.TranslateSpan
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace AutomorphicForm

namespace LocalIntertwining

namespace FlatFamilyDecomposition

variable (F : Type) [Field F] [NumberField F]

private abbrev InK (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
    ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))

-- The pin's `KT`, written rather than imported: the advise matches it to `ZbarHomsConj.Qbar`,
-- a subtype of `ℂ`, which is the FR-0134 shape-tier false positive (SET-AF16 §2.1).
private abbrev KT : Type := {k : AdelicGL2 (𝓞 F) F // InK F k}

private def restr (f : AdelicGL2 (𝓞 F) F → ℂ) : KT F → ℂ := fun k => f k.1

variable {F}

private theorem exists_linearIndependent_subfamily {X : Type} {n : ℕ} (v : Fin n → (X → ℂ)) :
    ∃ (m : ℕ) (ι : Fin m → Fin n), LinearIndependent ℂ (v ∘ ι) ∧
      Submodule.span ℂ (Set.range (v ∘ ι)) = Submodule.span ℂ (Set.range v) := by
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ℂ (Set.range v)
  have hbfin : b.Finite := (Set.finite_range v).subset hbsub
  have hft : Fintype b := hbfin.fintype
  let e : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  have hmem : ∀ i : Fin (Fintype.card b), ((e i : b) : X → ℂ) ∈ Set.range v := fun i => hbsub (e i).2
  choose ι hι using hmem
  have hcomp : v ∘ ι = fun i => ((e i : b) : X → ℂ) := funext hι
  have hrange : Set.range (fun i => ((e i : b) : X → ℂ)) = b := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hf
      exact ⟨e.symm ⟨f, hf⟩, by simp⟩
  refine ⟨_, ι, ?_, ?_⟩
  · rw [hcomp]
    exact hbind.comp e e.injective
  · rw [hcomp, hrange, hbspan]

private theorem eq_of_eqOn_of_isOpen {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) (h : Set.EqOn f g U) : f = g := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  obtain ⟨z₀, hz₀⟩ := hne
  funext z
  exact hf'.eqOn_of_preconnected_of_eventuallyEq hg' isPreconnected_univ (Set.mem_univ z₀)
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hz₀) h) (Set.mem_univ z)

variable (F)

private theorem eq_of_isInducedSection_of_forall_inK (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {f g : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (hg : IsInducedSection (𝓞 F) F χ₁ χ₂ g) (h : ∀ k, InK F k → f k = g k) : f = g := by
  funext x
  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F x
  rw [hf b hb k, hg b hb k, h k ⟨hk1, hk2⟩]

private theorem isInducedSection_sum (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {m : ℕ} (c : Fin m → ℂ)
    (ψ : Fin m → AdelicGL2 (𝓞 F) F → ℂ) (hψ : ∀ i, IsInducedSection (𝓞 F) F χ₁ χ₂ (ψ i)) :
    IsInducedSection (𝓞 F) F χ₁ χ₂ (fun g => ∑ i, c i * ψ i g) := by
  have hfun : (fun g => ∑ i, c i * ψ i g) = ∑ i, c i • ψ i := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmem : (∑ i, c i • ψ i) ∈ inducedSectionSubmodule χ₁ χ₂ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hψ i)
  rw [hfun]
  exact hmem

theorem _root_.AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    ∃ (n : ℕ) (c : Fin n → ℂ → ℂ) (ψ : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ i, Differentiable ℂ (c i))
      ∧ (∀ i s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ i s))
      ∧ (∀ i s, IsArchKFinite F (ψ i s))
      ∧ (∀ i s, IsKfSmooth F (ψ i s))
      ∧ (∀ i, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ i p.1 p.2))
      ∧ (∀ i g, Differentiable ℂ (fun s => ψ i s g))
      ∧ (∀ (i : Fin n) (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ i s k = ψ i s' k)
      ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g = ∑ i, c i s * ψ i s g := by
  intro α hα μ ν φ hφ hφK hφf hφjc hφhol

  obtain ⟨U, hU, hne, n, σ, hspan⟩ := AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous F φ hφK hφf hφjc

  have hA1 : ∀ i : Fin n, ∃ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      ψ (σ i) = φ (σ i)
      ∧ (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      ∧ (∀ s, IsArchKFinite F (ψ s))
      ∧ (∀ s, IsKfSmooth F (ψ s))
      ∧ Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)
      ∧ (∀ g, Differentiable ℂ (fun s => ψ s g))
      ∧ ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k :=
    fun i => AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection F hα μ ν (σ i) (φ (σ i)) (hφ (σ i)) (hφK (σ i)) (hφf (σ i))
      (hφjc.comp (continuous_const.prodMk continuous_id))
  choose ψ hψ using hA1

  have hmem : ∀ s ∈ U,
      restr F (φ s) ∈ Submodule.span ℂ (Set.range fun i => restr F (φ (σ i))) := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan s hs
    refine (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).2 ⟨c, ?_⟩
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, restr]
    exact (hc k.1 k.2.1 k.2.2).symm

  obtain ⟨m, ι, hind, hspan'⟩ := exists_linearIndependent_subfamily (fun i => restr F (φ (σ i)))
  obtain ⟨x, hx⟩ := EvalMatrix.exists_det_evalMatrix_ne_zero _ hind
  let Mi : Matrix (Fin m) (Fin m) ℂ := (EvalMatrix.evalMatrix ((fun i => restr F (φ (σ i))) ∘ ι) x)⁻¹
  let cf : ℂ → Fin m → ℂ := fun s => Mi.mulVec (fun l => φ s (x l).1)
  have hcf_hol : ∀ j, Differentiable ℂ (fun s => cf s j) := by
    intro j
    show Differentiable ℂ (fun s => ∑ l, Mi j l * φ s (x l).1)
    exact Differentiable.fun_sum fun l _ => (hφhol (x l).1).const_mul (Mi j l)
  have hcf_U : ∀ s ∈ U, restr F (φ s) = ∑ j, cf s j • restr F (φ (σ (ι j))) := by
    intro s hs
    have hs' : restr F (φ s) ∈ Submodule.span ℂ (Set.range ((fun i => restr F (φ (σ i))) ∘ ι)) := by
      rw [hspan']
      exact hmem s hs
    exact EvalMatrix.eq_sum_inv_evalMatrix_mulVec_smul _ x hx _ hs'

  have hall : ∀ (s : ℂ) (k : KT F), φ s k.1 = ∑ j, cf s j * φ (σ (ι j)) k.1 := by
    intro s k
    have hfun := eq_of_eqOn_of_isOpen (f := fun s => φ s k.1)
      (g := fun s => ∑ j, cf s j * φ (σ (ι j)) k.1) (hφhol k.1)
      (Differentiable.fun_sum fun j _ => (hcf_hol j).mul_const (φ (σ (ι j)) k.1)) hU hne (fun s hs => by
        have h := congrFun (hcf_U s hs) k
        simpa only [restr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h)
    exact congrFun hfun s
  refine ⟨m, fun j s => cf s j, fun j => ψ (ι j), hcf_hol, fun j s => (hψ (ι j)).2.1 s,
    fun j s => (hψ (ι j)).2.2.1 s, fun j s => (hψ (ι j)).2.2.2.1 s, fun j => (hψ (ι j)).2.2.2.2.1,
    fun j g => (hψ (ι j)).2.2.2.2.2.1 g, fun j s s' k h1 h2 => (hψ (ι j)).2.2.2.2.2.2 s s' k h1 h2, ?_⟩
  intro s g
  have hsec := eq_of_isInducedSection_of_forall_inK F (etaFst μ α hα s) (etaSnd ν α hα s) (hφ s)
    (isInducedSection_sum F _ _ (fun j => cf s j) (fun j => ψ (ι j) s) (fun j => (hψ (ι j)).2.1 s))
    (fun k hk => by
      have hk' : ∀ j, ψ (ι j) s k = φ (σ (ι j)) k := fun j =>
        ((hψ (ι j)).2.2.2.2.2.2 s (σ (ι j)) k hk.1 hk.2).trans (congrFun (hψ (ι j)).1 k)
      simp only [hk']
      exact hall s ⟨k, hk⟩)
  exact congrFun hsec g

end FlatFamilyDecomposition

end LocalIntertwining

end AutomorphicForm
