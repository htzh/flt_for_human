/-
  Consumer test for SET-AF100.

  One zone, and it is a real cross-module composition rather than a restatement: the unipotent
  surgery of SET-AF100 order B computes the `diagOne` Whittaker coefficient of a finite sum of
  unipotent translates as a character factor times the coefficient of the original function, and
  the per-place Casimir-trichotomy decay of order A bounds that coefficient by the idele norm.  Read
  together they say that the surgery's finite linear combination inherits the torus decay bound — the
  step the Rankin–Selberg unfolding consumes.  Deleting either module breaks this file: the surgery
  row supplies the identity, the decay row supplies the bound (`∃ δ C`).

  The hypothesis block is order A's (the archimedean purity, regularity, growth, Casimir eigenvalue
  and trichotomy data at every real place, and the complex-place bound) plus order B's (the periodicity
  of the test function under global unipotent elements and its Whittaker integrability).  No `sorry`,
  no `#check`.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerTorusDecay
import FLTForHuman.AutomorphicForm.Adelic.RankinSelbergShellIndicator

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped BigOperators

namespace AutomorphicForm

/-- The surgery coefficient inherits the per-place torus decay: order B's identity at `g' = 1`,
multiplied by order A's bound at the same idèle. -/
theorem exists_norm_unipotent_surgery_whittakerCoefficient_diagOne_le
    (K : Type) [Field K] [NumberField K]
    (h1 : ∀ v v' : InfinitePlace K, v.IsComplex → v'.IsComplex → v = v')
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (G : AdelicGL2 (𝓞 K) K → ℂ) (hGc : Continuous G)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), G (globalPoints (𝓞 K) K γ * g) = G g)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      G (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * G g)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ) (lam : ∀ v : InfinitePlace K, v.IsReal → ℝ)
    (hxn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) G)
    (hreg : ∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) G) ∧ Continuous (l.foldr (archDerivAt hv) G))
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G 1
              g‖ ≤
        C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hcas : ∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv G = ((lam v hv : ℝ) : ℂ) • G)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < lam v hv ∨
      (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] G = 0 ∧
        ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] G) 1
              g‖ ≤
            Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
      (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
        Matrix.GeneralLinearGroup.det h = 1 → G (g * archRealGLAt hv h) = G g))
    (hcx : ∀ (v : InfinitePlace K), v.IsComplex → ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ v → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G 1
              (diagOne a)‖ ≤
            C * ‖((a : AdeleRing (𝓞 K) K)).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 v‖) ^ δ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
      G (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * h) = G (unipotentGL2 u * h))
    (hint : ∀ (α : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G α g)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (t : (AdeleRing (𝓞 K) K)ˣ), ((t : AdeleRing (𝓞 K) K)).2 = 1 →
        ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ),
          ‖whittakerCoefficient K (productionPinsOf K D
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i))) 1 (diagOne t)‖ ≤
            c * (∑ i, ‖cs i‖ * ‖NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖) *
              ∏ w : InfinitePlace K,
                (‖((t : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                  (min 1 ‖((t : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by
  obtain ⟨δ, hδ, C, hC⟩ :=
    exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
      K h1 D ξ w₀ hξ G hGc hxG hxZ nw lam hxn hreg hgr hcas harch hcx
  obtain ⟨r, y, cs, -, -, hid, -⟩ :=
    exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul K D G hper hint S m
  refine ⟨δ, hδ, max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t ht => ?_⟩
  refine ⟨r, y, cs, ?_⟩
  have h1t : ((t : AdeleRing (𝓞 K) K)).2 = 1 := ht
  -- the two sides the calculation runs between, named once
  have hidt :
      whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i)))
          1 (diagOne t) =
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
          whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) G 1 (diagOne t) := by
    simpa using hid t 1 (fun i => by simp)
  have hP0 : 0 ≤ ∏ w : InfinitePlace K,
      (‖((t : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
        (min 1 ‖((t : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) :=
    Finset.prod_nonneg fun w _ => by positivity
  have hS0 : 0 ≤ ∑ i, ‖cs i‖ *
      ‖NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖ :=
    Finset.sum_nonneg fun i _ => by positivity
  have hsum : ‖∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖ ≤
      ∑ i, ‖cs i‖ * ‖NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖ := by
    calc ‖∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖
        ≤ ∑ i, ‖cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖ := by
          simpa using norm_sum_le (Finset.univ : Finset (Fin r))
            (fun i => cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i))
      _ = ∑ i, ‖cs i‖ * ‖NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖ :=
          Finset.sum_congr rfl fun i _ => norm_mul _ _
  calc ‖whittakerCoefficient K (productionPinsOf K D
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i)))
              1 (diagOne t)‖
      = ‖∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖ *
          ‖whittakerCoefficient K (productionPinsOf K D
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) G 1 (diagOne t)‖ := by
        rw [hidt, norm_mul]
    _ ≤ (∑ i, ‖cs i‖ * ‖NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖) *
          (C * ∏ w : InfinitePlace K,
            (‖((t : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
              (min 1 ‖((t : AdeleRing (𝓞 K) K)).1 w‖) ^ δ)) :=
        mul_le_mul hsum (hC t h1t) (norm_nonneg _) hS0
    _ ≤ (∑ i, ‖cs i‖ * ‖NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖) *
          (max C 1 * ∏ w : InfinitePlace K,
            (‖((t : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
              (min 1 ‖((t : AdeleRing (𝓞 K) K)).1 w‖) ^ δ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_left C 1) hP0) hS0
    _ = max C 1 * (∑ i, ‖cs i‖ * ‖NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)‖) *
          ∏ w : InfinitePlace K,
            (‖((t : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
              (min 1 ‖((t : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by ring

end AutomorphicForm
