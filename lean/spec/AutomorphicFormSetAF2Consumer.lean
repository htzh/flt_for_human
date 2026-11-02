/-
  Cross-module wire test for the adelic maximal compact subgroup (SET-AF2).

  A `spec/` probe, not a library module. Zone A composes the compactness with the one-place factors:
  `maximalCompactAt S` is compact as a closed subset of the compact group, and the factor's Haar
  measure is a probability. Zone B composes the membership API: the row-isometry projections of an
  element of the group, the factor inclusions, and the entry bound.

  Zones C–G are the five headlines of `Adelic/MaximalCompactFactors.lean`: the two-factor split
  (C), the one-place refinement with its commutation (D), the archimedean mirror (E), the
  neighbourhood basis read at `1` (F), and the archimedean determinant-one compactness (G).
  Zones H–I are the two headlines of `Adelic/InducedSectionMaximalCompact.lean`, in hypothesis form
  because a concrete family with all six properties is not available in the probe: each extracts a
  different conjunct (the flatness over the maximal compact in H, the non-vanishing point in I).

  Every zone is a real composition — no `#check` — so deleting the module it imports makes the probe
  fail.
-/
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionMaximalCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

namespace AutomorphicFormSetAF2Consumer

variable (K : Type) [Field K] [NumberField K]

-- Zone A: the factors are compact, and their Haar measures are probabilities.
--
-- `maximalCompactAt S` and `maximalCompactAway S` are closed subgroups of the compact
-- `adelicMaximalCompact`, so each is compact and carries the Haar probability read off `⊤`.
example (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsCompact (maximalCompactAt K S : Set (AdelicGL2 (𝓞 K) K)) ∧
      IsCompact (maximalCompactAway K S : Set (AdelicGL2 (𝓞 K) K)) ∧
      (maximalCompactAtHaar K S) Set.univ = 1 ∧
      (maximalCompactAwayHaar K S) Set.univ = 1 :=
  ⟨isCompact_maximalCompactAt K S, isCompact_maximalCompactAway K S,
    measure_univ, measure_univ⟩

-- Zone B: the membership API — the archimedean projection is a row isometry, the factors sit inside
-- the group, and the row-isometry entry bound holds for the identity.
example (w : InfinitePlace K) (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsRowIsometry (archComponent K w (glArch (𝓞 K) K k)) ∧
      archComponent K w (glArch (𝓞 K) K k) ∈ rowIsometrySubgroup w.Completion ∧
      (maximalCompactAt K S ≤ adelicMaximalCompact K) ∧
      ‖(((1 : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0‖ ≤ 1 :=
  ⟨isRowIsometry_archComponent hk w, archComponent_mem_rowIsometrySubgroup hk w,
    maximalCompactAt_le K S,
    WindowedSiegel.IsRowIsometry.norm_apply_le_one isRowIsometry_one 0 0⟩

-- Zone C (`M1-1`): the split has both factors inside the group, which is the form every consumer of
-- the row uses; it is the headline composed with the two factor inclusions.
example (S : Finset (HeightOneSpectrum (𝓞 K))) (k : AdelicGL2 (𝓞 K) K)
    (hk : k ∈ adelicMaximalCompact K) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 K) K, k₁ ∈ adelicMaximalCompact K ∧
      k₂ ∈ adelicMaximalCompact K ∧ k = k₁ * k₂ := by
  obtain ⟨k₁, k₂, h₁, h₂, heq⟩ :=
    exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq K S k hk
  exact ⟨k₁, k₂, maximalCompactAt_le K S h₁, maximalCompactAway_le K S h₂, heq⟩

-- Zone D (`M1-2`): the one-place refinement read as "the single-place factor is archimedean-trivial
-- and commutes with the rest".
open scoped Classical in
example (S : Finset (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ maximalCompactAt K S) :
    ∃ k' kv : AdelicGL2 (𝓞 K) K, k' ∈ maximalCompactAt K (S.erase v) ∧
      glArch (𝓞 K) K kv = 1 ∧ k' * kv = kv * k' ∧ k = k' * kv := by
  obtain ⟨k', kv, h', -, harch, heq, hcomm⟩ :=
    exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt K S v hv k hk
  exact ⟨k', kv, h', harch, hcomm, heq⟩

-- Zone E (`M1-3`): the archimedean mirror — the `w`-supported factor has trivial finite part, and
-- its complement has trivial archimedean part at `w`.
example (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ maximalCompactAt K ∅) (w : InfinitePlace K) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k₁ = 1 ∧ k₂ ∈ maximalCompactAt K ∅ ∧
      archComponent K w (glArch (𝓞 K) K k₂) = 1 := by
  obtain ⟨k₁, k₂, -, -, h1, -, -, -, h2, h3⟩ :=
    exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty K k hk w
  exact ⟨k₁, k₂, h1, h2, h3⟩

-- Zone F (`M1-4`): every neighbourhood of `1` contains a whole `maximalCompactAway S₀`, so in
-- particular it contains `1` — the neighbourhood-basis statement read at the identity.
example (W : Set (AdelicGL2 (𝓞 K) K)) (hW : W ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)),
      (1 : AdelicGL2 (𝓞 K) K) ∈ W ∧ (maximalCompactAway K S₀ : Set (AdelicGL2 (𝓞 K) K)) ⊆ W := by
  obtain ⟨S₀, hS₀⟩ := exists_maximalCompactAway_subset_of_mem_nhds_one K W hW
  exact ⟨S₀, hS₀ (maximalCompactAway K S₀).one_mem, hS₀⟩

-- Zone G (`M1-5`): the determinant-one row isometries are compact, and they contain the identity.
example (w : InfinitePlace K) :
    IsCompact (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) ∧
      (1 : GL (Fin 2) w.Completion) ∈ rowIsometrySubgroup₀ w.Completion :=
  ⟨isCompact_rowIsometrySubgroup_detOne K w, (rowIsometrySubgroup₀ w.Completion).one_mem⟩

-- Zone H (`M2-1`): the flatness conjunct of the right-translated family, extracted from the
-- headline. Hypothesis form: a concrete family with all six properties is not available here, so
-- most of the statement's binders are unused by the extracted conjunct — the linter is silenced for
-- that reason only.
set_option linter.unusedVariables false in
example (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (hφK : ∀ s, IsArchKFinite F (φ s)) (hφf : ∀ s, IsKfSmooth F (φ s))
      (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (k₀ : AdelicGL2 (𝓞 F) F) (hk₀ : k₀ ∈ adelicMaximalCompact F),
    ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s (k * k₀) = φ s' (k * k₀) := by
  intro _α hα φ hφ hφK hφf hφjc hφhol hφflat k₀ hk₀
  exact (flat_family_comp_mul_of_mem_adelicMaximalCompact F hα φ hφ hφK hφf hφjc hφhol hφflat
    k₀ hk₀).2.2.2.2.2

-- Zone I (`M2-2`): the non-vanishing at a Weyl/unipotent point gives back a non-vanishing point of
-- `φ` itself, so the two existentials are interchangeable. Hypothesis form, as in zone H.
set_option linter.unusedVariables false in
example (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (hφc : Continuous φ) (hφf : IsKfSmooth F φ) (hne : ∃ g, φ g ≠ 0),
    ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 := by
  intro _α hα s φ hφ hφc hφf hne
  obtain ⟨x, hx⟩ :=
    exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth F hα s φ
      hφ hφc hφf hne
  exact ⟨_, hx⟩

end AutomorphicFormSetAF2Consumer
