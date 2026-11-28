/-
The entire partial Euler product for the Bruhat–Eisenstein coefficients.

For a unitary pair of idele-class Hecke characters, a global additive character, and a holomorphic
family `φ` of induced sections, there is a **unitary idele-class character** `χ` and an **entire**
function `Nc` such that, for `Re s > 1`,

  `(∏'_{v ∉ S} (1 - χ_v(ϖ_v) |N v|^{-(2s+1)})) * Nc s = ∑'_{ξ ≠ 0} w(ξ) g`,

where the right side is the sum of the Bruhat–Eisenstein Whittaker coefficients over `ξ ≠ 0`. It is
the entire (not merely meromorphic) form of the Euler-product identity, and the row that makes the
completed `L`-function of the Eisenstein series an entire function of `s`.

Assumes: `PiecePartialEulerProduct` (`exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant`),
`PieceWeylIntegrability`, `ArchIntegralBound`'s `Glue` block, `PieceFactorizationDatum`, and
SET-AF112's `BruhatEisensteinWhittakerSummability`.

Transcribed from the pin below (pinned `aa2d8b3`, 595 `S_` lines).

## The rows

* `AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein` — 595 pin `S_` lines.

## Port deltas (order AF113B)

The pin is nine declarations in two sections — `GlueHeads` (five) and `PieceLayer` (four) — under its
`Target` headline. Five of the nine are already public in the port and are imported, not restated:

| pin (`P2M/Sol/S_…bruhatEisenstein.lean`) | port home |
|---|---|
| `:48` `EgenGlue.whittakerCoefficient_bruhatSeries_eq_finset_sum` | `EisensteinGeneral.Glue.…` (`EisensteinGeneral/ArchIntegralBound.lean`) |
| `:317` `EgenPiece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero` | `EisensteinGeneral.Piece.…` (same module) |
| `:141` `EgenPiece.integrable_weyl_unipotent_mul_of_factorization` | `EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization` (`EisensteinGeneral/PieceWeylIntegrability.lean`); it takes the *local* characters `ψv` and the bundled `FactorizationDatum` (preamble item 1), applied here at the pin's local data |
| `:225` `EgenPiece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant` | `EisensteinGeneral.Piece.…` (`EisensteinGeneral/PiecePartialEulerProduct.lean`, the AF110 headline); it takes the bundled `FactorizationDatum` `D` where the pin takes the 31 unpacked datum fields (`binder-spelling` / `D`-bundling only) |
| `:331` `EgenPiece.exists_sum_factorization_weyl_unipotent_mul_of_flat` | `EisensteinGeneral.Piece.…` (`EisensteinGeneral/PieceFactorizationDatum.lean`, promoted in ground prep) |

The four helpers the pin states in `EgenGlue`/`EgenPiece` are restated here `private`, with the pin's
label namespaces dropped (no tokens in names):

* `:64` `differentiable_tsum_and_summable_of_forall_radius` — verbatim. One import is added for it,
  `Mathlib.Analysis.Complex.LocallyUniformLimit`: the pin's `hloc.differentiableOn` is that module's
  `TendstoLocallyUniformlyOn.differentiableOn`, and the scaffold's closure does not reach it.
* `:83` `exists_differentiable_mul_eq_tsum_of_pieces` — verbatim.
* `:101` `exists_uniformizer_valued_eq` — verbatim but for two spellings: `IsDedekindDomain.HeightOneSpectrum.`
  qualifies `valuedAdicCompletion_eq_valuation'` (the port's `open` set does not expose it bare), and the
  `hval` rewrite needs `WithZero.exp_eq_coe_ofAdd` after it (the port's `valuation_exists_uniformizer`
  states `WithZero.exp (-1)`, the goal is `↑(Multiplicative.ofAdd (-1))`); `WithZero.coe_ne_zero` +
  `map_zero` stands in for the pin's `WithZero.exp_ne_zero` (same goal: `Valued.v π ≠ 0`).
* `:112` `isUnitaryChar_and_isIdeleClassChar_mul_inv` — verbatim.

The headline's proof is the pin's, one for one, with the calls above re-pointed: its `EgenGlue.` /
`EgenPiece.` label prefixes are dropped, the deprecated `dif_pos hne` becomes `dite_eq_left hne`, and
`NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` becomes the port's
`AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar` (the port's landing of that pin row). The
statement is the pin wrapper's, unchanged.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein.lean>

spec-pin: Theorems/Thm_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein.lean
spec-pin: P2M/Sol/S_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.EisensteinGeneral.PieceFactorizationDatum
import FLTForHuman.EisensteinGeneral.PiecePartialEulerProduct
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisensteinWhittakerSummability
import FLTForHuman.EisensteinGeneral.PieceWeylIntegrability
import FLTForHuman.EisensteinGeneral.ArchIntegralBound
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionSpan
import FLTForHuman.AutomorphicForm.Adelic.AddCharLocalComponents
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel
open MeasureTheory AutomorphicForm
open scoped Classical NNReal nonZeroDivisors

namespace AutomorphicForm

/-! ### The four helpers (pin `:64`, `:83`, `:101`, `:112`) -/

private theorem differentiable_tsum_and_summable_of_forall_radius {ι : Type} (f : ι → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i))
    (hM : ∀ R : ℝ, ∃ M : ι → ℝ, Summable M ∧ ∀ (i : ι) (s : ℂ), ‖s‖ ≤ R → ‖f i s‖ ≤ M i) :
    Differentiable ℂ (fun s : ℂ => ∑' i : ι, f i s) ∧ ∀ s : ℂ, Summable (fun i : ι => f i s) := by
  refine ⟨?_, fun s => ?_⟩
  · have hloc : TendstoLocallyUniformlyOn (fun t : Finset ι => fun s : ℂ => ∑ i ∈ t, f i s)
        (fun s : ℂ => ∑' i : ι, f i s) Filter.atTop Set.univ := by
      refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun s₀ _ => ?_
      obtain ⟨M, hMs, hMb⟩ := hM (‖s₀‖ + 1)
      refine ⟨Metric.closedBall 0 (‖s₀‖ + 1),
        mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds_of_mem (by simp)),
        tendstoUniformlyOn_tsum hMs fun i s hs => hMb i s ?_⟩
      simpa using hs
    exact differentiableOn_univ.mp (hloc.differentiableOn
      (Filter.Eventually.of_forall fun t => DifferentiableOn.fun_sum fun i _ => (hf i).differentiableOn)
      isOpen_univ)
  · obtain ⟨M, hMs, hMb⟩ := hM ‖s‖
    exact Summable.of_norm_bounded hMs fun i => hMb i s le_rfl

private theorem exists_differentiable_mul_eq_tsum_of_pieces {κ : Type} (n : ℕ) (c : Fin n → ℂ → ℂ)
    (hc : ∀ i, Differentiable ℂ (c i)) (Ep : ℂ → ℂ) (W : κ → ℂ → ℂ) (Q : Fin n → κ → ℂ → ℂ)
    (hQ : ∀ i ξ, Differentiable ℂ (Q i ξ))
    (hM : ∀ (i : Fin n) (R : ℝ), ∃ M : κ → ℝ, Summable M ∧ ∀ (ξ : κ) (s : ℂ), ‖s‖ ≤ R → ‖Q i ξ s‖ ≤ M ξ)
    (hW : ∀ s : ℂ, 1 < s.re → ∀ ξ : κ, W ξ s = ∑ i : Fin n, c i s * (Ep s * Q i ξ s)) :
    ∃ Nc : ℂ → ℂ, Differentiable ℂ Nc ∧ ∀ s : ℂ, 1 < s.re → Ep s * Nc s = ∑' ξ : κ, W ξ s := by
  have hD : ∀ i : Fin n, Differentiable ℂ (fun s : ℂ => ∑' ξ : κ, Q i ξ s) ∧
      ∀ s : ℂ, Summable (fun ξ : κ => Q i ξ s) := fun i =>
    differentiable_tsum_and_summable_of_forall_radius (Q i) (hQ i) (hM i)
  refine ⟨fun s => ∑ i : Fin n, c i s * ∑' ξ : κ, Q i ξ s,
    Differentiable.fun_sum fun i _ => (hc i).fun_mul (hD i).1, fun s hs => ?_⟩
  have hsum : ∀ i : Fin n, Summable (fun ξ : κ => c i s * (Ep s * Q i ξ s)) := fun i =>
    (((hD i).2 s).mul_left (Ep s)).mul_left (c i s)
  rw [tsum_congr (hW s hs), Summable.tsum_finsetSum fun i _ => hsum i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, tsum_mul_left]
  ring

private theorem exists_uniformizer_valued_eq (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : (v.adicCompletion F)ˣ, Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hval : Valued.v (π : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ,
      WithZero.exp_eq_coe_ofAdd]
  have hne : (π : v.adicCompletion F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact WithZero.coe_ne_zero hval.symm
  exact ⟨Units.mk0 _ hne, hval⟩

private theorem isUnitaryChar_and_isIdeleClassChar_mul_inv (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν) :
    IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) ∧ IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) ∧
      (Continuous μ → Continuous ν → Continuous (μ * ν⁻¹)) := by
  refine ⟨fun x => ?_, fun u => ?_, fun hμc hνc => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, hμ x, hν x, inv_one, mul_one]
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμic u, hνic u, inv_one, mul_one]
  · show Continuous (fun x => μ x * (ν x)⁻¹)
    exact hμc.mul hνc.inv

theorem exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    ∃ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      Continuous χ ∧ IsUnitaryChar (𝓞 F) F χ ∧ IsIdeleClassChar (𝓞 F) F χ ∧
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
        ∃ Nc : ℂ → ℂ, Differentiable ℂ Nc ∧
          ∀ s : ℂ, 1 < s.re →
            (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Nc s =
            ∑' ξ : {ξ : F // ξ ≠ 0},
              whittakerCoefficient F (productionPins F) ψ
                (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g := by
  intro α hα _hprin μ ν hμ hν hμic hνic ψ hψ φ hφ hφK hφf hφjc hφhol g
  classical

  choose ϖ hϖ using fun v : HeightOneSpectrum (𝓞 F) => exists_uniformizer_valued_eq F v
  by_cases hzero : ∀ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), φ s g' = 0
  ·
    obtain ⟨hμu, hμic', -⟩ := isUnitaryChar_and_isIdeleClassChar_mul_inv F μ μ hμ hμ hμic hμic
    refine ⟨μ * μ⁻¹, (continuous_const : Continuous fun _ : (AdeleRing (𝓞 F) F)ˣ => (1 : ℂˣ)).congr fun x => ?_,
      hμu, hμic', ∅, ϖ, hϖ, fun _ => 0, differentiable_const 0, fun s _ => ?_⟩
    · simp
    · simp [hzero]
  · push Not at hzero
    obtain ⟨s₀, g₀, hne₀⟩ := hzero

    have hφ₀c : Continuous (φ s₀) :=
      hφjc.comp (continuous_const.prodMk continuous_id)
    have hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ) := by
      refine (NumberField.TateGlobal.continuous_ideleNorm F).congr fun x => ?_
      simp [α, NumberField.TateGlobal.ideleNorm]
    obtain ⟨hμc, hνc⟩ := EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
      F α hα hαc μ ν s₀ (φ s₀) (hφ s₀) hφ₀c g₀ hne₀
    obtain ⟨hχu, hχic, hχc⟩ := isUnitaryChar_and_isIdeleClassChar_mul_inv F μ ν hμ hν hμic hνic

    obtain ⟨ψv, nψ, θr, θc, hψv, hψv', hnψfin, hψfin, hθr, hθc, hψarch'⟩ :=
      exists_localComponents_of_isGlobalAddChar F ψ hψ
    have hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
          = (∏ i : {w : InfinitePlace F // w.IsReal},
                Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
            * ∏ w : {w : InfinitePlace F // w.IsComplex},
                Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)) := by
      intro p
      rw [hψarch' p, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]

    obtain ⟨n, c, pcs, hc, hind, hK, hf, hjc, hhol, hflat, hsum⟩ :=
      exists_flat_isInducedSection_sum_eq_of_differentiable_family F hα μ ν φ hφ hφK hφf hφjc hφhol

    have hdat := fun (i : Fin n) (hne : ∃ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), pcs i s g' ≠ 0) =>
      EisensteinGeneral.Piece.exists_sum_factorization_weyl_unipotent_mul_of_flat F hα μ ν hμ hν hμc hνc
        ψ hψ ψv nψ hnψfin hψv hψv' hψfin θr hθr θc hθc hψarch (μ * ν⁻¹) rfl ϖ hϖ (pcs i) (hind i) (hK i) (hf i)
        (hjc i) (hhol i) (hflat i) hne g

    let S₀ : Fin n → Finset (HeightOneSpectrum (𝓞 F)) := fun i =>
      if hne : ∃ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), pcs i s g' ≠ 0 then (hdat i hne).choose else ∅
    let S : Finset (HeightOneSpectrum (𝓞 F)) := Finset.univ.biUnion S₀

    have hpiece : ∀ i : Fin n, ∃ Q : {ξ : F // ξ ≠ 0} → ℂ → ℂ,
        (∀ ξ : {ξ : F // ξ ≠ 0}, Differentiable ℂ (Q ξ)) ∧
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), 1 < s.re →
          whittakerCoefficient F (productionPins F) ψ
              (fun g' => pcs i s g' + ∑' ξ' : F, pcs i s (adelicWeyl (𝓞 F) F
                  * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g
            = (∏' v : {v // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Q ξ s) ∧
        (∀ R : ℝ, ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧
          ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ‖Q ξ s‖ ≤ M ξ) ∧
        (∀ s : ℂ, 1 < s.re →
          Integrable (fun y => pcs i s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
            (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)) := by
      intro i
      by_cases hne : ∃ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), pcs i s g' ≠ 0
      · have hsub : S₀ i ⊆ S := Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ i)
        have hsub' : (hdat i hne).choose ⊆ S := by
          simpa only [S₀, dite_eq_left hne] using hsub
        obtain ⟨cS, mS, m, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C, hχϖ, hχS, hnψ, hcS, hχc', hmS, hA, hB,
          hoff, hon, habm, hWr, hWc, hC, hind', hfac⟩ := (hdat i hne).choose_spec S hsub'
        obtain ⟨Q, hQ₁, hQ₂, hQ₃⟩ :=
          EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
            F ψ hψ ψv nψ hψv hψv' hψfin θr hθr θc hθc hψarch (μ * ν⁻¹) S ϖ hϖ (pcs i) hind' g
            ⟨cS, mS, m, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C, hχϖ, hχS, hnψ, hcS, hχc', hmS, hA, hB,
              hoff, hon, habm, hWr, hWc, hC, hfac⟩
        refine ⟨Q, hQ₁, hQ₂, hQ₃, ?_⟩
        exact EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization F ψv nψ (μ * ν⁻¹) S ϖ hϖ (pcs i) g
          ⟨cS, mS, m, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C, hχϖ, hχS, hnψ, hcS, hχc', hmS, hA, hB,
            hoff, hon, habm, hWr, hWc, hC, hfac⟩
      · push Not at hne
        refine ⟨fun _ _ => 0, fun _ => differentiable_const 0, fun ξ s _ => ?_,
          fun _ => ⟨fun _ => 0, summable_zero, fun _ _ _ => by simp⟩, fun s _ => ?_⟩
        · simp [hne]
        · simp [hne]
    choose Q hQ using hpiece

    have hW : ∀ s : ℂ, 1 < s.re → ∀ ξ : {ξ : F // ξ ≠ 0},
        whittakerCoefficient F (productionPins F) ψ
            (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g
          = ∑ i : Fin n, c i s
              * ((∏' v : {v // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Q i ξ s) := by
      intro s hs ξ
      rw [EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum F ψ hψ.continuous
        (fun x => AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar F hψ x) n (fun i => c i s)
        (fun i => pcs i s) (φ s) (fun i => ⟨_, _, hind i s⟩) (fun g' => hsum s g') (ξ : F) g
        (fun i => (hQ i).2.2.2 s hs)]
      exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.1 ξ s hs]
    obtain ⟨Nc, hNc, hid⟩ := exists_differentiable_mul_eq_tsum_of_pieces n c hc
      (fun s => ∏' v : {v // v ∉ S},
        (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
      (fun (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) => whittakerCoefficient F (productionPins F) ψ
        (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
            * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g)
      Q (fun i ξ => (hQ i).1 ξ) (fun i R => (hQ i).2.2.1 R) hW
    exact ⟨μ * ν⁻¹, hχc hμc hνc, hχu, hχic, S, ϖ, hϖ, Nc, hNc, hid⟩

end AutomorphicForm
