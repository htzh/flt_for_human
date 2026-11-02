/-
  The dead tail of `FLTForHuman.AutomorphicForm.Adelic.BigCellExpansion`, copied out of it on
  2026-11-02 (the AF7 finishing order) — the declarations its headline
  `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` does not reach, closed under the
  private premises they need.

  Provenance: the pin's `P2M/Sol/S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family.lean`
  (5,407 lines, pinned `aa2d8b3`), transcribed verbatim; the statements here are the pin's, at the
  pin's names and inner namespaces, `private` as in the pin.  **Twelve declarations / 150 lines**
  are unreachable from the public headline (`tools/deps/move_dead.py`, reachability): the real-place
  Fourier/Poisson route the pin abandoned for the archimedean `K`-finiteness engine the headline
  uses instead (`eq_finite_sum_fourier`, `phi_rot_expansion`, `multi_real_expansion`,
  `projArch_list_prod_incl`, `projFin_list_prod_incl`, `eq_list_prod_incl`, `rotAt_zero`,
  `ρR_pos`), and the definitional-unfolding API of four of the node's own objects (`evalAt_apply`,
  `entryF_apply`, `kF_coe`, `cF_apply`).  They are mathematics (statements about the port's own
  objects, nowhere else in the port), so they are shelved rather than deleted — playbook §3.8.

  Three dead declarations of the same run are **not** here because they turned out to be live:
  `Φ_snd`, `Φ_snd_sigmaC` and `Φ_snd_apply` (with the local bridge `mC_apply`) are the complex half
  of `ArchFactor.Φ` and are used by `flatOne_bigCell_eq`.  `move_dead.py`'s reference scanner is
  ASCII-only, so a declaration whose name starts with a Greek letter (`Φ_…`, `ρR_pos`) is reported
  unreferenced even when it is used; the four were restored to the live module by hand.  (`ρR_pos`
  really is unreferenced — its uses, if any, would have been invisible too, so it was checked with a
  plain `grep`.)

  Nothing in `FLTForHuman` imports this module and it declares no `spec-pin:` wire: it is a reading
  shelf in `Reserve`, built so it stays green and diffed by nothing.  Its premises are **copies** —
  the live module keeps its own.  The dead declarations that were *deleted* rather than shelved are
  the pin's `placeBorel` / `infMS` (and the `placeBorelSpace` instance): those are the port's
  `NumberTheory/AdelicHaar/PlaceMeasure.lean` (`M4aS4.*`) verbatim, so FR-0101's import-and-delete
  applies instead of a shelf.
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat
import FLTForHuman.AutomorphicForm.Adelic.ArchKFiniteFamilyTheorems
import FLTForHuman.AutomorphicForm.Adelic.ArchCompactOrbit
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import FLTForHuman.Analysis.MatrixGroup.UnitaryRightFinite
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightCharTransport
import Mathlib.Analysis.Fourier.AddCircle
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable

attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
attribute [-ext] NumberField.InfinitePlace.Completion.ext

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

-- the pin's 85 `letI := glBorel` / `haveI := borelSpace_…` walls are kept as written (they are the
-- pin's own idiom for a scoped `MeasurableSpace`/`BorelSpace` pair), so the `letI` style linter is
-- off for this file and only for this file
set_option linter.style.haveILetI false

namespace AutomorphicForm
set_option autoImplicit false

noncomputable section

section Height

set_option autoImplicit false

noncomputable section

open NumberField.AdelicHeight

namespace BigCellExpansion
namespace Height

section Local

variable {K : Type*} [NormedField K]

private theorem coe_mul (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

variable [IsUltrametricDist K]

end Local

end BigCellExpansion.Height

end

end Height

section Transport

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix
open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open scoped NumberField.InfinitePlace.Completion

open AutomorphicForm AutomorphicForm.WindowedSiegel

open scoped ComplexConjugate

namespace BigCellExpansion
namespace Transport

section Transport

variable {K L : Type} [NormedField K] [NormedField L]

private theorem IsRowIsometry.map_ringEquiv (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : IsRowIsometry (glEquivOfRingEquiv e k) := by
  obtain ⟨hd, hiso⟩ := hk
  refine ⟨?_, fun x y => ?_⟩
  · change ‖(RingEquiv.mapMatrix (m := Fin 2) e (k : Matrix (Fin 2) (Fin 2) K)).det‖ = 1
    rw [← RingEquiv.map_det, he, hd]
  · have hes : ∀ z : L, ‖e.symm z‖ = ‖z‖ := fun z => by rw [← he (e.symm z), e.apply_symm_apply]
    have hent : ∀ i j, ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => rfl
    simp only [hent]
    calc ‖x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 0) + y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 0)‖ ^ 2
          + ‖x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 1) + y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 1)‖ ^ 2
        = ‖e (e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)‖ ^ 2
          + ‖e (e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 1)‖ ^ 2 := by
          simp only [map_add, map_mul, e.apply_symm_apply]
      _ = ‖e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
          + ‖e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 := by
          rw [he, he]
      _ = ‖e.symm x‖ ^ 2 + ‖e.symm y‖ ^ 2 := hiso (e.symm x) (e.symm y)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [hes, hes]

end Transport

end BigCellExpansion.Transport

end

end Transport

noncomputable section

namespace BigCellExpansion
namespace RealPlaces

open MeasureTheory AddCircle Submodule

variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in

private theorem fourier_arg_add (n : ℤ) (u v : AddCircle T) :
    fourier n (u + v) = fourier n u * fourier n v := by
  simp_rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

omit hT in

private theorem fourier_neg_neg (n : ℤ) (v : AddCircle T) :
    fourier (-n) (-v) = fourier n v := by
  have hsm : (-n : ℤ) • (-v) = n • v := by rw [neg_zsmul, zsmul_neg, neg_neg]
  rw [fourier_apply, hsm, ← fourier_apply]

omit hT in

private theorem continuous_of_mem_span {s : Set (AddCircle T → ℂ)}
    (hs : ∀ f ∈ s, Continuous f) {v : AddCircle T → ℂ}
    (hv : v ∈ span ℂ s) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => exact continuous_const
  | add f g _ _ ihf ihg => exact ihf.add ihg
  | smul c f _ ih => exact ih.const_smul c

private theorem integrable_of_continuous {v : AddCircle T → ℂ} (hv : Continuous v) :
    Integrable v (@haarAddCircle T hT) :=
  hv.integrable_of_hasCompactSupport (isClosed_tsupport v).isCompact

section Core

variable (h : C(AddCircle T, ℂ))

private theorem fourierCoeff_translate (c : AddCircle T) (n : ℤ) :
    fourierCoeff (fun θ => h (θ + c)) n = fourier n c * fourierCoeff (⇑h) n := by
  have h1 : (fun u : AddCircle T => fourier (-n) u • h (u + c))
      = fun u : AddCircle T =>
        (fun z : AddCircle T => fourier (-n) (z + -c) • h z) (c + u) := by
    funext u
    show fourier (-n) u • h (u + c) = fourier (-n) (c + u + -c) • h (c + u)
    rw [add_comm c u, add_neg_cancel_right]
  have h2 : ∀ z : AddCircle T, fourier (-n) (z + -c) • h z
      = fourier n c • (fourier (-n) z • h z) := by
    intro z
    rw [fourier_arg_add, fourier_neg_neg, mul_comm, ← smul_smul]
  calc fourierCoeff (fun θ => h (θ + c)) n
      = ∫ u, fourier (-n) u • h (u + c) ∂haarAddCircle := rfl
    _ = ∫ u, (fun z : AddCircle T => fourier (-n) (z + -c) • h z) (c + u) ∂haarAddCircle := by
        rw [h1]
    _ = ∫ z, fourier (-n) (z + -c) • h z ∂haarAddCircle :=
        integral_add_left_eq_self (μ := haarAddCircle)
          (fun z : AddCircle T => fourier (-n) (z + -c) • h z) c
    _ = ∫ z, fourier n c • (fourier (-n) z • h z) ∂haarAddCircle := by
        simp_rw [h2]
    _ = fourier n c • ∫ z, fourier (-n) z • h z ∂haarAddCircle := integral_smul _ _
    _ = fourier n c • fourierCoeff (⇑h) n := rfl
    _ = fourier n c * fourierCoeff (⇑h) n := by rw [smul_eq_mul]

private theorem support_fourierCoeff_finite (s : Finset (AddCircle T → ℂ))
    (hsp : ∀ c : AddCircle T, (fun θ => h (θ + c)) ∈ span ℂ (s : Set (AddCircle T → ℂ))) :
    (Function.support fun n : ℤ => fourierCoeff (⇑h) n).Finite := by
  classical
  by_contra hinfin
  have hinf : (Function.support fun n : ℤ => fourierCoeff (⇑h) n).Infinite := hinfin

  have hWle : span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))
      ≤ span ℂ (s : Set (AddCircle T → ℂ)) := by
    rw [span_le]
    rintro _ ⟨c, rfl⟩
    exact hsp c
  haveI hfd : FiniteDimensional ℂ
      (span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))) :=
    Submodule.finiteDimensional_of_le hWle
  have hWcont : ∀ v ∈ span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c)),
      Continuous v := by
    intro v hv
    refine continuous_of_mem_span ?_ hv
    rintro f ⟨c, rfl⟩
    exact (map_continuous h).comp (continuous_add_const c)
  obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq
    (Module.finrank ℂ
      (span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))) + 1)

  let Φ : (span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))) →ₗ[ℂ]
      (↥t → ℂ) :=
    { toFun := fun v j => fourierCoeff (v : AddCircle T → ℂ) (j : ℤ)
      map_add' := by
        intro v w
        funext j
        show fourierCoeff ((v : AddCircle T → ℂ) + (w : AddCircle T → ℂ)) (j : ℤ) = _
        rw [fourierCoeff.add (integrable_of_continuous (hWcont v v.2))
          (integrable_of_continuous (hWcont w w.2))]
        rfl
      map_smul' := by
        intro cc v
        funext j
        show fourierCoeff (cc • (v : AddCircle T → ℂ)) (j : ℤ) = _
        rw [fourierCoeff.const_smul (v : AddCircle T → ℂ) cc (j : ℤ)]
        rfl }
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨g, hg0, hker⟩ :=
      (LinearMap.range Φ).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)

    have hzero : ∀ c : AddCircle T,
        (∑ j : ↥t, (fourier (j : ℤ) c * fourierCoeff (⇑h) (j : ℤ))
          • g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) = 0 := by
      intro c
      have hmem : (fun θ => h (θ + c))
          ∈ span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c)) :=
        subset_span ⟨c, rfl⟩
      have hval : Φ ⟨_, hmem⟩
          = fun j : ↥t => fourier (j : ℤ) c * fourierCoeff (⇑h) (j : ℤ) := by
        funext j
        exact fourierCoeff_translate h c (j : ℤ)
      have hgv : g (Φ ⟨_, hmem⟩) = 0 := LinearMap.mem_ker.mp (hker ⟨_, rfl⟩)
      rw [hval, LinearMap.pi_apply_eq_sum_univ] at hgv
      exact hgv

    have hfun0 : (fun c : AddCircle T =>
        ∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) c)
        = fun _ : AddCircle T => (0 : ℂ) := by
      funext c
      show (∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
          * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) c) = 0
      have hre : (∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
          * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) c)
          = ∑ j : ↥t, (fourier (j : ℤ) c * fourierCoeff (⇑h) (j : ℤ))
              • g fun j' : ↥t => if j = j' then (1 : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_mul]
        ring
      rw [hre]
      exact hzero c

    have hcoeffZero : ∀ i : ↥t,
        fourierCoeff (⇑h) (i : ℤ)
          * g (fun j' : ↥t => if i = j' then (1 : ℂ) else 0) = 0 := by
      intro i
      have hint : ∀ j : ↥t, Integrable (fun cc : AddCircle T =>
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc)
          (@haarAddCircle T hT) := fun j =>
        integrable_of_continuous (continuous_const.mul (map_continuous (fourier (j : ℤ))))
      have hfn : (fun cc : AddCircle T => ∑ j : ↥t,
            (fourierCoeff (⇑h) (j : ℤ)
              * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc)
          = ∑ j : ↥t, fun cc : AddCircle T =>
              (fourierCoeff (⇑h) (j : ℤ)
                * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc := by
        funext cc
        rw [Finset.sum_apply]
      have hzfn : (fun _ : AddCircle T => (0 : ℂ))
          = ∑ j : ↥t, fun cc : AddCircle T =>
              (fourierCoeff (⇑h) (j : ℤ)
                * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc :=
        hfun0.symm.trans hfn
      have hsum := fourierCoeff.sum (Finset.univ : Finset ↥t)
        (fun j : ↥t => fun cc : AddCircle T =>
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc)
        (fun j _ => hint j)
      have hz : fourierCoeff (fun _ : AddCircle T => (0 : ℂ)) (i : ℤ) = 0 := by
        simp [fourierCoeff]
      have hstep : (0 : ℂ) = ∑ j : ↥t,
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
            * fourierCoeff (T := T) (⇑(fourier (T := T) (j : ℤ))) (i : ℤ) := by
        calc (0 : ℂ)
            = fourierCoeff (fun _ : AddCircle T => (0 : ℂ)) (i : ℤ) := hz.symm
          _ = fourierCoeff (∑ j : ↥t, fun cc : AddCircle T =>
                (fourierCoeff (⇑h) (j : ℤ)
                  * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                  * fourier (j : ℤ) cc) (i : ℤ) := by rw [← hzfn]
          _ = (∑ j : ↥t, fourierCoeff fun cc : AddCircle T =>
                (fourierCoeff (⇑h) (j : ℤ)
                  * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                  * fourier (j : ℤ) cc) (i : ℤ) := by rw [hsum]
          _ = ∑ j : ↥t, fourierCoeff (fun cc : AddCircle T =>
                (fourierCoeff (⇑h) (j : ℤ)
                  * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                  * fourier (j : ℤ) cc) (i : ℤ) := by rw [Finset.sum_apply]
          _ = ∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
                * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                * fourierCoeff (T := T) (⇑(fourier (T := T) (j : ℤ))) (i : ℤ) :=
              Finset.sum_congr rfl fun j _ => fourierCoeff.const_mul _ _ _
      have hcollapse : (∑ j : ↥t,
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
            * fourierCoeff (T := T) (⇑(fourier (T := T) (j : ℤ))) (i : ℤ))
          = fourierCoeff (⇑h) (i : ℤ)
            * g fun j' : ↥t => if i = j' then (1 : ℂ) else 0 := by
        rw [Finset.sum_eq_single i]
        · rw [congrFun (fourierCoeff_fourier (T := T) (i : ℤ)) (i : ℤ),
            Pi.single_eq_same, mul_one]
        · intro b _ hbi
          have hbne : (i : ℤ) ≠ (b : ℤ) := fun hc => hbi (Subtype.coe_injective hc.symm)
          rw [congrFun (fourierCoeff_fourier (T := T) (b : ℤ)) (i : ℤ),
            Pi.single_eq_of_ne hbne, mul_zero]
        · intro hni
          exact absurd (Finset.mem_univ i) hni
      exact (hstep.trans hcollapse).symm

    have hgeq : g = 0 := by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ g x, LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have haj : g (fun j' : ↥t => if j = j' then (1 : ℂ) else 0) = 0 := by
        have hj := hcoeffZero j
        have hne : fourierCoeff (⇑h) (j : ℤ) ≠ 0 := Function.mem_support.mp (hts j.2)
        exact (mul_eq_zero.mp hj).resolve_left hne
      rw [haj, smul_zero]
    exact hg0 hgeq
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [Module.finrank_pi, Fintype.card_coe, htcard] at hle
  omega

private theorem eq_finite_sum_fourier (s : Finset (AddCircle T → ℂ))
    (hsp : ∀ c : AddCircle T, (fun θ => h (θ + c)) ∈ span ℂ (s : Set (AddCircle T → ℂ))) :
    ∃ tfin : Finset ℤ, ∀ θ : AddCircle T,
      h θ = ∑ n ∈ tfin, fourierCoeff (⇑h) n * fourier n θ := by
  classical
  have hfin := support_fourierCoeff_finite h s hsp
  refine ⟨hfin.toFinset, fun θ => ?_⟩
  have hvanish : ∀ n : ℤ, n ∉ hfin.toFinset → fourierCoeff (⇑h) n = 0 := by
    intro n hn
    by_contra hne
    exact hn (hfin.mem_toFinset.mpr (Function.mem_support.mpr hne))
  have hsummable : Summable (fourierCoeff (⇑h)) :=
    summable_of_ne_finset_zero hvanish
  have h1 := has_pointwise_sum_fourier_series_of_summable (f := h) hsummable θ
  have h2 : HasSum (fun n : ℤ => fourierCoeff (⇑h) n • fourier n θ)
      (∑ n ∈ hfin.toFinset, fourierCoeff (⇑h) n • fourier n θ) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [hvanish n hn, zero_smul]
  have heq := h1.unique h2
  simpa [smul_eq_mul] using heq

end Core

open Matrix AutomorphicForm AutomorphicForm.WindowedSiegel

private theorem rotGL_det_val (θ : ℝ) :
    (!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]).det = 1 := by
  rw [Matrix.det_fin_two_of]
  linear_combination Real.sin_sq_add_cos_sq θ

private def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]
    (by rw [rotGL_det_val]; exact one_ne_zero)

private theorem rotGL_coe (θ : ℝ) : (rotGL θ : Matrix (Fin 2) (Fin 2) ℝ)
    = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  rw [rotGL, GeneralLinearGroup.val_mkOfDetNeZero]

private theorem rotGL_add (θ₁ θ₂ : ℝ) : rotGL (θ₁ + θ₂) = rotGL θ₁ * rotGL θ₂ := by
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [rotGL_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one, Real.cos_add, Real.sin_add] <;>
    ring

private theorem rotGL_zero : rotGL 0 = 1 := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rotGL_coe, Real.cos_zero, Real.sin_zero, Units.val_one]

private theorem rotGL_periodic : Function.Periodic rotGL (2 * Real.pi) := by
  intro θ
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rotGL_coe, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem rotGL_neg (θ : ℝ) : rotGL (-θ) = (rotGL θ)⁻¹ := by
  have h : rotGL θ * rotGL (-θ) = 1 := by
    rw [← rotGL_add, add_neg_cancel, rotGL_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

private theorem isRowIsometry_rotGL (θ : ℝ) : IsRowIsometry (rotGL θ) := by
  constructor
  · rw [rotGL_coe, rotGL_det_val, norm_one]
  · intro x y
    simp only [rotGL_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.sin_sq_add_cos_sq θ

private theorem continuous_rotGL_val :
    Continuous fun θ : ℝ => (rotGL θ : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp only [rotGL_coe]
  refine continuous_matrix ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
  · exact Real.continuous_cos
  · exact Real.continuous_sin.neg
  · exact Real.continuous_sin
  · exact Real.continuous_cos

private theorem continuous_rotGL : Continuous rotGL := by
  rw [Units.continuous_iff]
  refine ⟨continuous_rotGL_val, ?_⟩
  have hinv : (fun θ : ℝ => (((rotGL θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
      = fun θ : ℝ => ((rotGL (-θ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext θ
    rw [rotGL_neg]
  rw [hinv]
  exact continuous_rotGL_val.comp continuous_neg

section Transport

open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open scoped NumberField.InfinitePlace.Completion
open BigCellExpansion.Transport
open scoped BigCellExpansion.Transport

private theorem continuous_glEquivOfRingEquiv {K L : Type} [NormedField K] [NormedField L]
    (e : K ≃+* L) (he : Continuous e) :
    Continuous (glEquivOfRingEquiv e) := by
  have hval : Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) :=
    Units.continuous_val
  have hcoeinv : Continuous fun k : GL (Fin 2) K =>
      ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Units.continuous_coe_inv
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) i :=
      (continuous_apply i).comp hval
    have h2 : Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) i j :=
      (continuous_apply j).comp h1
    exact he.comp h2
  · have h : (fun k : GL (Fin 2) K =>
        (((glEquivOfRingEquiv e k)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))
        = fun k : GL (Fin 2) K =>
          ((glEquivOfRingEquiv e (k⁻¹) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
      funext k
      rw [← map_inv]
    rw [h]
    refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun k : GL (Fin 2) K =>
        ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i :=
      (continuous_apply i).comp hcoeinv
    have h2 : Continuous fun k : GL (Fin 2) K =>
        ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j :=
      (continuous_apply j).comp h1
    exact he.comp h2

variable {F : Type} [Field F]

private def rotAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) : GL (Fin 2) w.Completion :=
  glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (rotGL θ)

private theorem rotAt_add {w : InfinitePlace F} (hw : w.IsReal) (θ₁ θ₂ : ℝ) :
    rotAt hw (θ₁ + θ₂) = rotAt hw θ₁ * rotAt hw θ₂ := by
  rw [rotAt, rotAt, rotAt, rotGL_add, map_mul]

private theorem rotAt_zero {w : InfinitePlace F} (hw : w.IsReal) : rotAt hw 0 = 1 := by
  rw [rotAt, rotGL_zero, map_one]

private theorem rotAt_periodic {w : InfinitePlace F} (hw : w.IsReal) :
    Function.Periodic (rotAt hw) (2 * Real.pi) := by
  intro θ
  rw [rotAt, rotAt, rotGL_periodic θ]

private theorem norm_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x),
    RingEquiv.apply_symm_apply]

private theorem isRowIsometry_rotAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    IsRowIsometry (rotAt hw θ) :=
  IsRowIsometry.map_ringEquiv _ (norm_ringEquivRealOfIsReal_symm hw) (isRowIsometry_rotGL θ)

private theorem continuous_rotAt {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (rotAt hw) := by
  have hcont : Continuous ((ringEquivRealOfIsReal hw).symm : ℝ → w.Completion) :=
    (AddMonoidHomClass.isometry_of_norm _ (norm_ringEquivRealOfIsReal_symm hw)).continuous
  exact (continuous_glEquivOfRingEquiv _ hcont).comp continuous_rotGL

end Transport

section InclContinuity

open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open IsDedekindDomain
open scoped IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

private def inclMatrixMap (w : InfinitePlace F) (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (archMatrixUpdate F w m i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private theorem adelicArchGLInclAt_val_eq (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = inclMatrixMap F w (k : Matrix (Fin 2) (Fin 2) w.Completion) := rfl

private theorem continuous_inclMatrixMap (w : InfinitePlace F) :
    Continuous (inclMatrixMap F w) := by
  refine continuous_matrix fun i j => ?_
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    have h : (fun m : Matrix (Fin 2) (Fin 2) v.Completion => archMatrixUpdate F v m i j v)
        = fun m => m i j :=
      funext fun m => archMatrixUpdate_apply_self F v m i j
    rw [h]
    exact (continuous_apply j).comp (continuous_apply i)
  · have h : (fun m : Matrix (Fin 2) (Fin 2) w.Completion => archMatrixUpdate F w m i j v)
        = fun _ => (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j :=
      funext fun m => archMatrixUpdate_apply_of_ne F w m i j hv
    rw [h]
    exact continuous_const

private theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) :
    Continuous (adelicArchGLInclAt F w) := by
  have hval : Continuous fun k : GL (Fin 2) w.Completion =>
      (k : Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val
  have hcoeinv : Continuous fun k : GL (Fin 2) w.Completion =>
      ((k⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_coe_inv
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ ⇑(adelicArchGLInclAt F w) :
        GL (Fin 2) w.Completion → Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = fun k : GL (Fin 2) w.Completion =>
          inclMatrixMap F w (k : Matrix (Fin 2) (Fin 2) w.Completion) :=
      funext fun k => adelicArchGLInclAt_val_eq F w k
    rw [h]
    exact (continuous_inclMatrixMap F w).comp hval
  · have h : (fun k : GL (Fin 2) w.Completion =>
        (((adelicArchGLInclAt F w k)⁻¹ : AdelicGL2 (𝓞 F) F) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
        = fun k : GL (Fin 2) w.Completion =>
          inclMatrixMap F w ((k⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
      funext k
      rw [← map_inv]
      exact adelicArchGLInclAt_val_eq F w k⁻¹
    rw [h]
    exact (continuous_inclMatrixMap F w).comp hcoeinv

private theorem rotAt_incl_mem_archRowIsometrySubgroup {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    adelicArchGLInclAt F w (rotAt hw θ) ∈ AutomorphicForm.archRowIsometrySubgroup F w :=
  Subgroup.mem_map_of_mem _
    ((AutomorphicForm.WindowedSiegel.mem_rowIsometrySubgroup_iff).mpr (isRowIsometry_rotAt hw θ))

end InclContinuity

section CircleFn

open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open IsDedekindDomain
open scoped IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

private theorem periodic_phi_rot (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) :
    Function.Periodic (fun θ : ℝ => φ (y * adelicArchGLInclAt F w (rotAt hw θ)))
      (2 * Real.pi) := by
  intro θ
  show φ (y * adelicArchGLInclAt F w (rotAt hw (θ + 2 * Real.pi)))
      = φ (y * adelicArchGLInclAt F w (rotAt hw θ))
  rw [rotAt_periodic hw θ]

private def circleFn (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) :
    AddCircle (2 * Real.pi) → ℂ :=
  (periodic_phi_rot hw φ y).lift

private theorem circleFn_coe (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) (θ : ℝ) :
    circleFn hw φ y ↑θ = φ (y * adelicArchGLInclAt F w (rotAt hw θ)) :=
  (periodic_phi_rot hw φ y).lift_coe θ

private theorem continuous_circleFn (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (y : AdelicGL2 (𝓞 F) F) :
    Continuous (circleFn hw φ y) := by
  have hqm : Topology.IsQuotientMap ((↑) : ℝ → AddCircle (2 * Real.pi)) :=
    QuotientAddGroup.isQuotientMap_mk _
  rw [hqm.continuous_iff]
  have h : (circleFn hw φ y ∘ ((↑) : ℝ → AddCircle (2 * Real.pi)))
      = fun θ : ℝ => φ (y * adelicArchGLInclAt F w (rotAt hw θ)) :=
    funext fun θ => circleFn_coe hw φ y θ
  rw [h]
  exact hφc.comp (continuous_const.mul
    ((continuous_adelicArchGLInclAt F w).comp (continuous_rotAt hw)))

private def circleRestrict (hw : w.IsReal) (y : AdelicGL2 (𝓞 F) F) :
    (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AddCircle (2 * Real.pi) → ℂ) where
  toFun ψ := circleFn hw ψ y
  map_add' ψ₁ ψ₂ := by
    funext θq
    induction θq using QuotientAddGroup.induction_on with
    | H θ =>
      show circleFn hw (ψ₁ + ψ₂) y ↑θ = circleFn hw ψ₁ y ↑θ + circleFn hw ψ₂ y ↑θ
      rw [circleFn_coe, circleFn_coe, circleFn_coe]
      rfl
  map_smul' cc ψ := by
    funext θq
    induction θq using QuotientAddGroup.induction_on with
    | H θ =>
      show circleFn hw (cc • ψ) y ↑θ = cc • circleFn hw ψ y ↑θ
      rw [circleFn_coe, circleFn_coe]
      rfl

-- the source's `private scoped instance fact_two_pi_pos` (an instance, so not in the copied set):
-- without it `AddCircle (2 * Real.pi)` has no `Fact (0 < ·)` and `fourier` does not elaborate
private instance fact_two_pi_pos : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem circleFn_translate_eq (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) (c : ℝ) :
    (fun θq : AddCircle (2 * Real.pi) => circleFn hw φ y (θq + ↑c))
      = circleFn hw (fun x => φ (x * adelicArchGLInclAt F w (rotAt hw c))) y := by
  funext θq
  induction θq using QuotientAddGroup.induction_on with
  | H θ =>
    have h1 : ((θ : AddCircle (2 * Real.pi)) + ↑c)
        = ((θ + c : ℝ) : AddCircle (2 * Real.pi)) := rfl
    show circleFn hw φ y ((θ : AddCircle (2 * Real.pi)) + ↑c) = _
    rw [h1, circleFn_coe, circleFn_coe, rotAt_add, map_mul, ← mul_assoc]

private theorem circleFn_translates_mem_span (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hK : AutomorphicForm.IsArchKFiniteAt F w φ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ s' : Finset (AddCircle (2 * Real.pi) → ℂ),
      ∀ cq : AddCircle (2 * Real.pi),
        (fun θq => circleFn hw φ y (θq + cq))
          ∈ Submodule.span ℂ (s' : Set (AddCircle (2 * Real.pi) → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hK
  refine ⟨s.image fun ψ => circleFn hw ψ y, ?_⟩
  intro cq
  induction cq using QuotientAddGroup.induction_on with
  | H c =>
    rw [circleFn_translate_eq hw φ y c]
    have hmem := hs (adelicArchGLInclAt F w (rotAt hw c))
      (rotAt_incl_mem_archRowIsometrySubgroup F hw c)
    have hmap := Submodule.mem_map_of_mem (f := circleRestrict hw y) hmem
    rw [Submodule.map_span] at hmap
    have himg : (circleRestrict hw y) '' (s : Set (AdelicGL2 (𝓞 F) F → ℂ))
        = ((s.image fun ψ => circleFn hw ψ y : Finset (AddCircle (2 * Real.pi) → ℂ)) :
            Set (AddCircle (2 * Real.pi) → ℂ)) := by
      rw [Finset.coe_image]
      rfl
    rw [himg] at hmap
    exact hmap

private theorem phi_rot_expansion (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hK : AutomorphicForm.IsArchKFiniteAt F w φ)
    (y : AdelicGL2 (𝓞 F) F) :
    ∃ tfin : Finset ℤ, ∀ θ : ℝ,
      φ (y * adelicArchGLInclAt F w (rotAt hw θ))
        = ∑ n ∈ tfin,
            fourierCoeff (circleFn hw φ y) n * fourier n (θ : AddCircle (2 * Real.pi)) := by
  obtain ⟨s', hs'⟩ := circleFn_translates_mem_span hw hK y
  obtain ⟨tfin, ht⟩ := eq_finite_sum_fourier
    (⟨circleFn hw φ y, continuous_circleFn hw hφc y⟩ : C(AddCircle (2 * Real.pi), ℂ)) s' hs'
  refine ⟨tfin, fun θ => ?_⟩
  have hθ := ht ↑θ
  rw [← circleFn_coe hw φ y θ]
  exact hθ

end CircleFn

section Projections

open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open IsDedekindDomain
open scoped IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

private def projArch (v : InfinitePlace F) : AdeleRing (𝓞 F) F →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def projFin : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem projArch_apply (v : InfinitePlace F) (a : AdeleRing (𝓞 F) F) :
    projArch F v a = a.1 v := rfl

private theorem projFin_apply (a : AdeleRing (𝓞 F) F) : projFin F a = a.2 := rfl

private theorem matrix_ext_of_proj {A B : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : ∀ v : InfinitePlace F, (projArch F v).mapMatrix A = (projArch F v).mapMatrix B)
    (hfin : (projFin F).mapMatrix A = (projFin F).mapMatrix B) : A = B := by
  ext i j
  refine Prod.ext ?_ ?_
  · funext v
    have h : (projArch F v).mapMatrix A i j = (projArch F v).mapMatrix B i j :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) v.Completion => M i j) (harch v)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply] at h
    exact h
  · have h : (projFin F).mapMatrix A i j = (projFin F).mapMatrix B i j :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) => M i j) hfin
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projFin_apply] at h
    exact h

private theorem projArch_mapMatrix_inclMatrixMap_self (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    (projArch F w).mapMatrix (inclMatrixMap F w m) = m := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply, inclMatrixMap]
  exact archMatrixUpdate_apply_self F w m i j

private theorem projArch_mapMatrix_inclMatrixMap_of_ne {w v : InfinitePlace F} (hv : v ≠ w)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    (projArch F v).mapMatrix (inclMatrixMap F w m) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply, inclMatrixMap]
  exact archMatrixUpdate_apply_of_ne F w m i j hv

private theorem projFin_mapMatrix_inclMatrixMap_apply (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2)
    (v : HeightOneSpectrum (𝓞 F)) :
    (inclMatrixMap F w m i j).2 v
      = ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) v := rfl

private theorem projFin_mapMatrix_inclMatrixMap (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    (projFin F).mapMatrix (inclMatrixMap F w m) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projFin_apply,
    projFin_mapMatrix_inclMatrixMap_apply]

private theorem projArch_incl_self (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    (projArch F w).mapMatrix
        ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (k : Matrix (Fin 2) (Fin 2) w.Completion) := by
  rw [adelicArchGLInclAt_val_eq, projArch_mapMatrix_inclMatrixMap_self]

private theorem projArch_incl_of_ne {w v : InfinitePlace F} (hv : v ≠ w) (k : GL (Fin 2) w.Completion) :
    (projArch F v).mapMatrix
        ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = 1 := by
  rw [adelicArchGLInclAt_val_eq, projArch_mapMatrix_inclMatrixMap_of_ne F hv]

private theorem projFin_incl (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    (projFin F).mapMatrix
        ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = 1 := by
  rw [adelicArchGLInclAt_val_eq, projFin_mapMatrix_inclMatrixMap]

private theorem incl_comm {w w' : InfinitePlace F} (hne : w ≠ w')
    (k : GL (Fin 2) w.Completion) (k' : GL (Fin 2) w'.Completion) :
    adelicArchGLInclAt F w k * adelicArchGLInclAt F w' k'
      = adelicArchGLInclAt F w' k' * adelicArchGLInclAt F w k := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply matrix_ext_of_proj
  · intro v
    rw [map_mul, map_mul]
    by_cases hvw : v = w
    · subst hvw
      rw [projArch_incl_self, projArch_incl_of_ne F hne, mul_one, one_mul]
    · by_cases hvw' : v = w'
      · subst hvw'
        rw [projArch_incl_self, projArch_incl_of_ne F hvw, mul_one, one_mul]
      · rw [projArch_incl_of_ne F hvw, projArch_incl_of_ne F hvw']
  · rw [map_mul, map_mul, projFin_incl, projFin_incl]

open scoped Classical in

private theorem projArch_list_prod_incl (k : ∀ u : InfinitePlace F, GL (Fin 2) u.Completion)
    (v : InfinitePlace F) :
    ∀ L : List (InfinitePlace F), L.Nodup →
      (projArch F v).mapMatrix
          (((L.map fun u => adelicArchGLInclAt F u (k u)).prod : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = if v ∈ L then (k v : Matrix (Fin 2) (Fin 2) v.Completion) else 1 := by
  intro L
  induction L with
  | nil =>
    intro _
    have h0 : v ∉ ([] : List (InfinitePlace F)) := by simp
    rw [List.map_nil, List.prod_nil, Units.val_one, map_one, ite_eq_right h0]
  | cons u L ih =>
    intro hL
    obtain ⟨huL, hLnd⟩ := List.nodup_cons.mp hL
    rw [List.map_cons, List.prod_cons, Units.val_mul, map_mul, ih hLnd]
    by_cases hvu : v = u
    · subst hvu
      have hmem : v ∈ v :: L := by simp
      rw [projArch_incl_self, ite_eq_right huL, mul_one, ite_eq_left hmem]
    · rw [projArch_incl_of_ne F hvu, one_mul]
      by_cases hvL : v ∈ L
      · have hmem : v ∈ u :: L := by simp [hvL]
        rw [ite_eq_left hvL, ite_eq_left hmem]
      · have hnmem : v ∉ u :: L := by simp [hvu, hvL]
        rw [ite_eq_right hvL, ite_eq_right hnmem]

private theorem projFin_list_prod_incl (k : ∀ u : InfinitePlace F, GL (Fin 2) u.Completion) :
    ∀ L : List (InfinitePlace F),
      (projFin F).mapMatrix
          (((L.map fun u => adelicArchGLInclAt F u (k u)).prod : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = 1 := by
  intro L
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, Units.val_one, map_one]
  | cons u L ih => rw [List.map_cons, List.prod_cons, Units.val_mul, map_mul, ih, projFin_incl, one_mul]

private theorem eq_list_prod_incl (g : AdelicGL2 (𝓞 F) F)
    (k : ∀ u : InfinitePlace F, GL (Fin 2) u.Completion)
    (L : List (InfinitePlace F)) (hL : L.Nodup) (hall : ∀ u : InfinitePlace F, u ∈ L)
    (harch : ∀ v : InfinitePlace F,
      (projArch F v).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = (k v : Matrix (Fin 2) (Fin 2) v.Completion))
    (hfin : (projFin F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = 1) :
    g = (L.map fun u => adelicArchGLInclAt F u (k u)).prod := by
  apply Units.ext
  apply matrix_ext_of_proj
  · intro v
    rw [harch v, projArch_list_prod_incl F k v L hL, ite_eq_left (hall v)]
  · rw [hfin, projFin_list_prod_incl]

end Projections

section EvalCoords

variable {G : Type}

private def evalAt (V : Submodule ℂ (G → ℂ)) (t : Finset G) : V →ₗ[ℂ] (↥t → ℂ) where
  toFun v := fun z => (v : G → ℂ) (z : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalAt_apply (V : Submodule ℂ (G → ℂ)) (t : Finset G) (v : V) (z : ↥t) :
    evalAt V t v z = (v : G → ℂ) (z : G) := rfl

private theorem mem_ker_evalAt {V : Submodule ℂ (G → ℂ)} {t : Finset G} {v : V} :
    v ∈ LinearMap.ker (evalAt V t) ↔ ∀ z ∈ t, (v : G → ℂ) z = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h z hz
    exact congrFun h ⟨z, hz⟩
  · intro h
    funext z
    exact h z z.2

private theorem exists_finset_ker_evalAt_eq_bot (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] :
    ∃ t : Finset G, LinearMap.ker (evalAt V t) = ⊥ := by
  classical
  have hex : ∃ n : ℕ, ∃ t : Finset G, Module.finrank ℂ (LinearMap.ker (evalAt V t)) = n :=
    ⟨_, ∅, rfl⟩
  obtain ⟨t₀, ht₀⟩ := Nat.find_spec hex
  refine ⟨t₀, ?_⟩
  by_contra hne
  obtain ⟨v, hvK, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hvz : ∃ z : G, (v : G → ℂ) z ≠ 0 := by
    by_contra hall
    exact hv0 (Subtype.ext (funext fun z => not_not.mp fun hz => hall ⟨z, hz⟩))
  obtain ⟨z, hz⟩ := hvz
  have hlt : LinearMap.ker (evalAt V (insert z t₀)) < LinearMap.ker (evalAt V t₀) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro u hu
      rw [mem_ker_evalAt] at hu ⊢
      exact fun z' hz' => hu z' (Finset.mem_insert_of_mem hz')
    · intro heq
      have hvmem : v ∈ LinearMap.ker (evalAt V (insert z t₀)) := heq ▸ hvK
      rw [mem_ker_evalAt] at hvmem
      exact hz (hvmem z (Finset.mem_insert_self z t₀))
  have hrank := Submodule.finrank_lt_finrank_of_lt hlt
  rw [ht₀] at hrank
  exact absurd hrank (not_lt.mpr (Nat.find_min' hex ⟨insert z t₀, rfl⟩))

private theorem exists_eval_coords (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] :
    ∃ (t : Finset G) (e : ↥t → (G → ℂ)), (∀ z : ↥t, e z ∈ V) ∧
      ∀ v ∈ V, v = ∑ z : ↥t, v (z : G) • e z := by
  classical
  obtain ⟨t, ht⟩ := exists_finset_ker_evalAt_eq_bot V
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (evalAt V t) ht
  refine ⟨t, fun z => (L fun z' : ↥t => if z = z' then (1 : ℂ) else 0 : V), fun z => (L _).2, ?_⟩
  intro v hv
  have hid : L (evalAt V t ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hL ⟨v, hv⟩
  have hexp : evalAt V t ⟨v, hv⟩
      = ∑ z : ↥t, v (z : G) • fun z' : ↥t => if z = z' then (1 : ℂ) else 0 := by
    have h := pi_eq_sum_univ (evalAt V t ⟨v, hv⟩)
    exact h
  have hsum : (⟨v, hv⟩ : V)
      = ∑ z : ↥t, v (z : G) • (L fun z' : ↥t => if z = z' then (1 : ℂ) else 0 : V) := by
    rw [← hid, hexp, map_sum]
    exact Finset.sum_congr rfl fun z _ => map_smul L _ _
  have hval := congrArg (fun u : V => (u : G → ℂ)) hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
  exact hval

end EvalCoords

section Uniform

variable {G : Type}

private theorem coeff_mem_and_exists_uniform_support (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (C : G → C(AddCircle T, ℂ))
    (hV : ∀ cq : AddCircle T, (fun y : G => C y cq) ∈ V)
    (hfin : ∀ y : G, (Function.support fun n : ℤ => fourierCoeff (⇑(C y)) n).Finite) :
    (∀ n : ℤ, (fun y : G => fourierCoeff (⇑(C y)) n) ∈ V) ∧
    ∃ tfin : Finset ℤ, ∀ (y : G) (n : ℤ), n ∉ tfin → fourierCoeff (⇑(C y)) n = 0 := by
  classical
  obtain ⟨t, e, heV, hcoord⟩ := exists_eval_coords V

  have hCy : ∀ y : G,
      (⇑(C y) : AddCircle T → ℂ) = fun cq : AddCircle T => ∑ z : ↥t, e z y * C (z : G) cq := by
    intro y
    funext cq
    have h := congrFun (hcoord (fun y' : G => C y' cq) (hV cq)) y
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _

  have hcoeff : ∀ (y : G) (n : ℤ),
      fourierCoeff (⇑(C y)) n = ∑ z : ↥t, e z y * fourierCoeff (⇑(C (z : G))) n := by
    intro y n
    have hfn : (fun cq : AddCircle T => ∑ z : ↥t, e z y * C (z : G) cq)
        = ∑ z : ↥t, fun cq : AddCircle T => e z y * C (z : G) cq := by
      funext cq
      rw [Finset.sum_apply]
    have hint : ∀ z : ↥t,
        Integrable (fun cq : AddCircle T => e z y * C (z : G) cq) (@haarAddCircle T hT) :=
      fun z => integrable_of_continuous (continuous_const.mul (map_continuous (C (z : G))))
    have hsum := fourierCoeff.sum (Finset.univ : Finset ↥t)
      (fun z : ↥t => fun cq : AddCircle T => e z y * C (z : G) cq) (fun z _ => hint z)
    calc fourierCoeff (⇑(C y)) n
        = fourierCoeff (fun cq : AddCircle T => ∑ z : ↥t, e z y * C (z : G) cq) n := by
          rw [hCy y]
      _ = fourierCoeff (∑ z : ↥t, fun cq : AddCircle T => e z y * C (z : G) cq) n := by
          rw [hfn]
      _ = (∑ z : ↥t, fourierCoeff fun cq : AddCircle T => e z y * C (z : G) cq) n := by
          rw [hsum]
      _ = ∑ z : ↥t, fourierCoeff (fun cq : AddCircle T => e z y * C (z : G) cq) n := by
          rw [Finset.sum_apply]
      _ = ∑ z : ↥t, e z y * fourierCoeff (⇑(C (z : G))) n :=
          Finset.sum_congr rfl fun z _ => fourierCoeff.const_mul _ _ _
  refine ⟨fun n => ?_, ?_⟩
  · have hfun : (fun y : G => fourierCoeff (⇑(C y)) n)
        = ∑ z : ↥t, fourierCoeff (⇑(C (z : G))) n • e z := by
      funext y
      rw [hcoeff y n, Finset.sum_apply]
      exact Finset.sum_congr rfl fun z _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hfun]
    exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (heV z)
  · refine ⟨(Finset.univ : Finset ↥t).biUnion fun z => (hfin (z : G)).toFinset, ?_⟩
    intro y n hn
    rw [hcoeff y n]
    refine Finset.sum_eq_zero fun z _ => ?_
    have hz : fourierCoeff (⇑(C (z : G))) n = 0 := by
      by_contra hne
      exact hn (Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ z,
        (hfin (z : G)).mem_toFinset.mpr (Function.mem_support.mpr hne)⟩)
    rw [hz, mul_zero]

end Uniform

section SpanGeneric

variable {X : Type} [TopologicalSpace X]

private theorem continuous_of_mem_span' {s : Set (X → ℂ)} (hs : ∀ f ∈ s, Continuous f)
    {v : X → ℂ} (hv : v ∈ span ℂ s) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => exact continuous_const
  | add f g _ _ ihf ihg => exact ihf.add ihg
  | smul c f _ ihf => exact ihf.const_smul c

end SpanGeneric

private theorem eq_sum_fourier_of_vanish (h : C(AddCircle T, ℂ)) (tfin : Finset ℤ)
    (hvan : ∀ n : ℤ, n ∉ tfin → fourierCoeff (⇑h) n = 0) (θ : AddCircle T) :
    h θ = ∑ n ∈ tfin, fourierCoeff (⇑h) n * fourier n θ := by
  have hsummable : Summable (fourierCoeff (⇑h)) := summable_of_ne_finset_zero hvan
  have h1 := has_pointwise_sum_fourier_series_of_summable (f := h) hsummable θ
  have h2 : HasSum (fun n : ℤ => fourierCoeff (⇑h) n • fourier n θ)
      (∑ n ∈ tfin, fourierCoeff (⇑h) n • fourier n θ) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [hvan n hn, zero_smul]
  have heq := h1.unique h2
  simpa [smul_eq_mul] using heq

section GenericClosure

variable {G : Type} [Group G]

private theorem rightTranslatesSpanFinite_add {K : Subgroup G} {f₁ f₂ : G → ℂ}
    (h₁ : RightTranslatesSpanFinite K f₁) (h₂ : RightTranslatesSpanFinite K f₂) :
    RightTranslatesSpanFinite K (f₁ + f₂) := by
  classical
  obtain ⟨s₁, hs₁⟩ := h₁
  obtain ⟨s₂, hs₂⟩ := h₂
  refine ⟨s₁ ∪ s₂, fun k hk => ?_⟩
  have e : (fun x => (f₁ + f₂) (x * k)) = (fun x => f₁ (x * k)) + fun x => f₂ (x * k) := rfl
  rw [e, Finset.coe_union]
  exact Submodule.add_mem _
    (Submodule.span_mono (fun x hx => Or.inl hx) (hs₁ k hk))
    (Submodule.span_mono (fun x hx => Or.inr hx) (hs₂ k hk))

private theorem rightTranslatesSpanFinite_smul {K : Subgroup G} (c : ℂ) {f : G → ℂ}
    (h : RightTranslatesSpanFinite K f) : RightTranslatesSpanFinite K (c • f) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun k hk => ?_⟩
  have e : (fun x => (c • f) (x * k)) = c • fun x => f (x * k) := rfl
  rw [e]
  exact Submodule.smul_mem _ c (hs k hk)

private theorem rightTranslatesSpanFinite_zero (K : Subgroup G) :
    RightTranslatesSpanFinite K (0 : G → ℂ) :=
  rightTranslatesSpanFinite_const K 0

end GenericClosure

section TranslateSpan

open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open IsDedekindDomain
open scoped IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

private def rTrans (g : AdelicGL2 (𝓞 F) F) (ψ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => ψ (y * g)

private def rTransₗ (g : AdelicGL2 (𝓞 F) F) :
    (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun := rTrans g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rTransₗ_apply (g : AdelicGL2 (𝓞 F) F) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    rTransₗ g ψ = rTrans g ψ := rfl

private theorem continuous_rTrans (g : AdelicGL2 (𝓞 F) F) {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : Continuous ψ) : Continuous (rTrans g ψ) :=
  hψ.comp (continuous_id.mul continuous_const)

private theorem isArchKFinite_add {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : IsArchKFinite F φ₁) (h₂ : IsArchKFinite F φ₂) : IsArchKFinite F (φ₁ + φ₂) :=
  fun w => rightTranslatesSpanFinite_add (h₁ w) (h₂ w)

private theorem isArchKFinite_smul (c : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsArchKFinite F φ) :
    IsArchKFinite F (c • φ) :=
  fun w => rightTranslatesSpanFinite_smul c (h w)

private theorem isArchKFinite_zero' : IsArchKFinite F (0 : AdelicGL2 (𝓞 F) F → ℂ) :=
  fun w => rightTranslatesSpanFinite_zero (archRowIsometrySubgroup F w)

private theorem isArchKFinite_rTrans {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφK : IsArchKFinite F φ)
    {w : InfinitePlace F} {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ archRowIsometrySubgroup F w) :
    IsArchKFinite F (rTrans g φ) := by
  classical
  intro w'
  by_cases hww' : w' = w
  · rw [hww']
    obtain ⟨s, hs⟩ := hφK w
    refine ⟨s, fun k hk => ?_⟩
    have e : (fun x => rTrans g φ (x * k)) = fun x => φ (x * (k * g)) := by
      funext x
      simp only [rTrans, mul_assoc]
    rw [e]
    exact hs (k * g) (Subgroup.mul_mem _ hk hg)
  · obtain ⟨s', hs'⟩ := hφK w'
    refine ⟨s'.image (rTransₗ g), fun k hk => ?_⟩
    have hcomm : k * g = g * k := by
      obtain ⟨k₀, -, rfl⟩ := Subgroup.mem_map.mp hk
      obtain ⟨g₀, -, rfl⟩ := Subgroup.mem_map.mp hg
      exact incl_comm F hww' k₀ g₀
    have e : (fun x => rTrans g φ (x * k)) = rTransₗ g (fun x => φ (x * k)) := by
      funext x
      simp only [rTransₗ_apply, rTrans, mul_assoc, hcomm]
    rw [e, Finset.coe_image]
    have hm := Submodule.mem_map_of_mem (f := rTransₗ g) (hs' k hk)
    rw [Submodule.map_span] at hm
    exact hm

private def transSpan (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ
    (Set.range fun g : ↥(archRowIsometrySubgroup F w) => rTrans (g : AdelicGL2 (𝓞 F) F) φ)

private theorem finiteDimensional_transSpan {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hK : IsArchKFiniteAt F w φ) : FiniteDimensional ℂ (transSpan w φ) := by
  obtain ⟨s, hs⟩ := hK
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (AdelicGL2 (𝓞 F) F → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  have hle : transSpan w φ ≤ Submodule.span ℂ (s : Set (AdelicGL2 (𝓞 F) F → ℂ)) := by
    rw [transSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hs (g : AdelicGL2 (𝓞 F) F) g.2
  exact Submodule.finiteDimensional_of_le hle

private theorem continuous_of_mem_transSpan {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ transSpan w φ) :
    Continuous v := by
  have hv' : v ∈ Submodule.span ℂ
      (Set.range fun g : ↥(archRowIsometrySubgroup F w) => rTrans (g : AdelicGL2 (𝓞 F) F) φ) := hv
  refine continuous_of_mem_span' ?_ hv'
  rintro _ ⟨g, rfl⟩
  exact continuous_rTrans _ hφc

private theorem isArchKFinite_of_mem_transSpan {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφK : IsArchKFinite F φ) {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ transSpan w φ) :
    IsArchKFinite F v := by
  have hv' : v ∈ Submodule.span ℂ
      (Set.range fun g : ↥(archRowIsometrySubgroup F w) => rTrans (g : AdelicGL2 (𝓞 F) F) φ) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact isArchKFinite_rTrans hφK g.2
  | zero => exact isArchKFinite_zero'
  | add f₁ f₂ _ _ ih₁ ih₂ => exact isArchKFinite_add ih₁ ih₂
  | smul c f _ ih => exact isArchKFinite_smul c ih

end TranslateSpan

section UniformExpansion

open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open IsDedekindDomain
open scoped IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

private def coeffFn (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) (n : ℤ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => fourierCoeff (circleFn hw φ y) n

private theorem uniform_expansion (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hφK : IsArchKFinite F φ) :
    (∀ n : ℤ, Continuous (coeffFn hw φ n) ∧ IsArchKFinite F (coeffFn hw φ n)) ∧
    ∃ tfin : Finset ℤ, ∀ (y : AdelicGL2 (𝓞 F) F) (θ : ℝ),
      φ (y * adelicArchGLInclAt F w (rotAt hw θ))
        = ∑ n ∈ tfin, coeffFn hw φ n y * fourier n (θ : AddCircle (2 * Real.pi)) := by
  haveI : FiniteDimensional ℂ (transSpan w φ) := finiteDimensional_transSpan (hφK w)
  let C : AdelicGL2 (𝓞 F) F → C(AddCircle (2 * Real.pi), ℂ) :=
    fun y => ⟨circleFn hw φ y, continuous_circleFn hw hφc y⟩
  have hV : ∀ cq : AddCircle (2 * Real.pi), (fun y => C y cq) ∈ transSpan w φ := by
    intro cq
    induction cq using QuotientAddGroup.induction_on with
    | H c =>
      have e : (fun y => C y (c : AddCircle (2 * Real.pi)))
          = rTrans (adelicArchGLInclAt F w (rotAt hw c)) φ := by
        funext y
        exact circleFn_coe hw φ y c
      rw [e]
      exact Submodule.subset_span ⟨⟨_, rotAt_incl_mem_archRowIsometrySubgroup F hw c⟩, rfl⟩
  have hfin : ∀ y : AdelicGL2 (𝓞 F) F,
      (Function.support fun n : ℤ => fourierCoeff (⇑(C y)) n).Finite := by
    intro y
    obtain ⟨s', hs'⟩ := circleFn_translates_mem_span hw (hφK w) y
    exact support_fourierCoeff_finite (C y) s' hs'
  obtain ⟨hmem, tfin, htfin⟩ := coeff_mem_and_exists_uniform_support (transSpan w φ) C hV hfin
  refine ⟨fun n => ?_, tfin, fun y θ => ?_⟩
  · have hn : coeffFn hw φ n ∈ transSpan w φ := hmem n
    exact ⟨continuous_of_mem_transSpan hφc hn, isArchKFinite_of_mem_transSpan hφK hn⟩
  · have h := eq_sum_fourier_of_vanish (C y) tfin (htfin y) (θ : AddCircle (2 * Real.pi))
    rw [← circleFn_coe hw φ y θ]
    exact h

end UniformExpansion

section MultiPlace

open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open IsDedekindDomain
open scoped IsDedekindDomain

private theorem list_prod_map_congr {α : Type} {f g : α → ℂ} :
    ∀ L : List α, (∀ a ∈ L, f a = g a) → (L.map f).prod = (L.map g).prod := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a L ih =>
    intro h
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, h a (by simp),
      ih (fun b hb => h b (by simp [hb]))]

variable {F : Type} [Field F] [NumberField F]

private def rotProd (L : List {w : InfinitePlace F // w.IsReal}) (θ : {w : InfinitePlace F // w.IsReal} → ℝ) :
    AdelicGL2 (𝓞 F) F :=
  (L.map fun w => adelicArchGLInclAt F w.1 (rotAt w.2 (θ w))).prod

private def charProd (L : List {w : InfinitePlace F // w.IsReal})
    (kd : {w : InfinitePlace F // w.IsReal} → ℤ) (θ : {w : InfinitePlace F // w.IsReal} → ℝ) : ℂ :=
  (L.map fun w => (fourier (kd w) ((θ w : ℝ) : AddCircle (2 * Real.pi)) : ℂ)).prod

private theorem rotProd_nil (θ : {w : InfinitePlace F // w.IsReal} → ℝ) : rotProd [] θ = 1 := by
  unfold rotProd
  rw [List.map_nil, List.prod_nil]

private theorem rotProd_cons (w : {w : InfinitePlace F // w.IsReal}) (L : List {w : InfinitePlace F // w.IsReal})
    (θ : {w : InfinitePlace F // w.IsReal} → ℝ) :
    rotProd (w :: L) θ = adelicArchGLInclAt F w.1 (rotAt w.2 (θ w)) * rotProd L θ := by
  unfold rotProd
  rw [List.map_cons, List.prod_cons]

omit [NumberField F] in
private theorem charProd_nil (kd : {w : InfinitePlace F // w.IsReal} → ℤ)
    (θ : {w : InfinitePlace F // w.IsReal} → ℝ) : charProd [] kd θ = 1 := by
  unfold charProd
  rw [List.map_nil, List.prod_nil]

omit [NumberField F] in
private theorem charProd_cons (w : {w : InfinitePlace F // w.IsReal}) (L : List {w : InfinitePlace F // w.IsReal})
    (kd : {w : InfinitePlace F // w.IsReal} → ℤ) (θ : {w : InfinitePlace F // w.IsReal} → ℝ) :
    charProd (w :: L) kd θ
      = (fourier (kd w) ((θ w : ℝ) : AddCircle (2 * Real.pi)) : ℂ) * charProd L kd θ := by
  unfold charProd
  rw [List.map_cons, List.prod_cons]

private theorem multi_real_expansion {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hφK : IsArchKFinite F φ) :
    ∀ L : List {w : InfinitePlace F // w.IsReal}, L.Nodup →
      ∃ (ι : Type) (_ : Fintype ι) (Cf : ι → AdelicGL2 (𝓞 F) F → ℂ)
        (kd : ι → {w : InfinitePlace F // w.IsReal} → ℤ),
        (∀ j : ι, Continuous (Cf j) ∧ IsArchKFinite F (Cf j)) ∧
        ∀ (y : AdelicGL2 (𝓞 F) F) (θ : {w : InfinitePlace F // w.IsReal} → ℝ),
          φ (y * rotProd L θ) = ∑ j : ι, Cf j y * charProd L (kd j) θ := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨Unit, inferInstance, fun _ => φ, fun _ _ => 0, fun _ => ⟨hφc, hφK⟩, fun y θ => ?_⟩
    rw [rotProd_nil, mul_one]
    simp [charProd_nil]
  | cons w₀ L ih =>
    intro hL
    obtain ⟨hw₀L, hLnd⟩ := List.nodup_cons.mp hL
    obtain ⟨ι, hι, Cf, kd, hCf, hexp⟩ := ih hLnd
    choose tfin htfin using fun j : ι => (uniform_expansion w₀.2 (hCf j).1 (hCf j).2).2
    have hcoef : ∀ (j : ι) (n : ℤ),
        Continuous (coeffFn w₀.2 (Cf j) n) ∧ IsArchKFinite F (coeffFn w₀.2 (Cf j) n) :=
      fun j n => (uniform_expansion w₀.2 (hCf j).1 (hCf j).2).1 n
    refine ⟨(Σ j : ι, ↥(tfin j)), inferInstance,
      fun p => coeffFn w₀.2 (Cf p.1) (p.2 : ℤ),
      fun p w => if w = w₀ then (p.2 : ℤ) else kd p.1 w,
      fun p => hcoef p.1 p.2, fun y θ => ?_⟩
    rw [rotProd_cons, ← mul_assoc, hexp (y * adelicArchGLInclAt F w₀.1 (rotAt w₀.2 (θ w₀))) θ]
    simp_rw [htfin]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_coe_sort (s := tfin j)]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [charProd_cons, ite_eq_left rfl, mul_assoc]
    congr 2
    unfold charProd
    refine list_prod_map_congr L fun w hw => ?_
    have hne : ¬ w = w₀ := fun h => hw₀L (h ▸ hw)
    dsimp only
    rw [ite_eq_right hne]

end MultiPlace

end BigCellExpansion.RealPlaces

end

noncomputable section

namespace BigCellExpansion
namespace Iwasawa

open Matrix
open scoped Matrix
open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open scoped NumberField.InfinitePlace.Completion

open AutomorphicForm AutomorphicForm.WindowedSiegel BigCellExpansion.RealPlaces

open scoped ComplexConjugate

section ExplicitUnitary

private def bR (ζ : ℂ) : ℝ := 1 + ‖ζ‖ ^ 2

private theorem bR_pos (ζ : ℂ) : 0 < bR ζ := by unfold bR; positivity

private def ρR (ζ : ℂ) : ℝ := bR ζ ^ (-(1 / 2 : ℝ))

private theorem ρR_pos (ζ : ℂ) : 0 < ρR ζ := Real.rpow_pos_of_pos (bR_pos ζ) _

end ExplicitUnitary

section Bridges

variable (F : Type) [Field F] [NumberField F]

open NumberField.AdelicLevel IsDedekindDomain

private theorem finmat_ext {A B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (finAdeleEval (𝓞 F) F v).mapMatrix A = (finAdeleEval (𝓞 F) F v).mapMatrix B) :
    A = B := by
  ext i j v
  have hv := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M i j) (h v)
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply] using hv

end Bridges

section FinPart

open NumberField.AdelicLevel IsDedekindDomain

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

variable (xf : FiniteAdeleRing (𝓞 F) F)

private def locK (v : HeightOneSpectrum (𝓞 F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  if xf v ∈ v.adicCompletionIntegers F then !![0, 1; 1, xf v] else !![-1, 0; (xf v)⁻¹, 1]

private def locKinv (v : HeightOneSpectrum (𝓞 F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  if xf v ∈ v.adicCompletionIntegers F then !![-(xf v), 1; 1, 0] else !![-1, 0; (xf v)⁻¹, 1]

private theorem inv_mem_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (h : xf v ∉ v.adicCompletionIntegers F) :
    (xf v)⁻¹ ∈ v.adicCompletionIntegers F :=
  ((v.adicCompletionIntegers F).mem_or_inv_mem (xf v)).resolve_left h

private theorem locK_mul_locKinv (v : HeightOneSpectrum (𝓞 F)) : locK xf v * locKinv xf v = 1 := by
  unfold locK locKinv
  split_ifs with h
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem locKinv_mul_locK (v : HeightOneSpectrum (𝓞 F)) : locKinv xf v * locK xf v = 1 := by
  unfold locK locKinv
  split_ifs with h
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem locK_mem (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) : locK xf v i j ∈ v.adicCompletionIntegers F := by
  unfold locK
  split_ifs with h
  · fin_cases i <;> fin_cases j <;> simp [h, zero_mem, one_mem]
  · have h' := inv_mem_of_not_mem xf h
    fin_cases i <;> fin_cases j <;> simp [h', zero_mem, one_mem]

private theorem locKinv_mem (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    locKinv xf v i j ∈ v.adicCompletionIntegers F := by
  unfold locKinv
  split_ifs with h
  · fin_cases i <;> fin_cases j <;> simp [h, zero_mem, one_mem]
  · have h' := inv_mem_of_not_mem xf h
    fin_cases i <;> fin_cases j <;> simp [h', zero_mem, one_mem]

private def entryF (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨f, Filter.Eventually.of_forall hf⟩

private theorem entryF_apply (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : entryF f hf v = f v := rfl

private def kffVal : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => entryF (fun v => locK xf v i j) (fun v => locK_mem xf v i j)

private def kffInv : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => entryF (fun v => locKinv xf v i j) (fun v => locKinv_mem xf v i j)

private theorem eval_kffVal (v : HeightOneSpectrum (𝓞 F)) :
    (finAdeleEval (𝓞 F) F v).mapMatrix (kffVal xf) = locK xf v := by
  ext i j; rfl

private theorem eval_kffInv (v : HeightOneSpectrum (𝓞 F)) :
    (finAdeleEval (𝓞 F) F v).mapMatrix (kffInv xf) = locKinv xf v := by
  ext i j; rfl

private theorem kffVal_mul_kffInv : kffVal xf * kffInv xf = 1 :=
  finmat_ext F fun v => by rw [map_mul, eval_kffVal, eval_kffInv, locK_mul_locKinv, map_one]

private theorem kffInv_mul_kffVal : kffInv xf * kffVal xf = 1 :=
  finmat_ext F fun v => by rw [map_mul, eval_kffVal, eval_kffInv, locKinv_mul_locK, map_one]

end FinPart

section Global

open NumberField.AdelicLevel IsDedekindDomain

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private def kFval (x : AdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, kffVal x.2 i j)

private def kFinv (x : AdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, kffInv x.2 i j)

private theorem kFval_entry (x : AdeleRing (𝓞 F) F) (i j : Fin 2) (v : InfinitePlace F) :
    (kFval F x i j).1 v
      = ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) v := rfl

private theorem kFinv_entry (x : AdeleRing (𝓞 F) F) (i j : Fin 2) (v : InfinitePlace F) :
    (kFinv F x i j).1 v
      = ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) v := rfl

private theorem projArch_kFval (x : AdeleRing (𝓞 F) F) (v : InfinitePlace F) :
    (projArch F v).mapMatrix (kFval F x) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply, kFval_entry, Matrix.one_apply]
  split_ifs <;> rfl

private theorem projArch_kFinv (x : AdeleRing (𝓞 F) F) (v : InfinitePlace F) :
    (projArch F v).mapMatrix (kFinv F x) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply, kFinv_entry, Matrix.one_apply]
  split_ifs <;> rfl

private theorem projFin_kFval (x : AdeleRing (𝓞 F) F) : (projFin F).mapMatrix (kFval F x) = kffVal x.2 := by
  ext i j; rfl

private theorem projFin_kFinv (x : AdeleRing (𝓞 F) F) : (projFin F).mapMatrix (kFinv F x) = kffInv x.2 := by
  ext i j; rfl

private theorem kFval_mul_kFinv (x : AdeleRing (𝓞 F) F) : kFval F x * kFinv F x = 1 := by
  apply matrix_ext_of_proj
  · intro v
    rw [map_mul, projArch_kFval, projArch_kFinv, one_mul, map_one]
  · rw [map_mul, projFin_kFval, projFin_kFinv, kffVal_mul_kffInv, map_one]

private theorem kFinv_mul_kFval (x : AdeleRing (𝓞 F) F) : kFinv F x * kFval F x = 1 := by
  apply matrix_ext_of_proj
  · intro v
    rw [map_mul, projArch_kFval, projArch_kFinv, one_mul, map_one]
  · rw [map_mul, projFin_kFval, projFin_kFinv, kffInv_mul_kffVal, map_one]

private def kF (x : AdeleRing (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  ⟨kFval F x, kFinv F x, kFval_mul_kFinv F x, kFinv_mul_kFval F x⟩

private theorem kF_coe (x : AdeleRing (𝓞 F) F) :
    ((kF F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = kFval F x := rfl

end Global

end BigCellExpansion.Iwasawa

end

namespace BigCellExpansion
namespace LevelExpansion

open MeasureTheory
open scoped MeasureTheory
open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.AdelicHaar
open scoped NumberField.AdelicHaar
open NumberField.AdelicLevel
open scoped NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

variable {G : Type*} [Mul G]

variable (F : Type) [Field F] [NumberField F]

open BigCellExpansion.Iwasawa

end BigCellExpansion.LevelExpansion

namespace BigCellExpansion
namespace QuotientChar

open MeasureTheory
open scoped MeasureTheory
open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.AdelicHaar
open scoped NumberField.AdelicHaar
open NumberField.AdelicLevel
open scoped NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm
open scoped NNReal

end BigCellExpansion.QuotientChar

namespace BigCellExpansion
namespace ArchExpansion

open MeasureTheory
open scoped MeasureTheory
open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.AdelicHaar
open scoped NumberField.AdelicHaar
open NumberField.AdelicLevel
open scoped NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

noncomputable section

section ComplexPort

open Matrix
open scoped Matrix
open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.InfinitePlace.NumberField
open scoped NumberField.InfinitePlace.NumberField
open NumberField.InfinitePlace
open scoped NumberField.InfinitePlace
open NumberField.InfinitePlace.NumberField.InfinitePlace
open scoped NumberField.InfinitePlace.NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open scoped NumberField.InfinitePlace.Completion

open AutomorphicForm AutomorphicForm.WindowedSiegel BigCellExpansion.RealPlaces BigCellExpansion.Iwasawa

open scoped ComplexConjugate

section MonoClass

private def monoC (d : ℕ × ℕ × ℕ) (ζ : ℂ) : ℂ :=
  ζ ^ d.1 * (starRingEnd ℂ) ζ ^ d.2.1 * (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) ^ (-((d.2.2 : ℂ) / 2))

private theorem base_ne_zero (ζ : ℂ) : (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

private theorem monoC_mul (d d' : ℕ × ℕ × ℕ) (ζ : ℂ) :
    monoC d ζ * monoC d' ζ = monoC (d.1 + d'.1, d.2.1 + d'.2.1, d.2.2 + d'.2.2) ζ := by
  unfold monoC
  dsimp only
  have h : (-(((d.2.2 + d'.2.2 : ℕ) : ℂ) / 2)) = (-((d.2.2 : ℂ) / 2)) + (-((d'.2.2 : ℂ) / 2)) := by
    push_cast; ring
  rw [h, Complex.cpow_add _ _ (base_ne_zero ζ), pow_add, pow_add]
  ring

private def IsMonoComb (f : ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (d : ι → ℕ × ℕ × ℕ),
    (∀ i, (d i).1 + (d i).2.1 ≤ (d i).2.2) ∧ ∀ ζ : ℂ, f ζ = ∑ i, c i * monoC (d i) ζ

private theorem IsMonoComb.add {f g : ℂ → ℂ} (hf : IsMonoComb f) (hg : IsMonoComb g) :
    IsMonoComb (fun ζ => f ζ + g ζ) := by
  obtain ⟨ι, hι, c, d, hd, hf⟩ := hf
  obtain ⟨ι', hι', c', d', hd', hg⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim d d', fun i => ?_, fun ζ => ?_⟩
  · cases i with
    | inl i => exact hd i
    | inr i => exact hd' i
  · show f ζ + g ζ = _
    rw [hf ζ, hg ζ, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]

private theorem IsMonoComb.const_mul {f : ℂ → ℂ} (a : ℂ) (hf : IsMonoComb f) :
    IsMonoComb (fun ζ => a * f ζ) := by
  obtain ⟨ι, hι, c, d, hd, hf⟩ := hf
  refine ⟨ι, hι, fun i => a * c i, d, hd, fun ζ => ?_⟩
  show a * f ζ = _
  rw [hf ζ, Finset.mul_sum]
  simp only [mul_assoc]

private theorem IsMonoComb.mul {f g : ℂ → ℂ} (hf : IsMonoComb f) (hg : IsMonoComb g) :
    IsMonoComb (fun ζ => f ζ * g ζ) := by
  obtain ⟨ι, hι, c, d, hd, hf⟩ := hf
  obtain ⟨ι', hι', c', d', hd', hg⟩ := hg
  refine ⟨ι × ι', inferInstance, fun p => c p.1 * c' p.2,
    fun p => ((d p.1).1 + (d' p.2).1, (d p.1).2.1 + (d' p.2).2.1, (d p.1).2.2 + (d' p.2).2.2),
    fun p => ?_, fun ζ => ?_⟩
  · have h1 := hd p.1
    have h2 := hd' p.2
    dsimp only
    omega
  · show f ζ * g ζ = _
    rw [hf ζ, hg ζ, Fintype.sum_prod_type]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [← monoC_mul]
    ring

end MonoClass

end ComplexPort

end

end BigCellExpansion.ArchExpansion

namespace BigCellExpansion
namespace BorelValue

open MeasureTheory
open scoped MeasureTheory
open NumberField
open scoped NumberField
open NumberField
open scoped NumberField
open NumberField.AdelicHaar
open scoped NumberField.AdelicHaar
open NumberField.AdelicLevel
open scoped NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

section ChiBracket

open scoped Classical
open NumberField.InfinitePlace.Completion NumberField.TateGlobal NumberField.AdelicVolume
open BigCellExpansion.RealPlaces BigCellExpansion.Iwasawa

variable {F : Type} [Field F] [NumberField F]

private noncomputable def cF (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (AdeleRing (𝓞 F) F)ˣ →* v.adicCompletion F :=
  ((finAdeleEval (𝓞 F) F v).comp (projFin F)).toMonoidHom.comp (Units.coeHom (AdeleRing (𝓞 F) F))

private theorem cF_apply (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (AdeleRing (𝓞 F) F)ˣ) :
    cF v u = (((u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v := rfl

end ChiBracket

end BigCellExpansion.BorelValue

end

namespace BigCellExpansion
namespace Assembly

end BigCellExpansion.Assembly

end AutomorphicForm
