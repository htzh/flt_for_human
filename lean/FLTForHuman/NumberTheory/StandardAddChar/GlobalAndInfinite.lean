/-
  The standard additive character: its global form and its two infinite places.

  `stdAddChar F` is the character of the adèles of a number field `F` obtained by composing the
  adelic trace `F → ℚ` with the standard character `psiQ` of `ℚ`:

    `stdAddChar F = (adelicTraceData F).psiK = psiQ.compAddMonoidHom (adelicTraceData F).adelicTrace`.

  This module records the three things about that character that the rest of the archimedean
  column reads:

  * it *is* a global additive character — principal invariant, continuous and nontrivial
    (`isGlobalAddChar_stdAddChar`, one line from the datum's own bundle);
  * at a finite place of `ℚ` the local component `psiLocal ℚ v`, obtained by composing with the
    single-place embedding `finAdeleSingleAt`, agrees with the single-place character `psiV v`
    (`psiLocal_rat_eq_psiV`).  On `ℚ` the trace is the identity, so the whole content is
    `traceInt ℚ = id` and `traceFinHom ℚ = id`, both from the density of the diagonal in the
    integral adèles (`eq_traceInt`);
  * at a single infinite place the value is `exp (2πi t)` for a real place `w`, read through
    `ringEquivRealOfIsReal`, and `exp (2πi · 2 Re z)` for a complex place, read through
    `ringEquivComplexOfIsComplex`.  The archimedean trace of `F` over `ℚ` is
    `∑ w, mult w * Re (extensionEmbedding w (x w))` (`infTraceSum`), so at a single infinite place
    it is `mult w · Re` of that place's embedding (`infTraceSum_single_of_isReal` /
    `…_of_isComplex`), and `mult w` is `1` at a real place and `2` at a complex one.

  Transcription: the four pins are `S_` files of the FLT corpus (pinned `aa2d8b3`), 10 / 69 / 62 /
  61 lines with 1 / 5 / 3 / 3 declarations.  The three headline rows replace the pins' `solution`
  and are stated at its text byte-for-byte; the pins' other public declarations
  (`infTraceSum_single_of_isReal`, `infTraceSum_single_of_isComplex`, `psiArch_ratArchLine`) are
  transcribed above them, and the `psiLocal_rat_eq_psiV` pin's four `private` helpers are
  transcribed with their `private` markers.

  spec-pin: P2M/Sol/S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar.lean
  spec-pin: P2M/Sol/S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV.lean
  spec-pin: P2M/Sol/S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal.lean
  spec-pin: P2M/Sol/S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex.lean

  ## Port deltas

  * `psiArch_ratArchLine` is declared **once**.  Both infinite-place pins carry it (identical
    statement, one under `PsiLine17` and one under `PsiLine40`, each pin's private search-stage
    namespace); the port folds those namespaces into `NumberField.StandardAddChar` and would
    otherwise duplicate the declaration, which `dedup --within` reads as a cluster.  The other
    three transcribed declarations are pairwise distinct, so nothing else is shared.
  * The two pin blocks' `open scoped Classical in` / `open … in` prefixes are replaced by the
    file-level `open scoped Classical` and by the `open` list below (`NumberField.AdelicTrace`,
    `NumberField.AdelicBox`, `NumberField.InfinitePlace`, `…InfinitePlace.Completion`), which is
    what those prefixes were reaching for.  Statement-neutral.
  * **Public/private choice.**  The four helpers of the `psiLocal_rat_eq_psiV` pin keep the pin's
    `private` markers and are therefore skipped by `check_port` and `scaffold_audit` (FR-0242);
    their statements are the pin's and are diffed by hand in the report.  All other declarations
    are public in the pin and stay public here.
  * No import was added: the scaffold's seven cover every premise (`adelicTraceData`,
    `isGlobalAddChar_psiK`, `psiQ_apply`, `psiLocal_apply`, `traceInt` / `eq_traceInt` /
    `traceInt_diag` / `diag_eq`, `traceFinHom_structureMap`, `traceFinHom_algebraMap`,
    `exists_algebraMap_add_mem_integralFiniteAdeles`, `finAdeleSingleAt`,
    `infTraceSum` / `traceInfHom`, `psiArch` / `psiArchPlace` / `ratArchLine`, `mult_isReal` /
    `mult_isComplex`, `ringEquivRealOfIsReal` / `ringEquivComplexOfIsComplex`).
  * **Mathlib drift in the pin bodies (FR-0255, and one instance of the FR-0245 class).**  At
    `v4.34` `AdeleRing R K` and `InfiniteAdeleRing K` are plain `def`s (products/Pi types), and
    `rw` matches at `implicit` transparency, i.e. it does **not** unfold them.  Every pin step
    that rewrites *into* the pair or the tuple — `AdelicTraceData.adelicTrace_apply`,
    `psiQ_apply`, `traceInfHom_apply` — therefore fails with "the target expression is not
    type-correct under the `implicit` transparency level", because a `Prod.mk`/`Pi.single` term
    is not syntactically of type `AdeleRing …`/`InfiniteAdeleRing …`.  Three sites, body only:
    - `psiLocal_rat_apply`: the pin's `rw [psiLocal_apply, …, psiQ_apply]` + `change` became
      `have hsplit : … = psiArch (… traceInf 0) * psiFin (traceFinHom ℚ …) := rfl`, then
      `rw [hsplit, map_zero, …]`.  The `rfl` is a term-mode defeq check at the default
      transparency, which does see through the `def`s.
    - Both infinite-place rows: the pin's `rw [AdelicTraceData.psiK_apply,
      AdelicTraceData.adelicTrace_apply, psiQ_apply]` became the same `have hsplit : … := rfl`.
    - The two `hinf` blocks: the pin's `rw [traceInfHom_apply, infTraceSum_single_of_…]` became
      `show ratArchLine (infTraceSum K (Pi.single …)) = ratArchLine t` (the defeq content of
      `traceInfHom_apply`, `rfl`) followed by the pin's own `rw [infTraceSum_single_of_…]`, which
      is a *ground* equation and so matches syntactically.
    No statement (and no `private` helper's statement) is changed: the four private helpers all
    hash equal to the pin's.  The other FR-0255 deprecations do not occur in these four pins (no
    `zero_le'`, no `if_pos` / `if_neg`, no `haveI` / `letI` site).
  * Heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N`, **never installed**):
    silent at **3000**, first failure at **1500** (the worst declaration is
    `traceFinHom_rat_apply`).  The project cap is 4000000; the module is ~6 s wall.

  The module is the whole public surface of its four pins, so its wire is complete.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLTForHuman.NumberTheory.NumberField.StandardGlobalAddChar
import FLTForHuman.NumberTheory.NumberField.StandardGlobalAddCharRat
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar
import FLTForHuman.NumberTheory.NumberField.AdelicTraceFin
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.LanglandsTunnell.StandardLocalConstantsAt

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open NumberField.StandardAddChar
open NumberField.AdelicTrace NumberField.AdelicBox
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

namespace NumberField.StandardAddChar

/-! ## The standard character is a global additive character -/

theorem isGlobalAddChar_stdAddChar
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) :=
  (adelicTraceData F).isGlobalAddChar_psiK

/-! ## The local component at a finite place of `ℚ` is `psiV`

On `ℚ` the adelic trace is the identity: `traceInt ℚ = id` on the integral adèles (from the
density of the diagonal, `eq_traceInt`), hence `traceFinHom ℚ = id`, and the product defining
`psiFin` collapses to the single place `v`. -/

private theorem algebraMap_trace_int (a : 𝓞 ℚ) :
    algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 ℚ) a) = a := by
  obtain ⟨n, rfl⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) a
  rw [Algebra.trace_algebraMap, RingOfIntegers.rank, Module.finrank_self, one_smul]

private theorem traceInt_rat : traceInt ℚ = AddMonoidHom.id _ := by
  symm
  refine eq_traceInt ℚ continuous_id fun a => ?_
  rw [traceInt_diag, algebraMap_trace_int, AddMonoidHom.id_apply, diag_eq]

private theorem traceFinHom_rat_apply (x : FiniteAdeleRing (𝓞 ℚ) ℚ) : traceFinHom ℚ x = x := by
  obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 ℚ) ℚ x
  let w : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ :=
    fun v => ⟨(algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x) v, hk v⟩
  have hsm : RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
        (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite w
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x :=
    RestrictedProduct.ext _ _ fun v => rfl
  have h1 : traceFinHom ℚ (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + x := by
    rw [← hsm, traceFinHom_structureMap, traceInt_rat, AddMonoidHom.id_apply]
  have h2 : traceFinHom ℚ (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := by
    rw [traceFinHom_algebraMap]
    congr 1
    exact trace_rat_apply k
  rw [map_add, h2] at h1
  exact add_left_cancel h1

private theorem psiLocal_rat_apply (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    psiLocal ℚ v x = psiV v x := by
  have hsplit : psiLocal ℚ v x
      = psiArch ((adelicTraceData ℚ).traceInf (0 : InfiniteAdeleRing ℚ))
        * psiFin (traceFinHom ℚ (finAdeleSingleAt ℚ v x)) := rfl
  rw [hsplit, map_zero, AddChar.map_zero_eq_one, one_mul, traceFinHom_rat_apply, psiFin_apply]
  rw [finprod_eq_single (fun w => psiV w (finAdeleSingleAt ℚ v x w)) v (fun w hw => by
    show psiV w (finAdeleSingleAt ℚ v x w) = 1
    rw [finAdeleSingleAt_apply_of_ne ℚ v x hw]
    exact AddChar.map_zero_eq_one _)]
  show psiV v (finAdeleSingleAt ℚ v x v) = psiV v x
  rw [finAdeleSingleAt_apply_self]

theorem psiLocal_rat_eq_psiV
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    psiLocal ℚ v = psiV v :=
  AddChar.ext _ _ (psiLocal_rat_apply v)

/-! ## The value at a single infinite place

At a single infinite place `w` the archimedean sum has one nonzero term, so the trace is
`mult w · Re` of the place's own embedding; the standard character of `ℚ` at its single
archimedean place is `t ↦ exp (2πi t)`. -/

theorem infTraceSum_single_of_isReal (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (t : ℝ) : infTraceSum F (Pi.single w ((ringEquivRealOfIsReal hw).symm t)) = t := by
  unfold infTraceSum
  rw [Finset.sum_eq_single w]
  · rw [Pi.single_eq_same, mult_isReal ⟨w, hw⟩]
    have hre : (extensionEmbedding w ((ringEquivRealOfIsReal hw).symm t)).re = t := by
      rw [← extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_re, ← ringEquivRealOfIsReal_apply,
        RingEquiv.apply_symm_apply]
    rw [hre]
    push_cast
    ring
  · intro w' _ hw'
    rw [Pi.single_eq_of_ne hw', map_zero, Complex.zero_re, mul_zero]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem psiArch_ratArchLine (t : ℝ) :
    psiArch (ratArchLine t) = Complex.exp (2 * Real.pi * Complex.I * t) := by
  have h1 : psiArch (ratArchLine t) = psiArchPlace default (ratArchLine t default) := by
    rw [psiArch_apply]
    exact finprod_unique _
  rw [h1, psiArchPlace_apply, ratArchLine_apply,
    ← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem infTraceSum_single_of_isComplex (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (z : ℂ) : infTraceSum F (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z)) = 2 * z.re := by
  unfold infTraceSum
  rw [Finset.sum_eq_single w]
  · rw [Pi.single_eq_same, mult_isComplex ⟨w, hw⟩]
    have hre : (extensionEmbedding w ((ringEquivComplexOfIsComplex hw).symm z)).re = z.re := by
      rw [← ringEquivComplexOfIsComplex_apply hw, RingEquiv.apply_symm_apply]
    rw [hre]
    push_cast
    ring
  · intro w' _ hw'
    rw [Pi.single_eq_of_ne hw', map_zero, Complex.zero_re, mul_zero]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem stdAddChar_single_infinitePlace_of_isReal
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * t) := by
  show (adelicTraceData K).psiK _ = _
  have hsplit : (adelicTraceData K).psiK
      (show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0))
      = psiArch ((adelicTraceData K).traceInf
          ((show (AdeleRing (𝓞 K) K) from
            (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0))).1)
        * psiFin ((adelicTraceData K).traceFin
          ((show (AdeleRing (𝓞 K) K) from
            (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0))).2) := rfl
  have hfin : (adelicTraceData K).traceFin
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0))).2 = 0 := by
    show (adelicTraceData K).traceFin 0 = 0
    exact map_zero _
  have hinf : (adelicTraceData K).traceInf
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0))).1
        = ratArchLine t := by
    show ratArchLine (infTraceSum K (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t)))
      = ratArchLine t
    rw [infTraceSum_single_of_isReal K w hw t]
  rw [hsplit, hfin, AddChar.map_zero_eq_one, mul_one, hinf, psiArch_ratArchLine]

theorem stdAddChar_single_infinitePlace_of_isComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * ((2 * z.re : ℝ) : ℂ)) := by
  show (adelicTraceData K).psiK _ = _
  have hsplit : (adelicTraceData K).psiK
      (show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))
      = psiArch ((adelicTraceData K).traceInf
          ((show (AdeleRing (𝓞 K) K) from
            (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))).1)
        * psiFin ((adelicTraceData K).traceFin
          ((show (AdeleRing (𝓞 K) K) from
            (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))).2) := rfl
  have hfin : (adelicTraceData K).traceFin
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))).2 = 0 := by
    show (adelicTraceData K).traceFin 0 = 0
    exact map_zero _
  have hinf : (adelicTraceData K).traceInf
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))).1
        = ratArchLine (2 * z.re) := by
    show ratArchLine (infTraceSum K (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z)))
      = ratArchLine (2 * z.re)
    rw [infTraceSum_single_of_isComplex K w hw z]
  rw [hsplit, hfin, AddChar.map_zero_eq_one, mul_one, hinf, psiArch_ratArchLine]

end NumberField.StandardAddChar

end
