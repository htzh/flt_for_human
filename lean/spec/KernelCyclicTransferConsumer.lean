/-
  Cross-module wire test for **D-4**, the conjugation headline and its seam
  (`FLTForHuman/WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean`).

  A `spec/` probe, not a library module. It exists separately from
  `spec/BaseChangeConsumer.lean` because D-4 imports the `IsogenyEndDatum/Engine.lean`
  cone, and `WeierstrassCurve.Affine.normFormulaAlong_of_elliptic` is declared both
  there and in `Velu/RestrictAlong.lean`; no single environment can import both cones
  (see the V2 topic §2.1). It also cannot be folded into
  `spec/IsogenyEndDatumConsumer.lean` without a purpose-built zone, and a separate file
  keeps the deletion probe unambiguous.

  Executed zones (each a real composition, no `#check`, no `sorry`; deleting
  `KernelCyclicTransfer.lean` makes every one of them fail):

  * zone 1 — the seam `ModularCurve.KwD5BetweenCurvesPMOPConjKerEquiv`, produced by the
    pin's `pck_s17`, is instantiated at a pair of `PeriodPair`s: the cyclicity of the
    kernel of the conjugated endomorphism is derived from the hypothesis that `ι`'s
    kernel is cyclic.  The `PeriodPair` gate instances are hypotheses: the port has no
    `L.weierstrassCurve.IsElliptic` instance, and the producer
    `exists_genusOnePlaceGate_isCentred_and_abelTheorem` lives in
    `WeierstrassCurve/GenusOnePlaceGateCentred.lean`, which is not co-importable with
    `Engine.lean` (the `instInfinitePlace` collision, P-2 §3.1);
  * zone 2 — the headline itself, in hypothesis form, at four curves of `ℂ`: both
    conjuncts (cyclicity transfer and the kernel-cardinality equality), the second
    composed with the imported `natCard_ker_pointMapOfPushforward_eq_finrankAlong`;
  * zone 3 — the `algEquiv` engine: `kw_surgehgf4_pck_pmop_equiv_bijective` turns the
    conjugation pushforward into an `AddEquiv` of the two point groups, and
    `kw_surgehgf4_pck_pmop_equiv_left_inv` is the resulting round trip;
  * zone 4 — the identity leg at the concrete curve `y² = x³ + 1` over `ℂ`:
    `kw_surgehgf4_pck_pmop_id` identifies the identity pushforward with the ported
    `IsogenyEndDatum.idDatum`'s point map, which the imported `idDatum_pointEnd` then
    evaluates.
-/
import FLTForHuman.WeierstrassCurve.Isogeny.KernelCyclicTransfer

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve
open WeierstrassCurve WeierstrassCurve.Affine

namespace KernelCyclicTransferConsumer

/-- The concrete curve `y² = x³ + 1` over `ℂ`. -/
abbrev W1 : WeierstrassCurve ℂ := WeierstrassCurve.mk (0 : ℂ) 0 0 0 1

/-- `Δ = -432 ≠ 0`, so `W1` is elliptic. -/
instance : W1.IsElliptic :=
  ⟨IsUnit.mk0 _
    (by norm_num [W1, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩

-- Zone 1: the seam at a pair of `PeriodPair`s (hypothesis form).
example (E E' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [GenusOnePlaceGate L.weierstrassCurve]
    [GenusOnePlaceGate.IsCentred L.weierstrassCurve] [AbelTheorem L.weierstrassCurve]
    [L'.weierstrassCurve.IsElliptic] [GenusOnePlaceGate L'.weierstrassCurve]
    [GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [AbelTheorem L'.weierstrassCurve]
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ι)
    (eE : L.weierstrassCurve.toAffine.FunctionField ≃ₐ[ℂ] E.FunctionField)
    (eE' : L'.weierstrassCurve.toAffine.FunctionField ≃ₐ[ℂ] E'.FunctionField)
    (hι'' : (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral)
    (hfin'' : FiniteAlong ℂ (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι))
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin)).ker) :
    IsAddCyclic (AddMonoidHom.ker (pointMapOfPushforward
        (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hι'' hfin''
        (normFormulaAlong_of_elliptic _ hfin''))) :=
  pck_s17 E E' ι hι hfin L L' eE eE' hι'' hfin'' hcyc

-- Zone 2: the headline in hypothesis form, both conjuncts.
example (E E' D D' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic] [D.IsElliptic] [D'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    [GenusOnePlaceGate D] [GenusOnePlaceGate.IsCentred D] [AbelTheorem D]
    [GenusOnePlaceGate D'] [GenusOnePlaceGate.IsCentred D'] [AbelTheorem D']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin)
    (eE : D.FunctionField ≃ₐ[ℂ] E.FunctionField) (eE' : D'.FunctionField ≃ₐ[ℂ] E'.FunctionField)
    (hι'' : (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι).toRingHom.IsIntegral)
    (hfin'' : FiniteAlong ℂ (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι))
    (hN'' : NormFormulaAlong ℂ (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι) hfin'')
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker) :
    IsAddCyclic (pointMapOfPushforward (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι)
        hι'' hfin'' hN'').ker ∧
      Nat.card (pointMapOfPushforward (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι)
        hι'' hfin'' hN'').ker = finrankAlong ℂ ι := by
  have hconj : ∀ x, eE (ModularCurve.kw_fdn2_qephod_hend21_conjSeam eE eE' ι x) = ι (eE' x) :=
    fun x => eE.apply_symm_apply (ι (eE' x))
  have h := WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
    E E' D D' ι hι hfin hN eE eE' _ hconj hι'' hfin'' hN'' hcyc
  exact ⟨h.1, h.2.trans (natCard_ker_pointMapOfPushforward_eq_finrankAlong E E' ι hι hfin hN)⟩

-- Zone 3: the conjugation pushforward is an additive equivalence, and its round trip.
example (W V : WeierstrassCurve.Affine ℂ) [W.IsElliptic] [V.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) :
    Nonempty (W.Point ≃+ V.Point) :=
  ⟨AddEquiv.ofBijective _
    (ModularCurve.kw_surgehgf4_pck_pmop_equiv_bijective e.symm)⟩

example (W V : WeierstrassCurve.Affine ℂ) [W.IsElliptic] [V.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]
    (e : W.FunctionField ≃ₐ[ℂ] V.FunctionField) (P : W.Point) :
    pointMapOfPushforward e.toAlgHom
        (ModularCurve.kw_surgehgf4_pck_algEquiv_isIntegral e)
        (ModularCurve.kw_surgehgf4_pck_algEquiv_finiteAlong e)
        (normFormulaAlong_of_elliptic _ (ModularCurve.kw_surgehgf4_pck_algEquiv_finiteAlong e))
        (pointMapOfPushforward e.symm.toAlgHom
          (ModularCurve.kw_surgehgf4_pck_algEquiv_isIntegral e.symm)
          (ModularCurve.kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)
          (normFormulaAlong_of_elliptic _
            (ModularCurve.kw_surgehgf4_pck_algEquiv_finiteAlong e.symm)) P)
      = P :=
  ModularCurve.kw_surgehgf4_pck_pmop_equiv_left_inv e P

-- Zone 4: the identity leg at the concrete curve `W1` (gates as hypotheses).
example [GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
    [AbelTheorem W1.toAffine]
    (hι : (AlgHom.id ℂ W1.toAffine.FunctionField).toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ (AlgHom.id ℂ W1.toAffine.FunctionField)) (P : W1.toAffine.Point) :
    pointMapOfPushforward (AlgHom.id ℂ W1.toAffine.FunctionField) hι hfin
        (normFormulaAlong_of_elliptic _ hfin) P
      = (IsogenyEndDatum.idDatum W1.toAffine).pointEnd' P := by
  rw [ModularCurve.kw_surgehgf4_pck_pmop_id hι hfin P,
    IsogenyEndDatum.idDatum_pointEnd W1.toAffine]
  rfl

end KernelCyclicTransferConsumer
