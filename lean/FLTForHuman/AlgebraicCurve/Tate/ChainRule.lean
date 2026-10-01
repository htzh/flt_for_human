/-
Tate chain rule — the derivation half of the Tate agreement, after FLT's
`P2M/Sol/S_AlgebraicCurve_tateChainRule.lean` (2,832 ln, 108 declarations)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateChainRule.lean>),
published by
`Theorems/Thm_AlgebraicCurve_tateChainRule.lean` as `AlgebraicCurve.tateChainRule`.

This is set 3.3b's theory module.  It proves the pin's
`ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule`: the Tate residue at a place `w` of `F`
above `v` is unchanged when the differential coefficient of the pulled-back coordinate
is folded into the argument.  The route is the pin's:

`kwF4gRRTate_chainRule_of_derivationFactor` (the `E`/`F` dictionary) plus
`kwTateRR2_derivationFactorSnd` (the derivation factor), where the derivation is the
`DualDom`-valued `tateResSndDer` and the factor is
`derivation_apply_eq_diffCoeff_smul`.

The pin's first 1,637 lines are the shared row-3.3 prelude already landed by set 3.3a
in `Tate/CommFinite.lean` (40 public rows) and the shared API in
`Defs/TateResidueCurrency.lean`; they are imported, not re-proved.  The pin's seven
`private` prelude helpers are the port's public `Defs/PushPull.lean` /
`Defs/PlaceCompletion.lean` rows.  The pin's `p2m_*` scaffolding, its unused
`variable` blocks, and its `set_option maxHeartbeats 12800000` raises (project cap
4,000,000) are dropped.

The ten `scoped instance`s of the tail (six `instFinDimRange*`, four `DualDom`
instances) are checker-invisible and are landed explicitly.
-/
import FLTForHuman.AlgebraicCurve.Defs.TateResidueCurrency
import FLTForHuman.AlgebraicCurve.Tate.CommFinite
import FLTForHuman.AlgebraicCurve.Tate.Prelude

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open LinearMap Submodule
open AlgebraicCurve AlgebraicCurve.Place
open ModularCurve.KwF4gRRTate

noncomputable section

namespace AlgebraicCurve

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

variable {K F E}

/-- The pullback `kaehlerPullback` commutes with the Kähler differentials: it is the
`K`-linear map `KaehlerDifferential.map K K E F` (the pin's `kaehlerPullback_D`). -/
@[scoped simp] theorem kaehlerPullback_D (e : E) :
    kaehlerPullback K F E (KaehlerDifferential.D K E e)
      = KaehlerDifferential.D K F (algebraMap E F e) :=
  KaehlerDifferential.map_D K K E F e

end CorrectedCarrier

end AlgebraicCurve

namespace ModularCurve.KwF4gRRTate


section AddSnd

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_add_snd (pA φ ψ₁ ψ₂ : V →ₗ[K] V) :
    tateComm pA φ (ψ₁ + ψ₂) = tateComm pA φ ψ₁ + tateComm pA φ ψ₂ := by
  unfold tateComm
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
  abel

theorem tateCommRestrict_add_snd (pA φ ψ₁ ψ₂ : V →ₗ[K] V) :
    tateCommRestrict pA φ (ψ₁ + ψ₂)
      = tateCommRestrict pA φ ψ₁ + tateCommRestrict pA φ ψ₂ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA φ (ψ₁ + ψ₂) a : V)
    = (tateCommRestrict pA φ ψ₁ a : V) + (tateCommRestrict pA φ ψ₂ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply, tateCommRestrict_apply]
  exact congrFun (congrArg DFunLike.coe (tateComm_add_snd pA φ ψ₁ ψ₂)) (a : V)

theorem tateCommTrace_add_snd (pA φ ψ₁ ψ₂ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ₁))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ₂))] :
    haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ (ψ₁ + ψ₂))) := by
      rw [tateCommRestrict_add_snd]; exact instFinDimRangeAdd _ _
    tateCommTrace pA φ (ψ₁ + ψ₂) = tateCommTrace pA φ ψ₁ + tateCommTrace pA φ ψ₂ := by
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ (ψ₁ + ψ₂))) := by
    rw [tateCommRestrict_add_snd]; exact instFinDimRangeAdd _ _
  unfold tateCommTrace
  rw [← finrankTrace_add]
  exact finrankTrace_congr (tateCommRestrict_add_snd pA φ ψ₁ ψ₂)

end AddSnd

section CommutatorVanish

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

scoped instance instFinDimRangeCompRight (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ ∘ₗ ψ)) := by
  rw [LinearMap.range_comp]; infer_instance

scoped instance instFinDimRangeCompLeft (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (ψ ∘ₗ φ)) :=
  Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)

theorem finrankTrace_commutator_eq_zero (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace (φ ∘ₗ ψ - ψ ∘ₗ φ) = 0 := by
  rw [← finrankTrace_sub, finrankTrace_comp_comm ψ φ, sub_self]

end CommutatorVanish

section LeibnizAbstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def piRestrict (pA φ : V →ₗ[K] V) : LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (pA ∘ₗ φ).restrict (fun x _ => LinearMap.mem_range_self pA (φ x))

theorem piRestrict_apply (pA φ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (piRestrict pA φ a : V) = pA (φ (a : V)) := rfl

def epsRestrict (pA φ ψ : V →ₗ[K] V) : LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (pA ∘ₗ φ ∘ₗ (LinearMap.id - pA) ∘ₗ ψ).restrict
    (fun x _ => LinearMap.mem_range_self pA _)

theorem epsRestrict_apply (pA φ ψ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (epsRestrict pA φ ψ a : V) = pA (φ (ψ (a : V) - pA (ψ (a : V)))) := by
  show pA (φ ((LinearMap.id (R := K) (M := V) - pA) (ψ (a : V)))) = _
  rw [LinearMap.sub_apply, LinearMap.id_apply]

theorem piRestrict_comp_eq (pA φ ψ : V →ₗ[K] V) :
    piRestrict pA (φ ∘ₗ ψ) = piRestrict pA φ ∘ₗ piRestrict pA ψ + epsRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext

  show pA (φ (ψ (a : V))) = pA (φ (pA (ψ (a : V)))) + (epsRestrict pA φ ψ a : V)
  rw [epsRestrict_apply, ← map_add, ← map_add]
  congr 2
  abel

theorem tateCommRestrict_eq_bracket (pA f g : V →ₗ[K] V) :
    tateCommRestrict pA f g
      = piRestrict pA f ∘ₗ piRestrict pA g - piRestrict pA g ∘ₗ piRestrict pA f := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  simp only [LinearMap.sub_apply, AddSubgroupClass.coe_sub, LinearMap.comp_apply]
  rw [tateCommRestrict_apply, tateComm_apply, piRestrict_apply, piRestrict_apply,
    piRestrict_apply, piRestrict_apply]

theorem bracket_leibniz_defect {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (F G H : W →ₗ[R] W) :
    (F ∘ₗ (G ∘ₗ H) - (G ∘ₗ H) ∘ₗ F)
      - ((F ∘ₗ G) ∘ₗ H - H ∘ₗ (F ∘ₗ G))
      - ((F ∘ₗ H) ∘ₗ G - G ∘ₗ (F ∘ₗ H))
      = G ∘ₗ (F ∘ₗ H - H ∘ₗ F) - (F ∘ₗ H - H ∘ₗ F) ∘ₗ G := by
  apply LinearMap.ext; intro x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

theorem tateCommTrace_leibniz_snd (pA f g h : V →ₗ[K] V)
    (hfin_fh : FiniteDimensional K (LinearMap.range (tateCommRestrict pA f h)))
    (hfin_gh : FiniteDimensional K (LinearMap.range (epsRestrict pA g h)))
    (hfin_fg : FiniteDimensional K (LinearMap.range (epsRestrict pA f g)))
    (hfin_fh' : FiniteDimensional K (LinearMap.range (epsRestrict pA f h)))
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA f (g ∘ₗ h)))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA (f ∘ₗ g) h))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA (f ∘ₗ h) g))] :
    tateCommTrace pA f (g ∘ₗ h)
      = tateCommTrace pA (f ∘ₗ g) h + tateCommTrace pA (f ∘ₗ h) g := by
  set A := LinearMap.range pA
  set F := piRestrict pA f
  set G := piRestrict pA g
  set H := piRestrict pA h
  set εgh := epsRestrict pA g h
  set εfg := epsRestrict pA f g
  set εfh := epsRestrict pA f h
  set CFH := F ∘ₗ H - H ∘ₗ F
  haveI : FiniteDimensional K (LinearMap.range εgh) := hfin_gh
  haveI : FiniteDimensional K (LinearMap.range εfg) := hfin_fg
  haveI : FiniteDimensional K (LinearMap.range εfh) := hfin_fh'
  haveI hCFH : FiniteDimensional K (LinearMap.range CFH) := by
    have : CFH = tateCommRestrict pA f h := (tateCommRestrict_eq_bracket pA f h).symm
    rw [this]; exact hfin_fh

  have hLHS : tateCommRestrict pA f (g ∘ₗ h)
      = (F ∘ₗ (G ∘ₗ H) - (G ∘ₗ H) ∘ₗ F)
        + (F ∘ₗ εgh - εgh ∘ₗ F) := by
    rw [tateCommRestrict_eq_bracket, piRestrict_comp_eq]
    show piRestrict pA f ∘ₗ (piRestrict pA g ∘ₗ piRestrict pA h + epsRestrict pA g h)
        - (piRestrict pA g ∘ₗ piRestrict pA h + epsRestrict pA g h) ∘ₗ piRestrict pA f = _
    apply LinearMap.ext; intro a
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
    abel
  have hRHS₁ : tateCommRestrict pA (f ∘ₗ g) h
      = ((F ∘ₗ G) ∘ₗ H - H ∘ₗ (F ∘ₗ G))
        + (εfg ∘ₗ H - H ∘ₗ εfg) := by
    rw [tateCommRestrict_eq_bracket, piRestrict_comp_eq]
    show (piRestrict pA f ∘ₗ piRestrict pA g + epsRestrict pA f g) ∘ₗ piRestrict pA h
        - piRestrict pA h ∘ₗ (piRestrict pA f ∘ₗ piRestrict pA g + epsRestrict pA f g) = _
    apply LinearMap.ext; intro a
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
    abel
  have hRHS₂ : tateCommRestrict pA (f ∘ₗ h) g
      = ((F ∘ₗ H) ∘ₗ G - G ∘ₗ (F ∘ₗ H))
        + (εfh ∘ₗ G - G ∘ₗ εfh) := by
    rw [tateCommRestrict_eq_bracket, piRestrict_comp_eq]
    show (piRestrict pA f ∘ₗ piRestrict pA h + epsRestrict pA f h) ∘ₗ piRestrict pA g
        - piRestrict pA g ∘ₗ (piRestrict pA f ∘ₗ piRestrict pA h + epsRestrict pA f h) = _
    apply LinearMap.ext; intro a
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
    abel

  have hDefect : tateCommRestrict pA f (g ∘ₗ h)
      - tateCommRestrict pA (f ∘ₗ g) h - tateCommRestrict pA (f ∘ₗ h) g
      = (G ∘ₗ CFH - CFH ∘ₗ G)
        + (F ∘ₗ εgh - εgh ∘ₗ F)
        - (εfg ∘ₗ H - H ∘ₗ εfg)
        - (εfh ∘ₗ G - G ∘ₗ εfh) := by
    rw [hLHS, hRHS₁, hRHS₂]
    have := bracket_leibniz_defect (R := K) F G H
    show _ = (G ∘ₗ CFH - CFH ∘ₗ G) + _ - _ - _
    rw [show G ∘ₗ CFH - CFH ∘ₗ G
      = (F ∘ₗ (G ∘ₗ H) - (G ∘ₗ H) ∘ₗ F)
        - ((F ∘ₗ G) ∘ₗ H - H ∘ₗ (F ∘ₗ G))
        - ((F ∘ₗ H) ∘ₗ G - G ∘ₗ (F ∘ₗ H)) from this.symm]
    abel

  have hT1 : finrankTrace (G ∘ₗ CFH - CFH ∘ₗ G) = 0 :=
    finrankTrace_commutator_eq_zero G CFH
  have hT2 : finrankTrace (F ∘ₗ εgh - εgh ∘ₗ F) = 0 :=
    finrankTrace_commutator_eq_zero F εgh
  have hT3' : finrankTrace (H ∘ₗ εfg - εfg ∘ₗ H) = 0 :=
    finrankTrace_commutator_eq_zero H εfg
  have hT3 : finrankTrace (εfg ∘ₗ H - H ∘ₗ εfg) = 0 := by
    have hneg : εfg ∘ₗ H - H ∘ₗ εfg = -(H ∘ₗ εfg - εfg ∘ₗ H) := by abel
    rw [show finrankTrace (εfg ∘ₗ H - H ∘ₗ εfg)
        = finrankTrace (-(H ∘ₗ εfg - εfg ∘ₗ H)) from finrankTrace_congr hneg,
      finrankTrace_neg, hT3', _root_.neg_zero]
  have hT4' : finrankTrace (G ∘ₗ εfh - εfh ∘ₗ G) = 0 :=
    finrankTrace_commutator_eq_zero G εfh
  have hT4 : finrankTrace (εfh ∘ₗ G - G ∘ₗ εfh) = 0 := by
    have hneg : εfh ∘ₗ G - G ∘ₗ εfh = -(G ∘ₗ εfh - εfh ∘ₗ G) := by abel
    rw [show finrankTrace (εfh ∘ₗ G - G ∘ₗ εfh)
        = finrankTrace (-(G ∘ₗ εfh - εfh ∘ₗ G)) from finrankTrace_congr hneg,
      finrankTrace_neg, hT4', _root_.neg_zero]

  unfold tateCommTrace
  set L := tateCommRestrict pA f (g ∘ₗ h)
  set R₁ := tateCommRestrict pA (f ∘ₗ g) h
  set R₂ := tateCommRestrict pA (f ∘ₗ h) g

  set D := L - R₁ - R₂ with hDdef
  haveI : FiniteDimensional K (LinearMap.range D) := by
    rw [hDdef]; exact instFinDimRangeSub _ _
  have hDtrace : finrankTrace D = 0 := by
    rw [finrankTrace_congr hDefect]

    set T1 := G ∘ₗ CFH - CFH ∘ₗ G
    set T2 := F ∘ₗ εgh - εgh ∘ₗ F
    set T3 := εfg ∘ₗ H - H ∘ₗ εfg
    set T4 := εfh ∘ₗ G - G ∘ₗ εfh
    haveI : FiniteDimensional K (LinearMap.range T1) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range T2) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range T3) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range T4) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range (T1 + T2)) := instFinDimRangeAdd _ _
    haveI : FiniteDimensional K (LinearMap.range (T1 + T2 - T3)) := instFinDimRangeSub _ _
    calc finrankTrace (T1 + T2 - T3 - T4)
        = finrankTrace (T1 + T2 - T3) - finrankTrace T4 := (finrankTrace_sub _ _).symm
      _ = finrankTrace (T1 + T2) - finrankTrace T3 - finrankTrace T4 := by
          rw [(finrankTrace_sub (T1 + T2) T3).symm]
      _ = finrankTrace T1 + finrankTrace T2 - finrankTrace T3 - finrankTrace T4 := by
          rw [finrankTrace_add T1 T2]
      _ = 0 := by rw [hT1, hT2, hT3, hT4]; ring

  have hLdecomp : L = R₁ + R₂ + D := by rw [hDdef]; abel
  rw [finrankTrace_congr hLdecomp, finrankTrace_add, finrankTrace_add, hDtrace, add_zero]

end LeibnizAbstract

section TateResLeibniz

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

theorem finiteDimensional_range_epsRestrict_lmulK (φ ψ : u.adicCompletion) :
    FiniteDimensional K (LinearMap.range
      (epsRestrict (tateProj u) (lmulK u φ) (lmulK u ψ))) := by

  haveI hα := finiteDimensional_range_alphaMap u ψ

  set pA := tateProj u
  set β : (u.adicCompletion ⧸ LinearMap.range pA) →ₗ[K] LinearMap.range pA :=
    (LinearMap.range pA).liftQ
      ((pA ∘ₗ lmulK u φ ∘ₗ (LinearMap.id - pA)).codRestrict (LinearMap.range pA)
        (fun x => LinearMap.mem_range_self pA _))
      (by
        rintro x ⟨y, rfl⟩
        apply Subtype.ext
        show (pA ∘ₗ lmulK u φ ∘ₗ (LinearMap.id - pA)) (pA y) = (0 : u.adicCompletion)
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
        rw [show pA (pA y) = pA y from congrFun (congrArg DFunLike.coe (tateProj_idem u)) y,
          sub_self, _root_.map_zero, _root_.map_zero])
    with hβdef

  have hfactor : epsRestrict pA (lmulK u φ) (lmulK u ψ) = β ∘ₗ alphaMap u ψ := by
    apply LinearMap.ext; intro a; apply Subtype.ext
    rw [epsRestrict_apply]
    rfl
  rw [hfactor, LinearMap.range_comp]
  infer_instance

theorem tateRes_leibniz_snd (hfin : KwF4gRRTateCommFinite K L)
    (f g h : u.adicCompletion) :
    haveI := hfin u f (g * h)
    haveI := hfin u (f * g) h
    haveI := hfin u (f * h) g
    tateRes u f (g * h) = tateRes u (f * g) h + tateRes u (f * h) g := by
  haveI := hfin u f (g * h)
  haveI := hfin u (f * g) h
  haveI := hfin u (f * h) g
  haveI := hfin u f h

  have hlmul : ∀ x y : u.adicCompletion, lmulK u (x * y) = lmulK u x ∘ₗ lmulK u y := by
    intro x y
    apply LinearMap.ext; intro z
    show (x * y) * z = x * (y * z)
    ring

  haveI hL : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f) (lmulK u g ∘ₗ lmulK u h))) := by
    rw [← hlmul g h]; exact hfin u f (g * h)
  haveI hR₁ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f ∘ₗ lmulK u g) (lmulK u h))) := by
    rw [← hlmul f g]; exact hfin u (f * g) h
  haveI hR₂ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f ∘ₗ lmulK u h) (lmulK u g))) := by
    rw [← hlmul f h]; exact hfin u (f * h) g

  have hleib := tateCommTrace_leibniz_snd (tateProj u) (lmulK u f) (lmulK u g) (lmulK u h)
    (hfin u f h)
    (finiteDimensional_range_epsRestrict_lmulK u g h)
    (finiteDimensional_range_epsRestrict_lmulK u f g)
    (finiteDimensional_range_epsRestrict_lmulK u f h)

  unfold tateRes
  unfold tateCommTrace at hleib ⊢
  rw [finrankTrace_congr (by rw [hlmul g h] : tateCommRestrict (tateProj u) (lmulK u f)
        (lmulK u (g * h)) = tateCommRestrict (tateProj u) (lmulK u f)
        (lmulK u g ∘ₗ lmulK u h)),
    finrankTrace_congr (by rw [hlmul f g] : tateCommRestrict (tateProj u)
        (lmulK u (f * g)) (lmulK u h) = tateCommRestrict (tateProj u)
        (lmulK u f ∘ₗ lmulK u g) (lmulK u h)),
    finrankTrace_congr (by rw [hlmul f h] : tateCommRestrict (tateProj u)
        (lmulK u (f * h)) (lmulK u g) = tateCommRestrict (tateProj u)
        (lmulK u f ∘ₗ lmulK u h) (lmulK u g))]
  exact hleib

end TateResLeibniz

section TateResCongr

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem tateRes_congr_fst {fh₁ fh₂ gh : u.adicCompletion} (heq : fh₁ = fh₂)
    [h₁ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁) (lmulK u gh)))]
    [h₂ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₂) (lmulK u gh)))] :
    tateRes u fh₁ gh = tateRes u fh₂ gh := by
  subst heq; rfl

end TateResCongr

section DerivationFactor

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- The pin's `KwF4gRRTateDerivationFactorSnd`: the derivation form of the Tate chain
rule, with the Kähler differential of `g` in place of the pulled-back coordinate. -/
def KwF4gRRTateDerivationFactorSnd [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]
    (hfinF : KwF4gRRTateCommFinite K F) : Prop :=
  ∀ (w : Place K F) [w.DCoordGenerates] (f : w.adicCompletion) (g : F),
    haveI := hfinF w f (algebraMap F w.adicCompletion g)
    haveI := hfinF w (f * algebraMap F w.adicCompletion
      (w.differentialCoeff (KaehlerDifferential.D K F g)))
      (algebraMap F w.adicCompletion w.uniformizer)
    tateRes w f (algebraMap F w.adicCompletion g)
      = tateRes w (f * algebraMap F w.adicCompletion
          (w.differentialCoeff (KaehlerDifferential.D K F g)))
          (algebraMap F w.adicCompletion w.uniformizer)

end DerivationFactor

section Reprice

variable {K F E : Type*} [Field K] [Field F] [Algebra K F]
variable [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

/-- The `E`/`F` dictionary: the derivation factor at the Kähler differential of the
uniformizer is the chain rule at the pulled-back coordinate. -/
theorem kwF4gRRTate_chainRule_of_derivationFactor
    (hfinF : KwF4gRRTateCommFinite K F)
    (hDF : ∀ [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]],
      KwF4gRRTateDerivationFactorSnd K F hfinF) :
    KwF4gRRTateChainRule K F E hfinF := by
  intro _ _ _ _ _ v _ w _ _ fh

  have hDFw := hDF w fh (algebraMap E F v.uniformizer)

  have hker : KaehlerDifferential.D K F (algebraMap E F v.uniformizer)
      = kaehlerPullback K F E v.dCoord :=
    (kaehlerPullback_D (K := K) (F := F) (E := E) v.uniformizer).symm

  have hX : fh * algebraMap F w.adicCompletion
        (w.differentialCoeff (kaehlerPullback K F E v.dCoord))
      = fh * algebraMap F w.adicCompletion
        (w.differentialCoeff (KaehlerDifferential.D K F (algebraMap E F v.uniformizer))) := by
    rw [hker]
  haveI := hfinF w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
  haveI := hfinF w (fh * algebraMap F w.adicCompletion
    (w.differentialCoeff (KaehlerDifferential.D K F (algebraMap E F v.uniformizer))))
    (algebraMap F w.adicCompletion w.uniformizer)
  haveI := hfinF w (fh * algebraMap F w.adicCompletion
    (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
    (algebraMap F w.adicCompletion w.uniformizer)
  calc tateRes w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (KaehlerDifferential.D K F (algebraMap E F v.uniformizer))))
          (algebraMap F w.adicCompletion w.uniformizer) := hDFw
    _ = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
          (algebraMap F w.adicCompletion w.uniformizer) := tateRes_congr_fst w hX.symm

end Reprice

section DualDom

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The `K`-dual of the completion of `F` at `w`, as a type synonym carrying an
`F`-module structure (the pin's `DualDom`). -/
def DualDom (w : Place K F) : Type _ := w.adicCompletion →ₗ[K] K

scoped instance (w : Place K F) : AddCommGroup (DualDom w) :=
  inferInstanceAs (AddCommGroup (w.adicCompletion →ₗ[K] K))

def DualDom.toLM {w : Place K F} (φ : DualDom w) : w.adicCompletion →ₗ[K] K := φ

@[scoped ext] theorem DualDom.ext {w : Place K F} {φ ψ : DualDom w}
    (h : ∀ x, φ.toLM x = ψ.toLM x) : φ = ψ := LinearMap.ext h

@[scoped simp] theorem DualDom.toLM_add {w : Place K F} (φ ψ : DualDom w) :
    (φ + ψ).toLM = φ.toLM + ψ.toLM := rfl

scoped instance (w : Place K F) : Module F (DualDom w) where
  smul h φ := φ.toLM ∘ₗ lmulK w (algebraMap F w.adicCompletion h)
  one_smul φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F w.adicCompletion 1 * x) = φ.toLM x
    rw [_root_.map_one, one_mul]
  mul_smul a b φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (a * b) * x) = φ.toLM (algebraMap F _ b * (algebraMap F _ a * x))
    rw [(algebraMap F w.adicCompletion).map_mul, mul_comm (algebraMap F _ a), mul_assoc]
  smul_zero a := DualDom.ext fun _ => rfl
  smul_add a φ ψ := DualDom.ext fun _ => rfl
  add_smul a b φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (a + b) * x)
      = φ.toLM (algebraMap F _ a * x) + φ.toLM (algebraMap F _ b * x)
    rw [(algebraMap F w.adicCompletion).map_add, add_mul, φ.toLM.map_add]
  zero_smul φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ 0 * x) = 0
    rw [(algebraMap F w.adicCompletion).map_zero, zero_mul, φ.toLM.map_zero]

@[scoped simp] theorem DualDom.smul_apply {w : Place K F} (h : F) (φ : DualDom w)
    (x : w.adicCompletion) :
    (h • φ).toLM x = φ.toLM (algebraMap F w.adicCompletion h * x) := rfl

scoped instance (w : Place K F) : Module K (DualDom w) :=
  inferInstanceAs (Module K (w.adicCompletion →ₗ[K] K))

theorem DualDom.k_smul_apply {w : Place K F} (c : K) (φ : DualDom w)
    (x : w.adicCompletion) :
    (c • φ).toLM x = c • φ.toLM x := rfl

scoped instance (w : Place K F) : IsScalarTower K F (DualDom w) where
  smul_assoc c h φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (c • h) * x) = c • φ.toLM (algebraMap F _ h * x)
    rw [Algebra.smul_def, (algebraMap F w.adicCompletion).map_mul,
      ← IsScalarTower.algebraMap_apply K F w.adicCompletion,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, φ.toLM.map_smul]

end DualDom

section GenericFactor

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Nontrivial Ω[F⁄K]]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]

/-- The derivation factor: any derivation of `F` into an `F`-module is the
differential coefficient times the value at the uniformizer. -/
theorem derivation_apply_eq_diffCoeff_smul (w : Place K F) [w.DCoordGenerates]
    (δ : Derivation K F M) (g : F) :
    δ g = w.differentialCoeff (KaehlerDifferential.D K F g) • δ w.uniformizer := by
  have hL := Derivation.liftKaehlerDifferential_comp_D δ
  have hLπ : δ.liftKaehlerDifferential w.dCoord = δ w.uniformizer := hL w.uniformizer
  calc δ g = δ.liftKaehlerDifferential (KaehlerDifferential.D K F g) := (hL g).symm
    _ = δ.liftKaehlerDifferential
        (w.differentialCoeff (KaehlerDifferential.D K F g) • w.dCoord) := by
          rw [w.differentialCoeff_smul_dCoord]
    _ = w.differentialCoeff (KaehlerDifferential.D K F g) • δ w.uniformizer := by
          rw [map_smul, hLπ]

end GenericFactor

section TateResDerivation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem range_smul_le {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) : LinearMap.range (c • φ) ≤ LinearMap.range φ := by
  rintro y ⟨x, rfl⟩
  exact (LinearMap.range φ).smul_mem c (LinearMap.mem_range_self φ x)

theorem finDimRangeSMul {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    FiniteDimensional K (LinearMap.range (c • φ)) :=
  Submodule.finiteDimensional_of_le (range_smul_le c φ)

theorem finrankTrace_smul {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    haveI := finDimRangeSMul c φ
    finrankTrace (c • φ) = c • finrankTrace φ := by
  haveI := finDimRangeSMul c φ
  have hW : ∀ x ∈ LinearMap.range φ, (c • φ) x ∈ LinearMap.range φ := fun x _ =>
    range_smul_le c φ (LinearMap.mem_range_self _ x)
  rw [finrankTrace_eq_trace_on_superspace (c • φ) (LinearMap.range φ) (range_smul_le c φ) hW]
  unfold finrankTrace
  rw [← LinearMap.map_smul]
  exact congrArg (LinearMap.trace K _) (LinearMap.ext fun x => Subtype.ext rfl)

theorem tateCommRestrict_smul_snd {V : Type*} [AddCommGroup V] [Module K V]
    (pA φ ψ : V →ₗ[K] V) (c : K) :
    tateCommRestrict pA φ (c • ψ) = c • tateCommRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA φ (c • ψ) a : V) = (c • tateCommRestrict pA φ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply]
  unfold tateComm
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
    smul_sub, Submodule.coe_smul]

theorem tateCommRestrict_smul_fst {V : Type*} [AddCommGroup V] [Module K V]
    (pA φ ψ : V →ₗ[K] V) (c : K) :
    tateCommRestrict pA (c • φ) ψ = c • tateCommRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA (c • φ) ψ a : V) = (c • tateCommRestrict pA φ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply]
  unfold tateComm
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
    smul_sub, Submodule.coe_smul]

theorem tateRes_congr_snd (u : Place K F) {fh gh₁ gh₂ : u.adicCompletion} (heq : gh₁ = gh₂)
    [h₁ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh₁)))]
    [h₂ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh₂)))] :
    tateRes u fh gh₁ = tateRes u fh gh₂ := by
  subst heq; rfl

theorem tateRes_add_snd (u : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (f g h : u.adicCompletion) :
    haveI := hfin u f (g + h); haveI := hfin u f g; haveI := hfin u f h
    tateRes u f (g + h) = tateRes u f g + tateRes u f h := by
  haveI := hfin u f (g + h); haveI := hfin u f g; haveI := hfin u f h
  have heq : lmulK u (g + h) = lmulK u g + lmulK u h := map_add _ _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f) (lmulK u g + lmulK u h))) := by
    rw [← heq]; exact hfin u f (g + h)
  unfold tateRes
  have hct := tateCommTrace_add_snd (tateProj u) (lmulK u f) (lmulK u g) (lmulK u h)
  unfold tateCommTrace at hct ⊢
  rw [← hct]
  exact finrankTrace_congr (by rw [heq])

def tateResFstLM (w : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (gh : w.adicCompletion) : DualDom w where
  toFun f := haveI := hfin w f gh; tateRes w f gh
  map_add' f₁ f₂ := by
    haveI := hfin w f₁ gh; haveI := hfin w f₂ gh
    exact tateRes_add_fst w f₁ f₂ gh
  map_smul' c f := by
    haveI := hfin w f gh; haveI := hfin w (c • f) gh
    show tateRes w (c • f) gh = c • tateRes w f gh
    have heq : tateCommRestrict (tateProj w) (lmulK w (c • f)) (lmulK w gh)
        = c • tateCommRestrict (tateProj w) (lmulK w f) (lmulK w gh) := by
      rw [show lmulK w (c • f) = c • lmulK w f from map_smul _ _ _,
        tateCommRestrict_smul_fst]
    haveI := finDimRangeSMul c (tateCommRestrict (tateProj w) (lmulK w f) (lmulK w gh))
    unfold tateRes tateCommTrace
    rw [finrankTrace_congr heq, finrankTrace_smul]

@[scoped simp] theorem tateResFstLM_apply (w : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (gh f : w.adicCompletion) :
    (tateResFstLM w hfin gh).toLM f = haveI := hfin w f gh; tateRes w f gh := rfl

variable [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]

def tateResSndDer (w : Place K F) [w.DCoordGenerates] [w.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K F) : Derivation K F (DualDom w) :=
  Derivation.mk'
    { toFun := fun g => tateResFstLM w hfin (algebraMap F w.adicCompletion g)
      map_add' := fun g h => DualDom.ext fun f => by
        simp only [tateResFstLM_apply, DualDom.toLM_add, map_add]
        exact tateRes_add_snd w hfin f _ _
      map_smul' := fun c g => DualDom.ext fun f => by
        simp only [tateResFstLM_apply, RingHom.id_apply, DualDom.k_smul_apply]
        haveI := hfin w f (algebraMap F _ (c • g))
        haveI := hfin w f (algebraMap F _ g)
        show tateRes w f (algebraMap F _ (c • g)) = c • tateRes w f (algebraMap F _ g)
        have heq : tateCommRestrict (tateProj w) (lmulK w f)
              (lmulK w (algebraMap F _ (c • g)))
            = c • tateCommRestrict (tateProj w) (lmulK w f)
              (lmulK w (algebraMap F _ g)) := by
          rw [show lmulK w (algebraMap F _ (c • g)) = c • lmulK w (algebraMap F _ g) from by
              rw [Algebra.smul_def, (algebraMap F w.adicCompletion).map_mul,
                ← IsScalarTower.algebraMap_apply K F w.adicCompletion,
                Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
              exact map_smul _ _ _,
            tateCommRestrict_smul_snd]
        haveI := finDimRangeSMul c
          (tateCommRestrict (tateProj w) (lmulK w f) (lmulK w (algebraMap F _ g)))
        unfold tateRes tateCommTrace
        rw [finrankTrace_congr heq, finrankTrace_smul] }
    (fun g h => DualDom.ext fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, tateResFstLM_apply, DualDom.smul_apply,
        DualDom.toLM_add]
      haveI := hfin w f (algebraMap F _ (g * h))
      haveI := hfin w (algebraMap F _ g * f) (algebraMap F _ h)
      haveI := hfin w (algebraMap F _ h * f) (algebraMap F _ g)
      haveI := hfin w f (algebraMap F _ g * algebraMap F _ h)
      haveI := hfin w (f * algebraMap F _ g) (algebraMap F _ h)
      haveI := hfin w (f * algebraMap F _ h) (algebraMap F _ g)
      show tateRes w f (algebraMap F _ (g * h))
        = tateRes w (algebraMap F _ g * f) (algebraMap F _ h)
          + tateRes w (algebraMap F _ h * f) (algebraMap F _ g)
      rw [tateRes_congr_snd w ((algebraMap F w.adicCompletion).map_mul g h),
        tateRes_leibniz_snd w hfin f (algebraMap F _ g) (algebraMap F _ h),
        tateRes_congr_fst w (mul_comm f (algebraMap F _ g)),
        tateRes_congr_fst w (mul_comm f (algebraMap F _ h))])

@[scoped simp] theorem tateResSndDer_apply (w : Place K F) [w.DCoordGenerates] [w.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K F) (g : F) (f : w.adicCompletion) :
    ((tateResSndDer w hfin) g).toLM f
      = haveI := hfin w f (algebraMap F _ g); tateRes w f (algebraMap F _ g) := rfl

end TateResDerivation

section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]

/-- The derivation factor, from the `DualDom`-valued derivation `tateResSndDer`. -/
theorem kwTateRR2_derivationFactorSnd [∀ w : Place K F, w.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) :
    KwF4gRRTateDerivationFactorSnd K F hfinF := by
  intro w _ f g
  haveI := hfinF w f (algebraMap F _ g)
  haveI := hfinF w (f * algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)))
    (algebraMap F _ w.uniformizer)

  have hδ := derivation_apply_eq_diffCoeff_smul (M := DualDom w) w (tateResSndDer w hfinF) g
  haveI := hfinF w (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f)
    (algebraMap F _ w.uniformizer)
  calc tateRes w f (algebraMap F _ g)
      = ((tateResSndDer w hfinF) g).toLM f := (tateResSndDer_apply w hfinF g f).symm
    _ = (w.differentialCoeff (KaehlerDifferential.D K F g)
          • (tateResSndDer w hfinF) w.uniformizer).toLM f := by rw [hδ]
    _ = ((tateResSndDer w hfinF) w.uniformizer).toLM
          (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f) :=
        DualDom.smul_apply _ _ _
    _ = tateRes w (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f)
          (algebraMap F _ w.uniformizer) := tateResSndDer_apply w hfinF w.uniformizer _
    _ = tateRes w (f * algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)))
          (algebraMap F _ w.uniformizer) :=
        tateRes_congr_fst w (mul_comm _ f)

end Headline

end ModularCurve.KwF4gRRTate

/-- The Tate chain rule, at the pin wrapper's binders. -/
theorem AlgebraicCurve.tateChainRule
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule K F E hfinF :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_chainRule_of_derivationFactor hfinF
    (fun {_ _} => ModularCurve.KwF4gRRTate.kwTateRR2_derivationFactorSnd hfinF)
