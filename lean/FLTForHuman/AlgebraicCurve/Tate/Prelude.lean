/-
Tate shared prelude — the row-3.3 declarations that set 3.3b (`Tate/ChainRule.lean`)
and set 3.3d (`Tate/TraceCompat.lean`) had each re-proved.  They are byte-identical
in statement in the two modules (the refactor round's detector found all 25 shared
`ModularCurve.KwF4gRRTate.*` declarations statement-identical), so this file is the
single home; both consumers import it and the duplicate copies are deleted.

It imports `Defs/TateResidueCurrency.lean` (the shared row-3.3 API) and
`Tate/CommFinite.lean` (set 3.3a's finiteness theory), because the pole-window
discharge `kwF4gRRTate_poleWindowFinite` / `lmul_adicIntegers_subset_poleWindow` /
`kwF4gRRTate_poleWindowImageFinite` uses `kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite`,
`poleWindowKSubmod` and `kwF4gRRTate_clearPole` from there; everything else is
mathlib through the API.

The declaration text is the `Tate/ChainRule.lean` copy verbatim (the two copies are
statement-identical; the checker verifies each against the pin's prelude in
`P2M/Sol/S_AlgebraicCurve_tateChainRule.lean` / `..._tateTraceCompat_...`).
-/
import FLTForHuman.AlgebraicCurve.Defs.TateResidueCurrency
import FLTForHuman.AlgebraicCurve.Tate.CommFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open LinearMap Submodule
open AlgebraicCurve AlgebraicCurve.Place
open ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve.KwF4gRRTate

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- The projection `tateProj u` is idempotent. -/
theorem tateProj_idem : tateProj u ∘ₗ tateProj u = tateProj u := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact tateProj_of_mem u (tateProj_mem_integers u x)

end TateProj

section FinrankTraceCyclicity

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The first factor of a cyclic compositum maps into the range of the other order. -/
theorem range_comp_map_left (f : M →ₗ[K] N) (g : N →ₗ[K] M) :
    ∀ x ∈ LinearMap.range (g ∘ₗ f), f x ∈ LinearMap.range (f ∘ₗ g) := by
  rintro x ⟨y, rfl⟩
  exact ⟨f y, rfl⟩

/-- `finrankTrace` is invariant under cyclic permutation of a compositum. -/
theorem finrankTrace_comp_comm (f : M →ₗ[K] N) (g : N →ₗ[K] M)
    [FiniteDimensional K (LinearMap.range (g ∘ₗ f))]
    [FiniteDimensional K (LinearMap.range (f ∘ₗ g))] :
    finrankTrace (g ∘ₗ f) = finrankTrace (f ∘ₗ g) := by
  set W := LinearMap.range (g ∘ₗ f)
  set W' := LinearMap.range (f ∘ₗ g)

  let fR : W →ₗ[K] W' := f.restrict (range_comp_map_left f g)
  let gR : W' →ₗ[K] W := g.restrict (range_comp_map_left g f)

  have hgf : (g ∘ₗ f).restrict (fun x _ => LinearMap.mem_range_self _ x) = gR ∘ₗ fR := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  have hfg : (f ∘ₗ g).restrict (fun x _ => LinearMap.mem_range_self _ x) = fR ∘ₗ gR := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  unfold finrankTrace
  rw [hgf, hfg, LinearMap.trace_comp_comm']

end FinrankTraceCyclicity

section TraceOnSuperspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `finrankTrace` of `φ` is the ambient trace of `φ` restricted to any invariant
superspace of its range. -/
theorem finrankTrace_eq_trace_on_superspace
    (φ : V →ₗ[K] V) (W : Submodule K V) [FiniteDimensional K W]
    (hrange : LinearMap.range φ ≤ W) (hW : ∀ x ∈ W, φ x ∈ W) :
    haveI : FiniteDimensional K (LinearMap.range φ) :=
      Submodule.finiteDimensional_of_le hrange
    finrankTrace φ = LinearMap.trace K W (φ.restrict hW) := by
  haveI : FiniteDimensional K (LinearMap.range φ) := Submodule.finiteDimensional_of_le hrange

  let i : LinearMap.range φ →ₗ[K] W := Submodule.inclusion hrange

  let π : W →ₗ[K] LinearMap.range φ :=
    { toFun := fun w => ⟨φ (w : V), LinearMap.mem_range_self φ (w : V)⟩
      map_add' := fun w₁ w₂ => by simp [Subtype.ext_iff]
      map_smul' := fun c w => by simp [Subtype.ext_iff] }

  have hip : i ∘ₗ π = φ.restrict hW := by
    apply LinearMap.ext; intro w; apply Subtype.ext; rfl

  have hpi : π ∘ₗ i = φ.restrict (fun x _ => LinearMap.mem_range_self φ x) := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  unfold finrankTrace
  rw [← hpi, ← hip, LinearMap.trace_comp_comm']

end TraceOnSuperspace

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `finrankTrace φ - finrankTrace ψ` is the trace of `φ - ψ` on the join of the two
ranges. -/
theorem finrankTrace_sub_eq
    (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    haveI : FiniteDimensional K
        ((LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V) : Type _) :=
      Submodule.finiteDimensional_sup _ _
    finrankTrace φ - finrankTrace ψ
      = LinearMap.trace K (LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V)
          ((φ - ψ).restrict
            (p := (LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V))
            (fun x _ => sub_mem
              (Submodule.mem_sup_left (LinearMap.mem_range_self φ x))
              (Submodule.mem_sup_right (LinearMap.mem_range_self ψ x)))) := by
  set W' : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ with hW'
  haveI : FiniteDimensional K W' := Submodule.finiteDimensional_sup _ _
  have hφW : ∀ x ∈ W', φ x ∈ W' := fun x _ =>
    Submodule.mem_sup_left (LinearMap.mem_range_self φ x)
  have hψW : ∀ x ∈ W', ψ x ∈ W' := fun x _ =>
    Submodule.mem_sup_right (LinearMap.mem_range_self ψ x)
  rw [finrankTrace_eq_trace_on_superspace φ W' le_sup_left hφW,
    finrankTrace_eq_trace_on_superspace ψ W' le_sup_right hψW,
    ← map_sub]

  refine congrArg (LinearMap.trace K W') (LinearMap.ext fun x => Subtype.ext ?_)
  rfl

end Additivity

section TermRangeFinite

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

/-- The image of the completion integers under multiplication by a fixed completion
element, modulo the completion integers, is finite-dimensional over `K` (the pin's
`KwF4gRRTatePoleWindowImageFinite`). -/
def KwF4gRRTatePoleWindowImageFinite : Prop :=
  ∀ (fh : u.adicCompletion),
    FiniteDimensional K (Submodule.map (adicIntegersKSubmod u).mkQ
      (Submodule.map (lmulK u fh) (adicIntegersKSubmod u)))

end TermRangeFinite

section Composite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The pole-window finiteness, discharged through the DVR quotient-power and
cotangent finiteness of set 3.3a. -/
theorem kwF4gRRTate_poleWindowFinite : KwF4gRRTatePoleWindowFinite K L :=
  kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
      kwF4gRRTate_DVRCotangentKFinite)

end Composite

section Subset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- If `πh^M * fh` is integral then `lmulK u fh` maps the completion integers into the
`M`-th pole window. -/
theorem lmul_adicIntegers_subset_poleWindow (fh : u.adicCompletion)
    (πh : u.adicCompletionIntegers) (M : ℕ)
    (hfhM : (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers) :
    Submodule.map (lmulK u fh) (adicIntegersKSubmod u) ≤ poleWindowKSubmod u πh M := by
  rintro x ⟨a, ha, rfl⟩

  rw [mem_poleWindowKSubmod_iff]
  show (πh : u.adicCompletion)^M * (lmulK u fh) a ∈ u.adicCompletionIntegers
  have : (lmulK u fh) a = fh * a := rfl
  rw [this, ← mul_assoc]
  exact mul_mem hfhM (show a ∈ u.adicCompletionIntegers from ha)

end Subset

section Discharge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

/-- The pin's `KwF4gRRTatePoleWindowImageFinite`, discharged from the pole-window
finiteness and the clearing of poles. -/
theorem kwF4gRRTate_poleWindowImageFinite :
    KwF4gRRTatePoleWindowImageFinite u := by
  intro fh
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hfhM⟩ := kwF4gRRTate_clearPole u πh hπh fh

  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  have hsub : Submodule.map A.mkQ (Submodule.map (lmulK u fh) A)
      ≤ Submodule.map A.mkQ P :=
    Submodule.map_mono (lmul_adicIntegers_subset_poleWindow u fh πh M hfhM)

  suffices hPim : FiniteDimensional K (Submodule.map A.mkQ P : Submodule K _) by
    exact Submodule.finiteDimensional_of_le hsub

  haveI : FiniteDimensional K (P ⧸ (A.comap P.subtype)) :=
    kwF4gRRTate_poleWindowFinite (K := K) (L := L) u πh hπh M
  let r : P →ₗ[K] (u.adicCompletion ⧸ A) := A.mkQ ∘ₗ P.subtype
  have hrange : LinearMap.range r = Submodule.map A.mkQ P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker r = A.comap P.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : (P ⧸ (A.comap P.subtype)) ≃ₗ[K] LinearMap.range r := hker ▸ r.quotKerEquivRange
  rw [← hrange]
  exact e.finiteDimensional

end Discharge

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `finrankTrace` only depends on the endomorphism. -/
theorem finrankTrace_congr {φ ψ : V →ₗ[K] V}
    [hφ : FiniteDimensional K (LinearMap.range φ)]
    [hψ : FiniteDimensional K (LinearMap.range ψ)]
    (h : φ = ψ) : finrankTrace φ = finrankTrace ψ := by
  subst h; rfl

/-- The range of a difference lies in the join of the ranges. -/
theorem range_sub_le (φ ψ : V →ₗ[K] V) :
    LinearMap.range (φ - ψ) ≤ LinearMap.range φ ⊔ LinearMap.range ψ := by
  rintro x ⟨y, rfl⟩
  exact sub_mem (Submodule.mem_sup_left (mem_range_self φ y))
    (Submodule.mem_sup_right (mem_range_self ψ y))

scoped instance instFinDimRangeSub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ - ψ)) :=
  haveI : FiniteDimensional K
      ((LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V) : Type _) :=
    Submodule.finiteDimensional_sup _ _
  Submodule.finiteDimensional_of_le (range_sub_le φ ψ)

/-- `finrankTrace` is additive. -/
theorem finrankTrace_sub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace φ - finrankTrace ψ = finrankTrace (φ - ψ) := by
  set W' : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ
  haveI : FiniteDimensional K W' := Submodule.finiteDimensional_sup _ _
  have hφψW : ∀ x ∈ W', (φ - ψ) x ∈ W' := fun x _ =>
    sub_mem (Submodule.mem_sup_left (mem_range_self φ x))
      (Submodule.mem_sup_right (mem_range_self ψ x))
  rw [finrankTrace_sub_eq φ ψ,
    finrankTrace_eq_trace_on_superspace (φ - ψ) W' (range_sub_le φ ψ) hφψW]

end Additivity

section TermMaps

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- The `K`-linear "multiplication by `c`" map on the range of `tateProj u`, followed
by the quotient map. -/
def alphaMap (c : u.adicCompletion) :
    LinearMap.range (tateProj u) →ₗ[K] (u.adicCompletion ⧸ LinearMap.range (tateProj u)) :=
  (LinearMap.range (tateProj u)).mkQ ∘ₗ lmulK u c ∘ₗ (LinearMap.range (tateProj u)).subtype

variable [u.FiniteResidue]

/-- The range of `alphaMap u c` is finite-dimensional. -/
theorem finiteDimensional_range_alphaMap (c : u.adicCompletion) :
    FiniteDimensional K (LinearMap.range (alphaMap u c)) := by

  haveI hF21 := kwF4gRRTate_poleWindowImageFinite u c
  set Q1 := u.adicCompletion ⧸ LinearMap.range (tateProj u)
  set Q2 := u.adicCompletion ⧸ adicIntegersKSubmod u
  let eQ : Q1 ≃ₗ[K] Q2 := Submodule.quotEquivOfEq _ _ (range_tateProj u)

  have hmap : (LinearMap.range (alphaMap u c)).map (eQ : Q1 →ₗ[K] Q2)
      = Submodule.map (adicIntegersKSubmod u).mkQ
          (Submodule.map (lmulK u c) (adicIntegersKSubmod u)) := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := hy
      refine ⟨c * (a : u.adicCompletion), ⟨(a : u.adicCompletion), ?_, rfl⟩, ?_⟩
      · exact (range_tateProj u) ▸ a.2
      · rfl
    · rintro x ⟨y, ⟨av, hav, rfl⟩, rfl⟩
      refine ⟨alphaMap u c ⟨av, (range_tateProj u).symm ▸ hav⟩, ⟨_, rfl⟩, ?_⟩
      rfl
  have : FiniteDimensional K
      ((LinearMap.range (alphaMap u c)).map (eQ : Q1 →ₗ[K] Q2)) := by
    rw [hmap]; exact hF21
  exact (Submodule.equivMapOfInjective (eQ : Q1 →ₗ[K] Q2) eQ.injective
    (LinearMap.range (alphaMap u c))).symm.finiteDimensional

end TermMaps

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

scoped instance instFinDimRangeNeg (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    FiniteDimensional K (LinearMap.range (-φ)) := by
  have h : LinearMap.range (-φ) = LinearMap.range φ := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩; exact ⟨-y, by simp⟩
    · rintro x ⟨y, rfl⟩; exact ⟨-y, by simp⟩
  rw [h]; infer_instance

scoped instance instFinDimRangeZero : FiniteDimensional K (LinearMap.range (0 : V →ₗ[K] V)) := by
  rw [LinearMap.range_zero]; infer_instance

theorem finrankTrace_zero : finrankTrace (0 : V →ₗ[K] V) = 0 := by
  unfold finrankTrace
  have hrest : (0 : V →ₗ[K] V).restrict
      (p := LinearMap.range (0 : V →ₗ[K] V))
      (fun x _ => LinearMap.mem_range_self _ x) = 0 := by
    apply LinearMap.ext; intro; apply Subtype.ext; rfl
  rw [hrest, _root_.map_zero]

theorem finrankTrace_neg (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    finrankTrace (-φ) = -finrankTrace φ := by
  have hsub := finrankTrace_sub (0 : V →ₗ[K] V) φ
  rw [finrankTrace_zero, zero_sub] at hsub
  calc finrankTrace (-φ) = finrankTrace ((0 : V →ₗ[K] V) - φ) :=
        finrankTrace_congr (zero_sub φ).symm
    _ = -finrankTrace φ := hsub.symm

scoped instance instFinDimRangeAdd (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ + ψ)) := by
  rw [show φ + ψ = φ - (-ψ) from (sub_neg_eq_add φ ψ).symm]
  exact instFinDimRangeSub φ (-ψ)

theorem finrankTrace_add (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace (φ + ψ) = finrankTrace φ + finrankTrace ψ := by
  have h := finrankTrace_sub φ (-ψ)
  rw [finrankTrace_neg, sub_neg_eq_add] at h
  calc finrankTrace (φ + ψ) = finrankTrace (φ - (-ψ)) :=
        finrankTrace_congr (sub_neg_eq_add φ ψ).symm
    _ = finrankTrace φ + finrankTrace ψ := h.symm

end Additivity

section TateCommAddFst

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V) :
    tateComm pA (φ₁ + φ₂) ψ = tateComm pA φ₁ ψ + tateComm pA φ₂ ψ := by
  unfold tateComm
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
  abel

theorem tateCommRestrict_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V) :
    tateCommRestrict pA (φ₁ + φ₂) ψ
      = tateCommRestrict pA φ₁ ψ + tateCommRestrict pA φ₂ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA (φ₁ + φ₂) ψ a : V)
    = (tateCommRestrict pA φ₁ ψ a : V) + (tateCommRestrict pA φ₂ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply, tateCommRestrict_apply]
  exact congrFun (congrArg DFunLike.coe (tateComm_add_fst pA φ₁ φ₂ ψ)) (a : V)

theorem tateCommTrace_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ₁ ψ))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ₂ ψ))] :
    haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA (φ₁ + φ₂) ψ)) := by
      rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
    tateCommTrace pA (φ₁ + φ₂) ψ = tateCommTrace pA φ₁ ψ + tateCommTrace pA φ₂ ψ := by
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA (φ₁ + φ₂) ψ)) := by
    rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  unfold tateCommTrace
  rw [← finrankTrace_add]
  exact finrankTrace_congr (tateCommRestrict_add_fst pA φ₁ φ₂ ψ)

end TateCommAddFst

section TateResAddFst

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem tateRes_add_fst (fh₁ fh₂ gh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁) (lmulK u gh)))]
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₂) (lmulK u gh)))] :
    haveI : FiniteDimensional K (LinearMap.range
        (tateCommRestrict (tateProj u) (lmulK u (fh₁ + fh₂)) (lmulK u gh))) := by
      have heq : lmulK u (fh₁ + fh₂) = lmulK u fh₁ + lmulK u fh₂ := map_add _ _ _
      rw [heq, tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
    tateRes u (fh₁ + fh₂) gh = tateRes u fh₁ gh + tateRes u fh₂ gh := by
  have heq : lmulK u (fh₁ + fh₂) = lmulK u fh₁ + lmulK u fh₂ := map_add _ _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u (fh₁ + fh₂)) (lmulK u gh))) := by
    rw [heq, tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁ + lmulK u fh₂) (lmulK u gh))) := by
    rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  unfold tateRes
  have hct := tateCommTrace_add_fst (tateProj u) (lmulK u fh₁) (lmulK u fh₂) (lmulK u gh)
  unfold tateCommTrace at hct ⊢
  rw [← hct]
  exact finrankTrace_congr (by rw [heq])

end TateResAddFst

