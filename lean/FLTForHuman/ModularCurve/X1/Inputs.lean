/-
  The capstone of the X₁ Hecke/diamond effort:
  `ModularCurve.heckeDiamondInputsAll`.

  For every prime `ℓ`, the X₁ Hecke inputs `HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ`
  hold; and for every `d` coprime to `M` there is a diamond automorphism of
  `x1FunctionField M` together with its base change to `x1FunctionFieldBar M`.

  This is the pin's assembly
  `P2M/Sol/S_ModularCurve_heckeDiamondInputsAll.lean` (pinned `aa2d8b3`). Its
  `X1HDIGeneric` helpers are reused from their ported homes rather than restated:
  `AlgebraicCurve.isAlgebraic_adjoin_of_transcendental`
  (`AlgebraicCurve/Place/DegreeOne.lean:54`) replaces the pin's
  `isAlgebraic_algebraAdjoin`/`isAlgebraic_adjoin_of_transcendental`, and
  `AlgebraicCurve.separableAlong_of_charZero`
  (`AlgebraicCurve/WeilExchange/Transport.lean:268`) replaces the pin's local copy;
  the two `Along` facts come from the same ported module. `finiteAlong_of_transcendental`
  and `isIntegral_of_finiteAlong` are new and stay `private`, as does the whole
  `X1HDIGeneric`/`X1HDIInputs` prelude, so the module's only public surface is the
  headline. Written by the manager as the effort's final wire test
  ([TOPIC-x1-hecke-diamond-inputs.md](../../topics/hecke/TOPIC-x1-hecke-diamond-inputs.md)
  §5 SET-X1-C).

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeDiamondInputsAll.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDiamondInputsAll.lean
-/
import FLTForHuman.ModularCurve.X1.HeckeModule
import FLTForHuman.ModularCurve.X1.QExpandStretch
import FLTForHuman.ModularCurve.X1.DiamondAut
import FLTForHuman.ModularCurve.X1.BaseChangeCover
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.AlgebraicCurve.Place.DegreeOne
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls are load-bearing; keep them literal.
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve

open AlgebraicCurve CongruenceSubgroup IntermediateField

/-! ## The generic exchange/along helpers (pin `X1HDIGeneric`) -/

section Along

variable {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']

/-- Adjoining a different transcendental `t` keeps `F` finite over the simple
extension. The proof is the port's own
`AlgebraicCurve.SeparatingTranscendentalOfPerfectField.finiteDimensional_adjoin_of_transcendental`
(`AlgebraicCurve/IsCurveOver/PerfectField.lean:71`), whose `adjoin`/`finrank`
argument already matches the pin's; only its hypothesis is spelled as the pin's
instance. -/
private theorem finiteDimensional_adjoin_of_transcendental {x : F} (_hx : Transcendental L x)
    [FiniteDimensional L⟮x⟯ F] {t : F} (ht : Transcendental L t) :
    FiniteDimensional L⟮t⟯ F := by
  classical
  have halg : Algebra.IsAlgebraic L⟮t⟯ F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental (K := L) x ht
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite L⟮x⟯ F)
  set E : IntermediateField L⟮t⟯ F := IntermediateField.adjoin L⟮t⟯ (insert x (↑s : Set F)) with hE
  have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hrange : ∀ r : L⟮x⟯, (r : F) ∈ E := by
    intro r
    have hle : L⟮x⟯ ≤ E.restrictScalars L :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_restrictScalars L).mpr hxE)
    exact (IntermediateField.mem_restrictScalars L).mp (hle r.2)
  have hmem : ∀ y : F, y ∈ E := by
    intro y
    have hy : y ∈ Submodule.span L⟮x⟯ (↑s : Set F) := by rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_)
      (fun r z _ hz => ?_) hy
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    · exact zero_mem E
    · exact add_mem hz hw
    · rw [Algebra.smul_def]
      exact mul_mem (hrange r) hz
  have htop : E = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hmem y
  haveI : Finite ↥(insert x (↑s : Set F)) :=
    Set.Finite.to_subtype ((s.finite_toSet).insert x)
  have hfdE : FiniteDimensional L⟮t⟯ ↥E := by
    rw [hE]
    exact IntermediateField.finiteDimensional_adjoin
      (fun z _ => (halg.isAlgebraic z).isIntegral)
  rw [htop] at hfdE
  haveI := hfdE
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := L⟮t⟯) (E := F)).toLinearEquiv

/-- **`FiniteAlong` follows from one transcendental presentation.** If `F` is
finite over `L⟮x₀⟯` and `F'` is finite over `L⟮x₁⟯`, then any `L`-morphism
`φ : F →ₐ[L] F'` is finite along. Verbatim from the pin's `X1HDIGeneric`. -/
private theorem finiteAlong_of_transcendental (φ : F →ₐ[L] F') {x₀ : F}
    (hx₀ : Transcendental L x₀) {x₁ : F'} (hx₁ : Transcendental L x₁)
    [FiniteDimensional L⟮x₁⟯ F'] : FiniteAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ

  have hy₀ : Transcendental L (φ x₀) := by
    have h := (transcendental_algebraMap_iff (R := L) (S := F) (A := F')
      (φ.toRingHom.injective)).mpr hx₀
    exact h
  haveI hfin : FiniteDimensional L⟮φ x₀⟯ F' := finiteDimensional_adjoin_of_transcendental hx₁ hy₀

  set E₀ : IntermediateField L F := L⟮x₀⟯ with hE₀
  have hmap : E₀.map φ = L⟮φ x₀⟯ := by
    rw [hE₀, IntermediateField.adjoin_map, Set.image_singleton]
  let e : E₀ ≃ₐ[L] L⟮φ x₀⟯ := (E₀.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : E₀, ((e w : L⟮φ x₀⟯) : F') = φ (w : F) := by
    intro w
    rfl
  letI : Algebra E₀ F' := ((algebraMap F F').comp (algebraMap E₀ F)).toAlgebra
  haveI : IsScalarTower E₀ F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E₀ F' := by
    refine Module.Finite.of_equiv_equiv (A₁ := L⟮φ x₀⟯) (B₁ := F') (A₂ := E₀) (B₂ := F')
      e.symm.toRingEquiv (RingEquiv.refl F') ?_
    refine RingHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.refl_apply]
    rw [show e.symm.toRingEquiv (e w) = w from e.symm_apply_apply w]
    show φ (w : F) = ((e w : L⟮φ x₀⟯) : F')
    rw [he]
  show Module.Finite F F'
  exact Module.Finite.of_restrictScalars_finite E₀ F F'

/-- **A finite map's ring hom is integral.** Verbatim from the pin's `X1HDIGeneric`. -/
private theorem isIntegral_of_finiteAlong (φ : F →ₐ[L] F') (h : FiniteAlong L φ) :
    φ.toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := h
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  exact fun x => Algebra.IsIntegral.isIntegral x

end Along

/-! ## The X₁ Hecke inputs (pin `X1HDIInputs`) -/

section Groups

variable (M ℓ : ℕ)

private theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp

private theorem T_mem_Gamma1_inf_Gamma0 : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (M * ℓ) := by
  exact ⟨T_mem_Gamma1 M, by simp [Gamma0_mem]⟩

private instance finiteIndex_Gamma1_inf_Gamma0 [NeZero M] [NeZero ℓ] :
    (Gamma1 M ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private theorem cocycle [NeZero ℓ] : ∀ γ ∈ Gamma1 M ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ Gamma1 M,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma1_mem] at hγ1 ⊢
    obtain ⟨h00, h11, -⟩ := hγ1
    refine ⟨h00, h11, ?_⟩
    show (((M : ℤ) * c' : ℤ) : ZMod M) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((M : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

end Groups

section Inputs

variable (L : Type*) [Field L] [Algebra ℚ L] (M ℓ : ℕ) [NeZero M] [NeZero ℓ]

private theorem charZero_of_algebraRat : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ L).injective

private theorem heckeBetaOneDefined : HeckeBetaOneDefined M ℓ := by
  intro y hy
  have hsub := qExpand_image_intFormRatiosC_subset ℚ (T_mem_Gamma1 M) ℓ (cocycle M ℓ)

  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M)) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 (M * ℓ))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

private theorem exists_transcendental_bot :
    ∃ x₀ : laurentBaseChange L (x1FunctionField M), Transcendental L x₀ := by
  obtain ⟨x, hx, -⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (Gamma1 M)
      (T_mem_Gamma1 M)
  exact ⟨x, hx⟩

private theorem exists_transcendental_finiteDimensional_top :
    ∃ x₁ : laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)), Transcendental L x₁ ∧
      FiniteDimensional L⟮x₁⟯ (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (Gamma1 M ⊓ Gamma0 (M * ℓ)) (T_mem_Gamma1_inf_Gamma0 M ℓ)

private theorem finiteAlong_alpha : FiniteAlong L (heckeAlphaOneBar L M ℓ) := by
  obtain ⟨x₀, hx₀⟩ := exists_transcendental_bot L M
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_top L M ℓ
  haveI := hfin
  exact finiteAlong_of_transcendental _ hx₀ hx₁

private theorem finiteAlong_beta : FiniteAlong L (heckeBetaOneBar L M ℓ) := by
  obtain ⟨x₀, hx₀⟩ := exists_transcendental_bot L M
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_top L M ℓ
  haveI := hfin
  exact finiteAlong_of_transcendental _ hx₀ hx₁

private theorem alphaIntegral : HeckeAlphaOneBarIntegral L M ℓ :=
  isIntegral_of_finiteAlong _ (finiteAlong_alpha L M ℓ)

private theorem betaIntegral : HeckeBetaOneBarIntegral L M ℓ :=
  isIntegral_of_finiteAlong _ (finiteAlong_beta L M ℓ)

private theorem hasPrincipalDivisors_top :
    HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) := by
  haveI : CharZero L := charZero_of_algebraRat L
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_top L M ℓ
  haveI := hfin
  exact AlgebraicCurve.hasPrincipalDivisors_of_transcendental L x₁ hx₁

private instance charZero_bot : CharZero (laurentBaseChange L (x1FunctionField M)) := by
  haveI : CharZero L := charZero_of_algebraRat L
  exact charZero_of_injective_algebraMap (algebraMap L _).injective

private theorem heckeInputsOneAlong : HeckeInputsOneAlong L M ℓ := by
  haveI := hasPrincipalDivisors_top L M ℓ
  have hα := alphaIntegral L M ℓ
  have hβ := betaIntegral L M ℓ
  have hfinα := finiteAlong_alpha L M ℓ
  have hfinβ := finiteAlong_beta L M ℓ
  refine heckeInputsOneAlong_intro (heckeBetaOneDefined M ℓ) hα hβ ?_ hfinα ?_
  · exact AlgebraicCurve.fundamentalIdentityAlong _ hβ hfinβ
      (AlgebraicCurve.separableAlong_of_charZero _ hβ)
  · exact AlgebraicCurve.normFormulaAlong _ hfinα
      (AlgebraicCurve.separableAlong_of_charZero _ hα)

end Inputs

section Diamond

variable (M : ℕ) [NeZero M]

private theorem diamond_inputs (d : ℕ) (hd : Nat.Coprime d M) :
    (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) ∧
      ∃ σ' : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
        IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) σ' := by
  refine ⟨ModularCurve.exists_isDiamondAut M hd, ?_⟩
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (x1FunctionField M) (diamondAut M d).toRingEquiv
  exact ⟨τ, fun y => hτ y⟩

end Diamond

/-- **The X₁ Hecke and diamond inputs all hold.** Verbatim from
`Theorems/Thm_ModularCurve_heckeDiamondInputsAll.lean`. The Hecke half is the
pin's `X1HDIInputs.heckeInputsOneAlong` assembled from the SET-X1-A definitions,
the stretch lemma and the two `JOneES` headlines; the diamond half composes
`exists_isDiamondAut` with `exists_algEquiv_laurentBaseChange_cover`. -/
theorem heckeDiamondInputsAll (M : ℕ) [NeZero M] :
    HeckeDiamondInputsAll M := by
  refine ⟨fun ℓ => ?_, fun d hd => diamond_inputs M d hd⟩
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  exact heckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ

end ModularCurve

end
