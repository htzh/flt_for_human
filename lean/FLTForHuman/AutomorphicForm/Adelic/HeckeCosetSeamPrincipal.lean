/-
  The Hecke coset system at a *principal* level, at a finite place.

  The `_principalLevel` sibling of
  `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen`
  (`AutomorphicForm/Adelic/HeckeCosetSeam.lean`): the same explicit `q_v + 1`-coset system, but
  for the level group `principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F` rather than
  `levelOne … ⊓ …`. Since `principalLevel = levelOne ⊓ levelOne.map (conj weyl)`, the extra work
  is the Weyl-conjugacy bookkeeping: the local component of a Weyl-conjugate is the Weyl
  conjugate of the local component (`finComponent_glFin_conj_weyl`), so the membership criterion
  `components_of_mem_prinU`/`mem_prinU_of_components` carries a second, conjugated condition. The
  docked Hecke generator then lies in the principal level outright
  (`heckeGen_inv_mul_docked_mem_U`: it is `(heckeGenAt t)⁻¹ * heckeGenAt t`), which is why this
  sibling is much shorter than its 908 pin lines suggest.

  Transcribed from
  `P2M/Sol/S_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel.lean`
  (pinned `aa2d8b3`, 908 lines, 56 declarations); the statement is the `Theorems/` wrapper
  verbatim. **The 807-line engine it re-proves is imported, not re-proved**: it is the public
  `Aux4SevenTN` chapter of `HeckeCosetSeam.lean`, and this module keeps only the declarations that
  actually differ — the `prinU` abbreviation, the five Weyl-conjugacy lemmas, and the
  `prinU`-flavoured versions of the docked statement, its coset-system proof and the headline.
  In particular the sibling's `l1U`-spelled re-statements of `mem_generalU_of_components` /
  `components_of_mem_generalU` are **not** repeated: the parent module's versions are stated for
  `(productionPinsGeneral F).U N`, which is *by definition*
  `levelOne ⊓ finiteAdelicGL2Subgroup F` (`productionPinsGeneralOf_U`), so the two spellings are
  the same group. The sibling's copies of `glArch_heckeGenAt`, `adicToAdelic_diagPi`,
  `isHeckeCosetSystem_congr_gen`, `doubleCoset_eq_of_inv_mul_mem`,
  `isHeckeCosetSystem_comp_equiv` and the four glue lemmas above `solution` are byte-identical to
  the parent's and are imported for the same reason.

  The pin's chapter namespace `Aux4SevenTN` belongs to the parent module, so this file's variants
  live in `Aux4SevenTNPrincipal` — the checker matches on the last name and the statement hash,
  not on the namespace. The pin's `private` declarations are public here, as in the parent.

  spec-pin: Theorems/Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel.lean
  spec-pin: P2M/Sol/S_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.HeckeCosetSeam
import FLTForHuman.NumberTheory.AdelicLevel.PrincipalLevel

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally (as in the pin's S_ files).
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel LocalGL2 HeckeIntegralSeam AdelicDock
open Aux4SevenTN

namespace Aux4SevenTNPrincipal

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

noncomputable abbrev prinU (N : Ideal (𝓞 F)) : Subgroup (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
  principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

theorem finComponent_glFin_weyl (w : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (weyl (𝓞 F) F))
      = weylInt (w.adicCompletionIntegers F) (w.adicCompletion F) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_weylInt, finComponent_apply, glFin_apply]
  show ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w = _
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem finComponent_glFin_conj_weyl (h : GL (Fin 2) (AdeleRing (𝓞 F) F)) (w : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F))
      = (weylInt (w.adicCompletionIntegers F) (w.adicCompletion F))⁻¹
          * finComponent (𝓞 F) F w (glFin (𝓞 F) F h)
          * weylInt (w.adicCompletionIntegers F) (w.adicCompletion F) := by
  simp only [map_mul, map_inv, finComponent_glFin_weyl]

theorem glArch_conj_weyl {h : GL (Fin 2) (AdeleRing (𝓞 F) F)} (harch : glArch (𝓞 F) F h = 1) :
    glArch (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F) = 1 := by
  rw [map_mul, map_mul, map_inv, harch, mul_one, inv_mul_cancel]

theorem mem_prinU_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N)
    (hfin' : ∀ w : HeightOneSpectrum (𝓞 F),
      (weylInt (w.adicCompletionIntegers F) (w.adicCompletion F))⁻¹
          * finComponent (𝓞 F) F w (glFin (𝓞 F) F h)
          * weylInt (w.adicCompletionIntegers F) (w.adicCompletion F) ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ prinU F N := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_principalLevel_iff]
    refine ⟨(Subgroup.mem_inf.mp (mem_generalU_of_components F harch hfin)).1, ?_⟩
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hc := mem_generalU_of_components F (h := (weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F)
      (glArch_conj_weyl F harch) (fun w => by rw [finComponent_glFin_conj_weyl]; exact hfin' w)
    exact (Subgroup.mem_inf.mp hc).1
  · show _ ∈ finiteAdelicGL2Subgroup F
    rw [finiteAdelicGL2Subgroup, MonoidHom.mem_ker]
    exact harch

theorem components_of_mem_prinU {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hh : h ∈ prinU F N) :
    glArch (𝓞 F) F h = 1 ∧
      (∀ w : HeightOneSpectrum (𝓞 F),
        finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N) ∧
      ∀ w : HeightOneSpectrum (𝓞 F),
        (weylInt (w.adicCompletionIntegers F) (w.adicCompletion F))⁻¹
            * finComponent (𝓞 F) F w (glFin (𝓞 F) F h)
            * weylInt (w.adicCompletionIntegers F) (w.adicCompletion F) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  rw [mem_principalLevel_iff] at h1
  obtain ⟨hL, hC⟩ := h1
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hC
  have hA := components_of_mem_generalU F (Subgroup.mem_inf.mpr ⟨hL, h2⟩)
  have harch' : (weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F ∈ finiteAdelicGL2Subgroup F := by
    rw [finiteAdelicGL2Subgroup, MonoidHom.mem_ker]
    exact glArch_conj_weyl F hA.1
  have hB := components_of_mem_generalU F (Subgroup.mem_inf.mpr ⟨hC, harch'⟩)
  exact ⟨hA.1, hA.2, fun w => by have := hB.2 w; rwa [finComponent_glFin_conj_weyl] at this⟩

theorem adicToAdelic_mem_generalU {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    adicToAdelic F v k ∈ prinU F N := by
  refine mem_prinU_of_components F (glArch_adicToAdelic F v k) (fun w => ?_) (fun w => ?_)
  · by_cases hw : w = v
    · subst hw
      rw [finComponent_glFin_adicToAdelic]
      exact mem_localLevelOne_of_mem_integralSubgroup F w hv hk
    · rw [finComponent_glFin_adicToAdelic_of_ne F v k hw]
      exact one_mem _
  · by_cases hw : w = v
    · subst hw
      rw [finComponent_glFin_adicToAdelic]
      exact mem_localLevelOne_of_mem_integralSubgroup F w hv
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (weylInt_mem)) hk) (weylInt_mem))
    · rw [finComponent_glFin_adicToAdelic_of_ne F v k hw, mul_one, inv_mul_cancel]
      exact one_mem _

theorem heckeGen_inv_mul_docked_mem_U {N : Ideal (𝓞 F)} :
    (heckeGen (𝓞 F) F v)⁻¹
      * adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v))
      ∈ prinU F N := by
  rw [adicToAdelic_diagPi]
  show (heckeGenAt (𝓞 F) F v (uniformizerUnit F v))⁻¹ * heckeGenAt (𝓞 F) F v (uniformizerUnit F v) ∈ prinU F N
  rw [inv_mul_cancel]
  exact one_mem _

theorem isHeckeCosetSystem_docked {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    IsHeckeCosetSystem (prinU F N)
      (adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v)))
      (fun i => adicToAdelic F v (genHeckeRep F v i)) := by
  have S := isHeckeCosetSystem_genHeckeRep F v
  constructor
  · intro i
    obtain ⟨u, hu, u', hu', heq⟩ := HeckePair.mem_doubleCoset_iff.mp (S.mem_doubleCoset i)
    refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨adicToAdelic F v u, adicToAdelic_mem_generalU F v hv hu,
       adicToAdelic F v u', adicToAdelic_mem_generalU F v hv hu', ?_⟩
    rw [← map_mul, ← map_mul, heq]
  · intro z hz
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hz
    obtain ⟨harch₁, hfin₁, hfin₁'⟩ := components_of_mem_prinU F hu₁
    set y₁ : GL (Fin 2) (v.adicCompletion F) := finComponent (𝓞 F) F v (glFin (𝓞 F) F u₁)
      with hy₁def
    have hy₁ : y₁ ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) :=
      mem_integralSubgroup_of_mem_localLevelOne F v (hfin₁ v)
    have hylocal : y₁ * diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v)
        ∈ HeckePair.doubleCoset
          (integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F))
          (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v)) :=
      HeckePair.mem_doubleCoset_iff.mpr ⟨y₁, hy₁, 1, one_mem _, by rw [mul_one]⟩
    obtain ⟨i₀, hi₀⟩ := S.covers _ hylocal
    have habs : (QuotientGroup.mk (u₁
          * adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v)) * u₂) :
        _ ⧸ prinU F N)
        = QuotientGroup.mk (u₁
          * adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v))) := by
      rw [QuotientGroup.eq]
      simpa [mul_inv_rev, mul_assoc] using (prinU F N).inv_mem hu₂
    have hloc : (y₁ * diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v))⁻¹
        * genHeckeRep F v i₀
        ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) :=
      QuotientGroup.eq.mp hi₀
    have hkey : ((u₁ * adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v)))⁻¹
        * adicToAdelic F v (genHeckeRep F v i₀)) ∈ prinU F N := by
      refine mem_prinU_of_components F ?_ ?_ ?_
      · simp only [map_mul, map_inv, mul_inv_rev, glArch_adicToAdelic, harch₁]
        simp
      · intro w
        by_cases hw : w = v
        · subst hw
          have hloc2 : (y₁ * diagPi (piLoc F w) (algebraMap_piLoc_ne_zero F w))⁻¹
              * genHeckeRep F w i₀ ∈ localLevelOne (𝓞 F) F w N :=
            mem_localLevelOne_of_mem_integralSubgroup F w hv hloc
          have hgoal_eq : finComponent (𝓞 F) F w (glFin (𝓞 F) F
              ((u₁ * adicToAdelic F w (diagPi (piLoc F w) (algebraMap_piLoc_ne_zero F w)))⁻¹
                * adicToAdelic F w (genHeckeRep F w i₀)))
              = (y₁ * diagPi (piLoc F w) (algebraMap_piLoc_ne_zero F w))⁻¹
                * genHeckeRep F w i₀ := by
            simp only [map_mul, map_inv, mul_inv_rev, finComponent_glFin_adicToAdelic, hy₁def]
          rw [hgoal_eq]
          exact hloc2
        · have hgone : finComponent (𝓞 F) F w (glFin (𝓞 F) F
              ((u₁ * adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v)))⁻¹
                * adicToAdelic F v (genHeckeRep F v i₀)))
              = (finComponent (𝓞 F) F w (glFin (𝓞 F) F u₁))⁻¹ := by
            simp only [map_mul, map_inv, mul_inv_rev,
              finComponent_glFin_adicToAdelic_of_ne F v _ hw]
            simp
          rw [hgone]
          exact Subgroup.inv_mem _ (hfin₁ w)
      · intro w
        by_cases hw : w = v
        · subst hw
          have hloc2 : (weylInt (w.adicCompletionIntegers F) (w.adicCompletion F))⁻¹
              * ((y₁ * diagPi (piLoc F w) (algebraMap_piLoc_ne_zero F w))⁻¹ * genHeckeRep F w i₀)
              * weylInt (w.adicCompletionIntegers F) (w.adicCompletion F) ∈ localLevelOne (𝓞 F) F w N :=
            mem_localLevelOne_of_mem_integralSubgroup F w hv
              (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ weylInt_mem) hloc) weylInt_mem)
          have hgoal_eq : finComponent (𝓞 F) F w (glFin (𝓞 F) F
              ((u₁ * adicToAdelic F w (diagPi (piLoc F w) (algebraMap_piLoc_ne_zero F w)))⁻¹
                * adicToAdelic F w (genHeckeRep F w i₀)))
              = (y₁ * diagPi (piLoc F w) (algebraMap_piLoc_ne_zero F w))⁻¹
                * genHeckeRep F w i₀ := by
            simp only [map_mul, map_inv, mul_inv_rev, finComponent_glFin_adicToAdelic, hy₁def]
          rw [hgoal_eq]
          exact hloc2
        · have hgone : finComponent (𝓞 F) F w (glFin (𝓞 F) F
              ((u₁ * adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v)))⁻¹
                * adicToAdelic F v (genHeckeRep F v i₀)))
              = (finComponent (𝓞 F) F w (glFin (𝓞 F) F u₁))⁻¹ := by
            simp only [map_mul, map_inv, mul_inv_rev,
              finComponent_glFin_adicToAdelic_of_ne F v _ hw]
            simp
          rw [hgone]
          have h3 := hfin₁' w
          have : (weylInt (w.adicCompletionIntegers F) (w.adicCompletion F))⁻¹
              * (finComponent (𝓞 F) F w (glFin (𝓞 F) F u₁))⁻¹
              * weylInt (w.adicCompletionIntegers F) (w.adicCompletion F)
              = ((weylInt (w.adicCompletionIntegers F) (w.adicCompletion F))⁻¹
                  * finComponent (𝓞 F) F w (glFin (𝓞 F) F u₁)
                  * weylInt (w.adicCompletionIntegers F) (w.adicCompletion F))⁻¹ := by
            group
          rw [this]
          exact Subgroup.inv_mem _ h3
    exact ⟨i₀, habs.trans (QuotientGroup.eq.mpr hkey)⟩
  · intro i j hij
    rw [QuotientGroup.eq] at hij
    rw [← map_inv, ← map_mul] at hij
    have hcomp := (components_of_mem_prinU F hij).2.1 v
    rw [finComponent_glFin_adicToAdelic] at hcomp
    have hmem := mem_integralSubgroup_of_mem_localLevelOne F v hcomp
    exact S.mk_injective (QuotientGroup.eq.mpr hmem)

theorem exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd_dev
    (N : Ideal (𝓞 F)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      IsHeckeCosetSystem (prinU F N) (heckeGen (𝓞 F) F v) reps := by
  have habs : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := (Ideal.absNorm_ne_zero_iff v.asIdeal).mp habs
  haveI : Fintype (Option (𝓞 F ⧸ v.asIdeal)) := Fintype.ofFinite _
  have ecard : Fintype.card (Fin (Ideal.absNorm v.asIdeal + 1))
      = Fintype.card (Option (𝓞 F ⧸ v.asIdeal)) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_option_quotient]
  refine ⟨(fun i => adicToAdelic F v (genHeckeRep F v i)) ∘ Fintype.equivOfCardEq ecard, ?_⟩
  have hdock := isHeckeCosetSystem_docked F v hv
  have hdc : HeckePair.doubleCoset (prinU F N) (heckeGen (𝓞 F) F v)
      = HeckePair.doubleCoset (prinU F N)
        (adicToAdelic F v (diagPi (piLoc F v) (algebraMap_piLoc_ne_zero F v))) :=
    (doubleCoset_eq_of_inv_mul_mem (heckeGen_inv_mul_docked_mem_U F v)).symm
  exact isHeckeCosetSystem_comp_equiv _ (isHeckeCosetSystem_congr_gen hdc hdock)

end Aux4SevenTNPrincipal

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletionIntegers F,
      ∃ hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0,
        Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) ∧
        finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v ∧
        ∃ sec : 𝓞 F ⧸ v.asIdeal → 𝓞 F,
          (∀ c : 𝓞 F ⧸ v.asIdeal, Ideal.Quotient.mk v.asIdeal (sec c) = c) ∧
          ∀ M : Ideal (𝓞 F), ¬ v.asIdeal ∣ M →
            HeckeIntegralSeam.IsHeckeCosetSystem
              (principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
              (fun i : Option (𝓞 F ⧸ v.asIdeal) =>
                finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
                  (i.elim (localRepInf ϖ hϖ0)
                    (fun c => localRepSome ϖ hϖ0
                      (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c)))))) := by
  refine ⟨Aux4SevenTN.piLoc F v, Aux4SevenTN.algebraMap_piLoc_ne_zero F v,
    Aux4SevenTN.valued_piLoc F v, Aux4SevenTN.adicToAdelic_diagPi F v, Quotient.out,
    fun c => mk_out F v c, fun M hM => ?_⟩
  rw [family_eq, heckeGen_eq_adicToAdelic]
  exact Aux4SevenTNPrincipal.isHeckeCosetSystem_docked F v hM
