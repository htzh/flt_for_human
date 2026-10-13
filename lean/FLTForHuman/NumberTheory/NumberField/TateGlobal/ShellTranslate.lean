/-
  The shell translation: invariance of the set integral under left translation
  (`setIntegral_smul_eq'`), the norm of the zeta integrand
  (`norm_zetaIntegrand`), the real power of `ideleNorm` on a uniformizer power
  (`ideleNorm_unifPow_rpow`) and the per-shell norm bound
  `setIntegral_shell_norm_le`.

  Transcribed from the pin's `Fold_ShellTranslate` section
  (`M4aLocalCFT.ShellTranslate` namespace), declared lines 5004-5091 of file A,
  pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, and so are the
  file-scoped `set_option maxHeartbeats 1600000` / `maxSynthPendingDepth 3`
  (A 4984/4986); the declarations elaborate at the low edit cap.  The pin's
  deprecated `if_pos`/`if_neg` are spelled `ite_eq_left`/`ite_eq_right`
  (proof-only change).  No file-wide option beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ShellBound
import FLTForHuman.AutomorphicForm.Adelic.LsXi

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_ShellTranslate

open AutomorphicForm IsDedekindDomain
open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal Pointwise

noncomputable section

namespace NumberField
namespace TateGlobal
namespace ShellTranslate

variable {F : Type} [Field F] [NumberField F]

-- pin: setIntegral_smul_eq' (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5004)
theorem setIntegral_smul_eq' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    {U : Set (AdeleRing (𝓞 F) F)ˣ} (hU : MeasurableSet U) (g : (AdeleRing (𝓞 F) F)ˣ)
    (G : (AdeleRing (𝓞 F) F)ˣ → E) :
    ∫ x in g • U, G x ∂ν = ∫ u in U, G (g * u) ∂ν := by
  have hgU : MeasurableSet (g • U) := hU.const_smul g
  rw [← integral_indicator hgU, ← integral_indicator hU, ← integral_mul_left_eq_self _ g]
  congr 1
  funext u
  have hiff : g * u ∈ g • U ↔ u ∈ U := by
    constructor
    · intro h
      obtain ⟨u', hu', h'⟩ := Set.mem_smul_set.mp h
      rw [smul_eq_mul] at h'
      rw [← mul_left_cancel h']
      exact hu'
    · intro hu
      exact Set.mem_smul_set.mpr ⟨u, hu, rfl⟩
  simp only [Set.indicator]
  by_cases hu : u ∈ U
  · rw [ite_eq_left (hiff.mpr hu), ite_eq_left hu]
  · rw [ite_eq_right (mt hiff.mp hu), ite_eq_right hu]

-- pin: norm_zetaIntegrand (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5028)
theorem norm_zetaIntegrand {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχu : IsUnitaryChar (𝓞 F) F χ) (f : AdeleRing (𝓞 F) F → ℂ) (s : ℂ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    ‖f ↑x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖
      = ‖f ↑x‖ * ideleNorm F x ^ s.re := by
  rw [norm_mul, norm_mul, hχu x, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos x)]

-- pin: ideleNorm_unifPow_rpow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5036)
theorem ideleNorm_unifPow_rpow (ϖ : Uniformizers F) (σ : ℝ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    ideleNorm F (unifPow ϖ k) ^ σ
      = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat := by
  rw [ShellBound.ideleNorm_unifPow, Finsupp.prod, Finsupp.prod,
    ← Real.finsetProd_rpow _ _ (fun v _ => zpow_nonneg (Nat.cast_nonneg _) _) σ]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hn : 0 ≤ k v := Finsupp.le_def.mp hk v
  have ha : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (ShellBound.one_lt_absNorm v).le
  calc ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(k v))) ^ σ
      = ((Ideal.absNorm v.asIdeal : ℝ) ^ ((-(k v) : ℤ) : ℝ)) ^ σ := by
        rw [Real.rpow_intCast]
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (((-(k v) : ℤ) : ℝ) * σ) := by
        rw [← Real.rpow_mul ha.le]
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ ((-σ) * ((k v).toNat : ℝ)) := by
        congr 1
        have hcast : (((k v).toNat : ℕ) : ℝ) = ((k v : ℤ) : ℝ) := by
          exact_mod_cast congrArg (Int.cast (R := ℝ)) (Int.toNat_of_nonneg hn)
        rw [hcast]
        push_cast
        ring
    _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ ((k v).toNat : ℝ) := by
        rw [Real.rpow_mul ha.le]
    _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ (k v).toNat := by
        rw [Real.rpow_natCast]

-- pin: setIntegral_shell_norm_le (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5063)
theorem setIntegral_shell_norm_le [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] (ϖ : Uniformizers F)
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    {f : AdeleRing (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχu : IsUnitaryChar (𝓞 F) F χ) {s : ℂ} {M : ℝ}
    (k : ExpIndex (F := F) S) (hk : 0 ≤ k.1)
    (hM : ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
        ‖f ↑(unifPow ϖ k.1 * u)‖ * ideleNorm F u ^ s.re ∂ν ≤ M) :
    ∫ x in shell S k.1, ‖f ↑x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν
      ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat) * M := by
  have hC0 : 0 ≤ k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat := by
    rw [Finsupp.prod]
    exact Finset.prod_nonneg fun v _ =>
      pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
  have hpt : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      ‖f ↑(unifPow ϖ k.1 * u) * ((χ (unifPow ϖ k.1 * u) : ℂˣ) : ℂ)
          * ((ideleNorm F (unifPow ϖ k.1 * u) : ℝ) : ℂ) ^ s‖
        = (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat)
          * (‖f ↑(unifPow ϖ k.1 * u)‖ * ideleNorm F u ^ s.re) := fun u => by
    rw [norm_zetaIntegrand hχu, ideleNorm_mul,
      Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le,
      ideleNorm_unifPow_rpow ϖ s.re hk]
    ring
  rw [shell_eq_smul ϖ k.2, setIntegral_smul_eq' ν (isOpen_unitsOutside S).measurableSet]
  simp only [hpt]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hM hC0

end ShellTranslate
end TateGlobal
end NumberField

end

end Fold_ShellTranslate
