/-
  Consumer specification for T12 SET 2, the eigenform-extraction chain.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the five SET-2 modules, at their subject homes:

  * `FLTForHuman/Algebra/IntegralExtensionCharacters.lean` — the two generic
    character/prime existence lemmas;
  * `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean` — the generic
    faithful-lattice eigenvector;
  * `FLTForHuman/ModularForms/Level/Degeneracy.lean` — `exists_degeneracy_Gamma0`;
  * `FLTForHuman/ModularForms/EigenformLevel.lean` — the two level-raising
    headlines;
  * `FLTForHuman/ModularForms/EigenformExtraction.lean` — the three extraction
    statements.

  The `[extraction]` zone below is a real cross-module composition (not a list of
  `#check`s and not `sorry`-terminated, playbook §7.2): a Hecke character `χ` is
  fed to `HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq`
  (EigenformExtraction), the resulting normalised eigenform is handed to the
  ported `IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul` dictionary
  (HeckeEigenform) to read off its `T_ℓ` eigenvalue, and the same eigenform is
  then raised to level `N * p` by `exists_isNormalizedEigenform_level_mul`
  (EigenformLevel). Deleting any of the three modules fails this file. The
  remaining zones exercise the degeneracy map and the two generic algebra nodes.

  It is deliberately **not part of any library** (nothing globs `spec/`), so it
  can never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideSet2Consumer.lean 2>&1 | grep -c error
-/
import FLTForHuman.Algebra.IntegralExtensionCharacters
import FLTForHuman.Algebra.FaithfulLatticeEigenvector
import FLTForHuman.ModularForms.Level.Degeneracy
import FLTForHuman.ModularForms.EigenformLevel
import FLTForHuman.ModularForms.EigenformExtraction

set_option autoImplicit false

noncomputable section

/-! ## Zone `[extraction]` — character → eigenform → Hecke eigenvalue → level raise -/

namespace TsideSet2

variable {N : ℕ} [NeZero N] {S : Set ℕ}

-- The wire test. `exists_isNormalizedEigenform_qCoeff_eq` (EigenformExtraction)
-- produces a normalised eigenform `f` for `χ` with `qCoeff f ℓ = χ (T_ℓ)`;
-- `heckeTLin_apply_eq_qCoeff_smul` (HeckeEigenform) rewrites `T_ℓ f` as
-- `qCoeff f ℓ • f`; substituting the character value yields the eigenvalue
-- equation. The same `f` is then raised to level `N * p` by
-- `exists_isNormalizedEigenform_level_mul` (EigenformLevel).
example (hN : CuspForm.HasIntegralStructure N 2) (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) {p : ℕ} (hp : p.Prime) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      f.IsNormalizedEigenform ∧
      CuspForm.heckeTLin 2 hℓ hℓN f = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) • f ∧
      ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2, g.IsNormalizedEigenform := by
  obtain ⟨f, hf, hfT, -⟩ := CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq hN χ
  refine ⟨f, hf, ?_, ?_⟩
  · rw [CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul N f hf ℓ hℓ hℓN,
      hfT ℓ hℓ hℓN hℓS]
  · obtain ⟨g, hg, -⟩ := CuspForm.exists_isNormalizedEigenform_level_mul f hf hp
    exact ⟨g, hg⟩

-- The `U_q` half of the same dictionary: at a prime `q ∣ N` outside `S`, the
-- character value is again the eigenvalue.
example (hN : CuspForm.HasIntegralStructure N 2) (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      f.IsNormalizedEigenform ∧
      CuspForm.heckeULin 2 hqN f = χ (CuspForm.heckeAlgebra.U hq hqN hqS) • f := by
  obtain ⟨f, hf, -, hfU⟩ := CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq hN χ
  exact ⟨f, hf, by rw [CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul N f hf q hq hqN,
    hfU q hq hqN hqS]⟩

/-! ## Zone `[level]` — degeneracy and the level-divisibility iteration -/

-- The degeneracy map `f(τ) ↦ f(dτ)` (Degeneracy), whose level target is then an
-- input of the level-divisibility iteration (EigenformLevel): raising an
-- eigenform along `M ∣ N` agrees at coefficients coprime to `N`.
example {M N d : ℕ} [NeZero N] (hd : d * M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) :=
  CuspForm.exists_degeneracy_Gamma0 hd f

example {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, n.Coprime N → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n :=
  CuspForm.exists_isNormalizedEigenform_of_dvd hMN f hf

/-! ## Zone `[algebra]` — the two generic nodes the extraction is built on -/

-- `IntegralExtensionCharacters`: a character of `A` extends along an integral
-- extension `A → B`.
example {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    [Field K] [IsAlgClosed K] (χ : A →+* K)
    (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ :=
  RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed χ hker

-- `FaithfulLatticeEigenvector`: the generic engine the extraction applies to the
-- Hecke algebra; here instantiated at its abstract hypotheses.
example {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [CommRing T]
    (ρ : T →+* Module.End K V) (L : Submodule ℤ V) (hL : L.FG)
    (hstab : ∀ (t : T), ∀ x ∈ L, ρ t x ∈ L)
    (hfaith : ∀ t : T, (∀ x ∈ L, ρ t x = 0) → t = 0)
    (hfree : ∀ (n : ℕ) (y : Fin n → V), (∀ i, y i ∈ L) → LinearIndependent ℤ y →
      LinearIndependent K y) (χ : T →+* K) :
    ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v :=
  Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom ρ L hL hstab hfaith hfree χ

end TsideSet2

end
