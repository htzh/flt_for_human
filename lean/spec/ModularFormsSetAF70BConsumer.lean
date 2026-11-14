/-
  Cross-module wire test for SET-AF70B (Eichler--Shimura in weight two for `Γ_H(M)`, and the
  two-dimensional eigenspace).

  A `spec/` probe, not a library module. One zone per headline of
  `ModularForms/EichlerShimura/WeightTwoCohomology.lean`, each *consuming* the headline rather than
  restating it: the row is fired at concrete data and the conclusion is read in the shape the
  downstream cone will read it.

  * **Zone G, row `CohCarrier.exists_eichlerShimura_H1_gammaH` at `M = 2`, `H = ⊤`.** The
    `∃ J ES` package is fired and read at the zero pair `f = g = 0` (`ES (0, 0) = 0`, through the
    row's own linearity), on the involution `J` (`↑(J γ) = jConjSL ↑γ`), and the
    Hecke-equivariance conjunct is read at the prime `ℓ = 3` (`3 ∤ 2`, so the `T_3` line
    `ES (T_3 f, T_3 g) = T_3 (ES (f, g))`). Injectivity and the range identification are carried
    along in the same package.

  * **Zone H, row `CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two`
    at `M = 2`, `H = ⊤`, `S = ∅`.** The `Fin 2` basis of the parabolic cohomology over the Hecke
    algebra is fired and read by its coordinate expansion `∑ i, b.repr v i • b i = v`, and the
    eigenbasis half of the row is read at an arbitrary character `χ`: the simultaneous eigenspace
    `⨅ a, eigenspace (a) (χ a)` is two-dimensional.

  The two `abbrev`s `Vtwo` and `Atwo` name the two types the row is stated in, so that the zone
  can read them without re-spelling the Hecke generating set.

  The file contains no `#check`s, no `sorry`s and no placeholder proofs.
-/
import FLTForHuman.ModularForms.EichlerShimura.WeightTwoCohomology

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularCurve ModularCurve.Period UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace SetAF70BConsumer

/-! ## The two types the row `477` is stated in, at `M = 2`, `H = ⊤`, `S = ∅` -/

/-- The parabolic cohomology of `Γ_H(2)` at `H = ⊤`, as the row `477` reads it. -/
abbrev Vtwo : Type := ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH 2 ⊤) ℂ)

/-- The Hecke algebra of the row `477` at `M = 2`, `H = ⊤`, `S = ∅`, inside the endomorphism ring
of the parabolic cohomology. -/
abbrev Atwo : Subalgebra ℂ (Module.End ℂ Vtwo) :=
  Algebra.adjoin ℂ {T : Module.End ℂ Vtwo |
    (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ (∅ : Set ℕ) ∨ ℓ ∣ 2) ∧
      ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      ((T v : Vtwo) : CohCarrier.H1 2 ⊤ ℂ) = CohCarrier.heckeT 2 ⊤ ℓ ℂ (v : CohCarrier.H1 2 ⊤ ℂ)) ∨
    (∃ d : (ZMod 2)ˣ, ∀ v,
      ((T v : Vtwo) : CohCarrier.H1 2 ⊤ ℂ) = CohCarrier.diamondL 2 ⊤ ℂ d (v : CohCarrier.H1 2 ⊤ ℂ))}

/-! ## Zone G — the `409` at `M = 2`, `H = ⊤`, read at `f = g = 0` and at `ℓ = 3` -/

/-- Zone G: the Eichler--Shimura package at `M = 2`, `H = ⊤`, with the period map read at the zero
pair, the involution `J` read on its values, and the `T_3` equivariance read at `ℓ = 3`. -/
theorem zoneG_two :
    ∃ (J : ↥(CohCarrier.GammaH 2 ⊤) →* ↥(CohCarrier.GammaH 2 ⊤))
      (ES : (CuspForm (CohCarrier.GammaH 2 ⊤) 2 × CuspForm (CohCarrier.GammaH 2 ⊤) 2) →ₗ[ℂ]
        CohCarrier.H1 2 ⊤ ℂ),
      (∀ γ : ↥(CohCarrier.GammaH 2 ⊤),
        ((J γ : ↥(CohCarrier.GammaH 2 ⊤)) : SL(2, ℤ)) =
          ModularCurve.Period.jConjSL (γ : SL(2, ℤ))) ∧
      ES (0, 0) = 0 ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH 2 ⊤) ℂ ∧
      (∀ (f g : CuspForm (CohCarrier.GammaH 2 ⊤) 2),
        ES (CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num) f,
            CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num) g) =
          CohCarrier.heckeT 2 ⊤ 3 ℂ (ES (f, g))) := by
  obtain ⟨J, ES, hJ, -, hinj, hrange, hT, -, -⟩ := CohCarrier.exists_eichlerShimura_H1_gammaH 2 ⊤
  have h0 : ((0 : CuspForm (CohCarrier.GammaH 2 ⊤) 2), (0 : CuspForm (CohCarrier.GammaH 2 ⊤) 2)) =
      (0 : CuspForm (CohCarrier.GammaH 2 ⊤) 2 × CuspForm (CohCarrier.GammaH 2 ⊤) 2) := rfl
  exact ⟨J, ES, hJ, by rw [h0, map_zero], hinj, hrange,
    fun f g => hT 3 (by norm_num) (by norm_num) f g⟩

/-- Zone G, the period conjunct spent on the zero pair at a fixed coset `γ : Γ_H(2)`: the
Eichler--Shimura period map vanishes there. -/
theorem zoneG_two_apply (γ : ↥(CohCarrier.GammaH 2 ⊤)) :
    ∃ (J : ↥(CohCarrier.GammaH 2 ⊤) →* ↥(CohCarrier.GammaH 2 ⊤))
      (ES : (CuspForm (CohCarrier.GammaH 2 ⊤) 2 × CuspForm (CohCarrier.GammaH 2 ⊤) 2) →ₗ[ℂ]
        CohCarrier.H1 2 ⊤ ℂ),
      ((J γ : ↥(CohCarrier.GammaH 2 ⊤)) : SL(2, ℤ)) = ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) ∧
      ES (0, 0) (Additive.ofMul γ) = 0 := by
  obtain ⟨J, ES, hJ, -, -, -, -, -, -⟩ := CohCarrier.exists_eichlerShimura_H1_gammaH 2 ⊤
  have h0 : ((0 : CuspForm (CohCarrier.GammaH 2 ⊤) 2), (0 : CuspForm (CohCarrier.GammaH 2 ⊤) 2)) =
      (0 : CuspForm (CohCarrier.GammaH 2 ⊤) 2 × CuspForm (CohCarrier.GammaH 2 ⊤) 2) := rfl
  exact ⟨J, ES, hJ γ, by rw [h0, map_zero, AddMonoidHom.zero_apply]⟩

/-! ## Zone H — the `477` at `M = 2`, `H = ⊤`, `S = ∅`, the `Fin 2` basis and the eigenspace -/

/-- Zone H: the `Fin 2` basis of the parabolic cohomology at `M = 2`, `H = ⊤`, `S = ∅`, read by its
coordinate expansion, together with the two-dimensionality of every character's simultaneous
eigenspace. -/
theorem zoneH_two :
    ∃ b : Module.Basis (Fin 2) ↥Atwo Vtwo,
      (∀ v : Vtwo, ∑ i : Fin 2, b.repr v i • b i = v) ∧
      ∀ χ : ↥Atwo →ₐ[ℂ] ℂ,
        Module.finrank ℂ ↥(⨅ a : ↥Atwo, Module.End.eigenspace (a : Module.End ℂ Vtwo) (χ a)) = 2 := by
  obtain ⟨⟨b⟩, hχ⟩ :=
    CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two 2 ⊤ ∅
      (Set.finite_empty)
  exact ⟨b, fun v => b.sum_repr v, hχ⟩

end SetAF70BConsumer
