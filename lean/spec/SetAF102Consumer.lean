/-
  Cross-module wire test for SET-AF102 — the torsion basis at the two exceptional `j`-invariants,
  the char-two orbit count, the faithful-inertia good model, and (once landed) the two `jq`
  integrality modules.

  A `spec/` probe, not a library module. One zone per order, each *firing* its headline at concrete
  data and reading the conclusion in the shape the downstream cone reads it — no `#check`s, no
  `sorry`s, no restated theorems.

  * **Zone A1** `WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three` at
    `K = AlgebraicClosure ℚ`, `M = 2`: the `∃!`-basis half of the conclusion at the smallest modulus.
  * **Zone A2** `WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two`
    at a char-two algebraically closed field, with the cube root of unity the headline needs
    **produced by A1's own engine** `WeierstrassCurve.Automorphism.exists_cube_root` (so the zone
    composes two orders of the set).
  * **Zone A3** `WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` at the
    concrete curve `legendreCurve 2` over `ℚ → AlgebraicClosure ℚ`, ellipticity discharged from
    `LegendreNormalForm.legendre_Δ` (`Δ = 64`), reading the Galois subfield it produces.
-/
import FLTForHuman.WeierstrassCurve.Automorphism.TorsionBasis
import FLTForHuman.WeierstrassCurve.Reduction.InertiaFaithful
import FLTForHuman.ModularCurve.LevelN.TorsionOrbit
import FLTForHuman.ModularCurve.Analytic.JqInverseIntegral
import FLTForHuman.ModularCurve.Analytic.JqModCIntegral

set_option autoImplicit false

noncomputable section

open WeierstrassCurve
open scoped WeierstrassCurve Topology

namespace SetAF102Consumer

/-! ## Zone A1 — the `j = 0` torsion basis at `M = 2` -/

theorem j_zero_basis_pair_ne :
    ∃ (E : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E.IsElliptic) (P Q : E.toAffine.Point),
      E.j = 0 ∧ P ≠ Q := by
  let _ : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
  obtain ⟨E, hE, _, P, Q, hj, -, h2P, -, hbasis, -, -⟩ :=
    WeierstrassCurve.exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three
      (K := AlgebraicClosure ℚ) 2 (by norm_num)
  let _ : E.IsElliptic := hE
  refine ⟨E, hE, P, Q, hj, fun hPQ => ?_⟩
  -- `P` is its own `(1,0)`- and its own `(0,1)`-combination, so uniqueness forces `(1,0) = (0,1)`.
  obtain ⟨c₀, -, huniq⟩ := hbasis P h2P
  have h1 : P = ((1 : ZMod 2)).val • P + ((0 : ZMod 2)).val • Q := by
    rw [ZMod.val_one 2]
    simp
  have h2 : P = ((0 : ZMod 2)).val • P + ((1 : ZMod 2)).val • Q := by
    rw [hPQ, ZMod.val_one 2]
    simp
  have hc1 : ((1 : ZMod 2), (0 : ZMod 2)) = c₀ := huniq _ h1
  have hc2 : ((0 : ZMod 2), (1 : ZMod 2)) = c₀ := huniq _ h2
  exact absurd (congrArg Prod.fst (hc1.trans hc2.symm)) (by decide)

/-! ## Zone A2 — the char-two orbit count, with `w` from A1's cube-root engine -/

theorem char_two_orbit_count (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (M : ℕ) [NeZero M] (hM : (M : L) ≠ 0) (H : Subgroup (ZMod M)ˣ) :
    Nat.card {s : Set (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
        ∃ P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf P = M ∧
          s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
            T = (u : ZMod M).val • P}} =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h3 : (3 : L) ≠ 0 := by
    intro h
    have h1 : (1 : L) = 0 := by linear_combination h - h2
    exact one_ne_zero h1
  obtain ⟨w, hw, hw1⟩ := WeierstrassCurve.Automorphism.exists_cube_root (K := L) h3
  exact (WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
    w hw hw1 M hM H).1

/-! ## Zone A3 — the Galois subfield at the Legendre curve -/

theorem legendreCurve_two_isElliptic : (legendreCurve (2 : ℚ)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, LegendreNormalForm.legendre_Δ]
  norm_num

theorem exists_galois_subfield_of_legendre :
    ∃ S : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ S ∧ IsGalois ℚ S := by
  let _ : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
  let _ : (legendreCurve (2 : ℚ)).IsElliptic := legendreCurve_two_isElliptic
  obtain ⟨S, hfd, hgal, -⟩ :=
    WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
      (E := legendreCurve (2 : ℚ)) (Ω := AlgebraicClosure ℚ) (by norm_num)
  exact ⟨S, hfd, hgal⟩

/-! ## Zone M1 — firing the 233 headline at `X = 0` produces a cusp form with vanishing
`q`-expansion -/

theorem exists_cuspForm_qExpansion_eq_zero :
    ∃ f : CuspForm ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) (2 * (1 : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) = 0 := by
  obtain ⟨f, hf⟩ :=
    ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
      (Γ := ⊤) (hT := Subgroup.mem_top ModularGroup.T) (m := 1) le_rfl
      (X := 0) (M := 1) (by simp) (by simp [isIntegral_zero]) (by simp [isIntegral_zero])
  exact ⟨f, by simpa using hf⟩

end SetAF102Consumer
