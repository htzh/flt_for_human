/-
  The count of cyclic subgroups of order `n` on an elliptic curve over an
  algebraically closed field.

  For `F` a field, `K` an algebraically closed `F`-algebra in which `n` is invertible,
  and `W/F` elliptic, the number of additive subgroups `G ≤ (W⁄K).Point` that are
  cyclic of cardinality `n` is the Dedekind psi value `ψ(n)`:

  `Nat.card {G : AddSubgroup (W⁄K).Point // IsAddCyclic G ∧ Nat.card G = n} = ψ(n)`.

  This is the moduli count the modular-equation theory uses: `ψ(N)` is the `Y`-degree
  of `Φ_N`, and (at an odd prime `ℓ`, where `ψ(ℓ) = ℓ + 1`) the number of cyclic
  order-`ℓ` subgroups whose Vélu quotients give the `ℓ + 1` roots.

  The two ingredients are both in the port: the torsion classification
  `W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`
  (`Elliptic/TorsionZMod.lean`), which gives `(W⁄K)[n] ≅ (ℤ/n)²`, and the generic
  count `AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy`
  (`WeierstrassCurve/Velu/CyclicCount.lean`), which transports the projective-line
  count of cyclic subgroups of `(ℤ/n)²` along that equivalence.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`:
  `Theorems/Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed.lean`
  (15 lines); proof from
  `P2M/Sol/S_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed.lean`
  (22 lines).

  spec-pin: Theorems/Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed.lean
-/
import FLTForHuman.Elliptic.TorsionZMod
import FLTForHuman.WeierstrassCurve.Velu.CyclicCount

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

set_option linter.style.haveILetI false in
/-- **`ψ(n)` cyclic order-`n` subgroups.**  Over an algebraically closed field in which
`n` is invertible, an elliptic curve has exactly `ψ(n)` cyclic subgroups of order `n`.
Verbatim from
`Theorems/Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed.lean`. -/
theorem WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card {G : AddSubgroup (W⁄K).Point // IsAddCyclic G ∧ Nat.card G = n}
      = ModularCurve.dedekindPsi n := by
  haveI : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  obtain ⟨e⟩ := W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) hn
  exact AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy n e

end
