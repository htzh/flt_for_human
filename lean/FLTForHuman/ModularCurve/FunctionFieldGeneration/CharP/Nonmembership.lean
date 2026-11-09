/-
  The prime non-membership over an arbitrary field: the `C` layer's instance of the generic theorem.

  At `κ = κ' = K`, `ε = RingHom.id` and `jg = jqModC K`, the theory's statement reads: for a prime
  `p ∤ M`, the level-degree package at `M` and the non-membership in the base field, the level-`p`
  series is not in the level-`M` field. The conclusion is *relative* — `levelField (jqModC K) M` is
  `K⟮jqModC K⟯⟮jqNModC K M⟯` — while the pin's statement is *absolute*, over the adjoin of the
  level series at the divisors of `M`; `mem_levelField_of_mem_divisorAdjoin` is the one step between
  them, and it spends the package's generation clause.

  So the delegation is: discharge the theory's source condition (`rfl` here, since `jg` is
  `jqModC K` and the two fields coincide), convert `Pkg` to `PkgAt` (`pkg_pkgAt`), take the
  package's generation clause at `M`, and apply the generic theorem. The two per-layer inputs are exactly the
  pin's: the package conjunction and `hbase`. In particular no `degreeAt (jqModC K) p` is needed —
  the theory does not ask for one.

  `jqNModC_prime_not_mem_fullC` is the pinned wrapper's statement verbatim (explicit `hall`
  conjunction, explicit divisor adjoin), so this module is the `C` layer's only public node in the
  prime non-membership, as `CharP/SlotProduct.lean` is for the slot product.
  spec-pin: Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean
  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_fullC.lean
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.PrimeNonmembership
import FLTForHuman.ModularCurve.FunctionFieldGeneration.CharP.LevelPackage

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-- **Prime non-membership over an arbitrary field**: `jqNModC K p ∉ fullC K M` for `p ∤ M`. The
pin's wrapper verbatim — explicit `hall` conjunction and explicit divisor adjoin — delegated to the
generic `prime_notMem_levelField` at `(ε := RingHom.id) (jg := jqModC K)`, with the absolute-to-
relative step supplied by `mem_levelField_of_mem_divisorAdjoin`. -/
theorem jqNModC_prime_not_mem_fullC {K : Type*} [Field K] (M : ℕ) [NeZero M]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'})
    (hbase : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    jqNModC K p ∉ IntermediateField.adjoin K
      {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'} := by
  intro hmem
  have h : PkgAt (jqModC K) M := pkg_pkgAt M hall
  obtain ⟨-, hgen⟩ := h M dvd_rfl
  exact prime_notMem_levelField (κ' := K) (jqModC K) rfl hζ hpM h hbase
    (mem_levelField_of_mem_divisorAdjoin hgen hmem)

end ModularCurve
