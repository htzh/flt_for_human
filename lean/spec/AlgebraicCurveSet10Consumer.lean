/-
  Consumer specification for SET 10 of the `AlgebraicCurve` layer.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed across modules, expressed in Lean so
  that each is either bound or not.  It is a deliverable measure, not a proof obligation.  It
  is **not part of any library** (`lake build` does not see `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/AlgebraicCurveSet10Consumer.lean 2>&1 | grep -c error

  The error count is the metric.

  ZONES
  -----
    [h1]   ZONE A — `genusFF_eq_of_constantFieldExtension_of_isAlgClosed`
               (`Genus/ConstantFieldExtensionConsequences.lean`) read through the definition of
               `genusFF` (`Defs/Repartitions.lean`): the two `H¹` dimensions at the zero divisor
               agree, so the invariance is an invariance of the cohomology, not only of a number.
    [ell]  ZONE B — the genus equality composed with SET 9's
               `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed`
               (`IsCurveOver/ConstantFieldExtensionSpan.lean`) at the same `lift`: the two
               Riemann-Roch invariants are invariant together, which is what a later row that
               compares Riemann-Roch data across the extension consumes.
-/
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan

open AlgebraicCurve

noncomputable section

/-! ## ZONE A — [h1] the invariance is an `H¹` invariance -/

/-- The `K`-dimension of `H¹(0)` on the two sides agrees: the genus equality of SET 10, unfolded
through the definition of `genusFF`. -/
theorem zone_h1_finrank_eq (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
    [IsScalarTower K K' F'] [IsScalarTower K F F'] [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    Module.finrank K (H1 (K := K) (F := F) (0 : Divisor K F))
      = Module.finrank K' (H1 (K := K') (F := F') (0 : Divisor K' F')) := by
  have h := genusFF_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen
  simpa only [genusFF] using h.symm

/-! ## ZONE B — [ell] `ell` and `genusFF` are invariant at the same `lift` -/

/-- SET 9's `ell` invariance and SET 10's genus invariance, at the same divisor and lift. -/
theorem zone_ell_and_genus (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
    [IsScalarTower K K' F'] [IsScalarTower K F F'] [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (D : Divisor K F) [FiniteDimensional K ↥(riemannRochSpace D)]
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) :
    ell (K := K') (D.mapDomain lift) = ell (K := K) D ∧ genusFF K' F' = genusFF K F :=
  ⟨ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen lift
      hlift_ord hlift_inj hlift_new D,
    genusFF_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen⟩

end
