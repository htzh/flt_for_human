window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Localization.FractionRing"] = {
  "module": "Mathlib.RingTheory.Localization.FractionRing",
  "cards": {
    "IsFractionRing.algEquivOfAlgEquiv": {
      "refs": [{"where":"type","name":"AlgEquiv","module":"Mathlib.Algebra.Algebra.Equiv","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsFractionRing","module":"Mathlib.RingTheory.Localization.FractionRing","kind":"abbrev"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"body","name":"IsLocalization.algEquivOfAlgEquiv","module":"Mathlib.RingTheory.Localization.Basic","kind":"def"},{"where":"body","name":"nonZeroDivisors","module":"Mathlib.Algebra.GroupWithZero.NonZeroDivisors","kind":"def"}],
      "range": {"start":{"line":532,"column":0},"end":{"line":536,"column":79}},
      "name": "IsFractionRing.algEquivOfAlgEquiv",
      "module": "Mathlib.RingTheory.Localization.FractionRing",
      "kind": "def",
      "elaborated_type": "{R : Type u_8} →\n  {A : Type u_9} →\n    {K : Type u_10} →\n      {B : Type u_11} →\n        {L : Type u_12} →\n          [inst : CommSemiring R] →\n            [inst_1 : CommRing A] →\n              [inst_2 : CommRing B] →\n                [inst_3 : CommRing K] →\n                  [inst_4 : CommRing L] →\n                    [inst_5 : Algebra R A] →\n                      [inst_6 : Algebra R K] →\n                        [inst_7 : Algebra A K] →\n                          [IsFractionRing A K] →\n                            [IsScalarTower R A K] →\n                              [inst_10 : Algebra R B] →\n                                [inst_11 : Algebra R L] →\n                                  [inst_12 : Algebra B L] →\n                                    [IsFractionRing B L] → [IsScalarTower R B L] → (A ≃ₐ[R] B) → K ≃ₐ[R] L",
      "doc": "Given `R`-algebras `A, B` and localization maps to their fraction rings\n`f : A →ₐ[R] K, g : B →ₐ[R] L`, an isomorphism `h : A ≃ₐ[R] B` induces an isomorphism of\nfraction rings `K ≃ₐ[R] L`. ",
      "short": "algEquivOfAlgEquiv",
      "signature_source": "noncomputable def algEquivOfAlgEquiv : K ≃ₐ[R] L :=",
      "body_source": "IsLocalization.algEquivOfAlgEquiv K L h (MulEquivClass.map_nonZeroDivisors h)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
