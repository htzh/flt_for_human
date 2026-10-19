window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.LinearMap.Defs"] = {
  "module": "Mathlib.Algebra.Module.LinearMap.Defs",
  "cards": {
    "LinearMap": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":79,"column":0},"end":{"line":87,"column":36}},
      "name": "LinearMap",
      "module": "Mathlib.Algebra.Module.LinearMap.Defs",
      "kind": "inductive",
      "elaborated_type": "{R : Type u_14} →\n  {S : Type u_15} →\n    [inst : Semiring R] →\n      [inst_1 : Semiring S] →\n        (R →+* S) →\n          (M : Type u_16) →\n            (M₂ : Type u_17) →\n              [inst_2 : AddCommMonoid M] →\n                [inst_3 : AddCommMonoid M₂] → [_root_.Module R M] → [_root_.Module S M₂] → Type (max u_16 u_17)",
      "doc": "A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`\nis semilinear if it satisfies the two properties `f (x + y) = f x + f y` and\n`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation\n`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which\n`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear\nmaps is available with the predicate `IsLinearMap`, but it should be avoided most of the time. ",
      "short": "LinearMap",
      "signature_source": "structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)\n    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends\n    AddHom M M₂, MulActionHom σ M M₂",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    }
  }
};
