window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.LinearAlgebra.Basis.Defs"] = {
  "module": "Mathlib.LinearAlgebra.Basis.Defs",
  "cards": {
    "Module.Basis": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":82,"column":0},"end":{"line":95,"column":25}},
      "name": "Module.Basis",
      "module": "Mathlib.LinearAlgebra.Basis.Defs",
      "kind": "inductive",
      "elaborated_type": "Type u_1 →\n  (R : Type u_3) →\n    (M : Type u_4) →\n      [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max (max u_1 u_3) u_4)",
      "doc": "A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.\n\nThe basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`.\nTo turn a linear independent family of vectors spanning `M` into a basis, use `Basis.mk`.\nThey are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,\navailable as `Basis.repr`.\n",
      "short": "Basis",
      "signature_source": "@[wikidata Q189569]\nstructure Basis where\n  /-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/\n  ofRepr ::\n    /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:\n    the `c`s such that `x = ∑ i, c i`. -/\n    repr : M ≃ₗ[R] ι →₀ R",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Module.Basis.map": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"LinearEquiv","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Module.Basis","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomInvPair.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"body","name":"Finsupp.module","module":"Mathlib.Data.Finsupp.SMul","kind":"def"},{"where":"body","name":"LinearEquiv.symm","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"def"},{"where":"body","name":"LinearEquiv.trans","module":"Mathlib.Algebra.Module.Equiv.Defs","kind":"def"},{"where":"body","name":"Module.Basis.repr","module":"Mathlib.LinearAlgebra.Basis.Defs","kind":"abbrev"}],
      "range": {"start":{"line":167,"column":0},"end":{"line":170,"column":30}},
      "name": "Module.Basis.map",
      "module": "Mathlib.LinearAlgebra.Basis.Defs",
      "kind": "def",
      "elaborated_type": "{ι : Type u_1} →\n  {R : Type u_3} →\n    {M : Type u_4} →\n      {M' : Type u_5} →\n        [inst : Semiring R] →\n          [inst_1 : AddCommMonoid M] →\n            [inst_2 : _root_.Module R M] →\n              [inst_3 : AddCommMonoid M'] →\n                [inst_4 : _root_.Module R M'] → Module.Basis ι R M → (M ≃ₗ[R] M') → Module.Basis ι R M'",
      "doc": "Apply the linear equivalence `f` to the basis vectors. ",
      "short": "map",
      "signature_source": "@[simps]\nprotected def map : Basis ι R M' :=",
      "body_source": "ofRepr (f.symm.trans b.repr)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
