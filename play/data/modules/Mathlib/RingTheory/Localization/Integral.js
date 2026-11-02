window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Localization.Integral"] = {
  "module": "Mathlib.RingTheory.Localization.Integral",
  "cards": {
    "IsLocalization.integerNormalization": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsLocalization","module":"Mathlib.RingTheory.Localization.Defs","kind":"abbrev"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Submonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"Finset","module":"Mathlib.Data.Finset.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"body","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"Polynomial.support","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"_private.Mathlib.RingTheory.Localization.Integral.0.IsLocalization.exists_integer_polynomial_multiple_and_support_subset","module":"Mathlib.RingTheory.Localization.Integral","kind":"theorem"},{"where":"body","name":"Exists.choose","module":"Init.Classical","kind":"def"},{"where":"body","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":48,"column":0},"end":{"line":51,"column":82}},
      "name": "IsLocalization.integerNormalization",
      "module": "Mathlib.RingTheory.Localization.Integral",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  [inst : CommRing R] →\n    (M : Submonoid R) →\n      {S : Type u_2} →\n        [inst_1 : CommRing S] → [inst_2 : Algebra R S] → [IsLocalization M S] → Polynomial S → Polynomial R",
      "doc": "`integerNormalization p` normalizes `p` to have integer coefficients\nby clearing the denominators ",
      "short": "integerNormalization",
      "signature_source": "@[no_expose] noncomputable def integerNormalization (p : S[X]) : R[X] :=",
      "body_source": "(exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Integral.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsLocalization.integerNormalization_spec": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsLocalization","module":"Mathlib.RingTheory.Localization.Defs","kind":"abbrev"},{"where":"type","name":"IsLocalization.integerNormalization","module":"Mathlib.RingTheory.Localization.Integral","kind":"def"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Submonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":53,"column":0},"end":{"line":56,"column":60}},
      "name": "IsLocalization.integerNormalization_spec",
      "module": "Mathlib.RingTheory.Localization.Integral",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (M : Submonoid R) {S : Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S]\n  [inst_3 : IsLocalization M S] (p : Polynomial S),\n  ∃ b ∈ M, Polynomial.map (algebraMap R S) (IsLocalization.integerNormalization M p) = b • p",
      "doc": "",
      "short": "integerNormalization_spec",
      "signature_source": "theorem integerNormalization_spec (p : S[X]) :\n    ∃ b ∈ M, (integerNormalization M p).map (algebraMap R S) = b • p :=",
      "body_source": "let e := exists_integer_polynomial_multiple_and_support_subset M p\n  ⟨e.choose, e.choose_spec.1, e.choose_spec.2.choose_spec.1⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Integral.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
