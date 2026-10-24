window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.Elliptic.EDS"] = {
  "module": "FLTForHuman.Elliptic.EDS",
  "cards": {
    "FLTForHuman.Elliptic.Param": {
      "refs": [],
      "range": {"start":{"line":38,"column":0},"end":{"line":42,"column":13}},
      "name": "FLTForHuman.Elliptic.Param",
      "module": "FLTForHuman.Elliptic.EDS",
      "kind": "inductive",
      "elaborated_type": "Type",
      "doc": "The three parameters of a normalised EDS, as indeterminates. ",
      "short": "Param",
      "signature_source": "inductive Param : Type\n  | B : Param\n  | C : Param\n  | D : Param",
      "body_source": "",
      "source_file": "lean/FLTForHuman/Elliptic/EDS.lean",
      "has_source": true,
      "has_refs": false
    },
    "FLTForHuman.Elliptic.normEDS_eq_aeval": {
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.Param","module":"FLTForHuman.Elliptic.EDS","kind":"inductive"},{"where":"type","name":"FLTForHuman.Elliptic.universalNormEDS","module":"FLTForHuman.Elliptic.EDS","kind":"def"},{"where":"type","name":"AddMonoidAlgebra.algebra","module":"Mathlib.Algebra.MonoidAlgebra.Basic","kind":"def"},{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"type","name":"MvPolynomial","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"abbrev"},{"where":"type","name":"MvPolynomial.aeval","module":"Mathlib.Algebra.MvPolynomial.Eval","kind":"def"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":50,"column":0},"end":{"line":53,"column":63}},
      "name": "FLTForHuman.Elliptic.normEDS_eq_aeval",
      "module": "FLTForHuman.Elliptic.EDS",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R),\n  normEDS b c d = fun x =>\n    (MvPolynomial.aeval fun t => FLTForHuman.Elliptic.Param.rec b c d t) (FLTForHuman.Elliptic.universalNormEDS x)",
      "doc": "Specialising the universal EDS recovers `normEDS b c d`. ",
      "short": "normEDS_eq_aeval",
      "signature_source": "lemma normEDS_eq_aeval (b c d : R) :\n    normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) :=",
      "body_source": "by\n  simp_rw [universalNormEDS, map_normEDS, MvPolynomial.aeval_X]",
      "source_file": "lean/FLTForHuman/Elliptic/EDS.lean",
      "has_source": true,
      "has_refs": true
    },
    "FLTForHuman.Elliptic.universalNormEDS": {
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.Param","module":"FLTForHuman.Elliptic.EDS","kind":"inductive"},{"where":"type","name":"MvPolynomial","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"abbrev"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Finsupp","module":"Mathlib.Data.Finsupp.Defs","kind":"inductive"},{"where":"body","name":"MvPolynomial.X","module":"Mathlib.Algebra.MvPolynomial.Basic","kind":"def"},{"where":"body","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":46,"column":0},"end":{"line":48,"column":45}},
      "name": "FLTForHuman.Elliptic.universalNormEDS",
      "module": "FLTForHuman.Elliptic.EDS",
      "kind": "def",
      "elaborated_type": "ℤ → MvPolynomial FLTForHuman.Elliptic.Param ℤ",
      "doc": "The universal normalised EDS over `ℤ[B, C, D]`. ",
      "short": "universalNormEDS",
      "signature_source": "noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ :=",
      "body_source": "normEDS (X Param.B) (X Param.C) (X Param.D)",
      "source_file": "lean/FLTForHuman/Elliptic/EDS.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
