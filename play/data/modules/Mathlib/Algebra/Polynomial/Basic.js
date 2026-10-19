window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Basic"] = {
  "module": "Mathlib.Algebra.Polynomial.Basic",
  "cards": {
    "Polynomial": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":67,"column":0},"end":{"line":75,"column":34}},
      "name": "Polynomial",
      "module": "Mathlib.Algebra.Polynomial.Basic",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_1) → [Semiring R] → Type u_1",
      "doc": "`Polynomial R` is the type of univariate polynomials over `R`,\ndenoted as `R[X]` within the `Polynomial` namespace.\n\nPolynomials should be seen as (semi-)rings with the additional constructor `X`.\nThe embedding from `R` is called `C`. ",
      "short": "Polynomial",
      "signature_source": "@[wikidata Q43260]\nstructure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::\n  /-- The coefficients `ℕ →₀ R` of a polynomial in `R[X]`. -/\n  toFinsupp : AddMonoidAlgebra R ℕ",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "Polynomial.C": {
      "seed": true,
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.module","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.monomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":429,"column":0},"end":{"line":436,"column":26}},
      "name": "Polynomial.C",
      "module": "Mathlib.Algebra.Polynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → R →+* Polynomial R",
      "doc": "`C a` is the constant polynomial `a`.\n`C` is provided as a ring homomorphism.\n",
      "short": "C",
      "signature_source": "def C : R →+* R[X] :=",
      "body_source": "{ monomial 0 with\n    map_one' := by simp [monomial_zero_one]\n    map_mul' := by simp [monomial_mul_monomial]\n    map_zero' := by simp }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "Polynomial.X": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":478,"column":0},"end":{"line":480,"column":14}},
      "name": "Polynomial.X",
      "module": "Mathlib.Algebra.Polynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → Polynomial R",
      "doc": "`X` is the polynomial variable (aka indeterminate). ",
      "short": "X",
      "signature_source": "def X : R[X] :=",
      "body_source": "monomial 1 1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "Polynomial.module": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":286,"column":0},"end":{"line":288,"column":38}},
      "name": "Polynomial.module",
      "module": "Mathlib.Algebra.Polynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  [inst : Semiring R] → {S : Type u_1} → [inst_1 : Semiring S] → [_root_.Module S R] → _root_.Module S (Polynomial R)",
      "doc": "",
      "short": "module",
      "signature_source": "instance module {S} [Semiring S] [Module S R] : Module S R[X] :=",
      "body_source": "fast_instance% Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩\n    toFinsupp_injective toFinsupp_smul",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "Polynomial.monomial": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":378,"column":0},"end":{"line":382,"column":45}},
      "name": "Polynomial.monomial",
      "module": "Mathlib.Algebra.Polynomial.Basic",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → ℕ → R →ₗ[R] Polynomial R",
      "doc": "`monomial s a` is the monomial `a * X^s` ",
      "short": "monomial",
      "signature_source": "def monomial (n : ℕ) : R →ₗ[R] R[X] where\n  toFun t := ⟨.single n t⟩\n  map_add' x y := by simp [← ofFinsupp_add]\n  map_smul' r x := by simp [← ofFinsupp_smul]",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
