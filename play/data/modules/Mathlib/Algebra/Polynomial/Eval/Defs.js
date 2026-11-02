window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Polynomial.Eval.Defs"] = {
  "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
  "cards": {
    "Polynomial.eval": {
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":249,"column":0},"end":{"line":251,"column":26}},
      "name": "Polynomial.eval",
      "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : Semiring R] → R → Polynomial R → R",
      "doc": "`eval x p` is the evaluation of the polynomial `p` at `x` ",
      "short": "eval",
      "signature_source": "def eval (x : R) (p : R[X]) : R :=",
      "body_source": "eval₂ (RingHom.id _) x p",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Polynomial.eval₂": {
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":55,"column":0},"end":{"line":58,"column":30}},
      "name": "Polynomial.eval₂",
      "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → {S : Type u_2} → [inst : Semiring R] → [inst_1 : Semiring S] → (R →+* S) → S → Polynomial R → S",
      "doc": "Evaluate a polynomial `p` given a ring hom `f` from the scalar ring\nto the target and a value `x` for the variable in the target ",
      "short": "eval₂",
      "signature_source": "",
      "body_source": "",
      "source_file": null,
      "has_source": false,
      "source_note": "generated declaration or structure field; no standalone source declaration",
      "has_refs": true
    },
    "Polynomial.eval₂RingHom": {
      "refs": [{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"AddMonoidHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.eval₂AddMonoidHom","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"Polynomial.eval₂_mul","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"theorem"}],
      "range": {"start":{"line":212,"column":0},"end":{"line":216,"column":42}},
      "name": "Polynomial.eval₂RingHom",
      "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} → {S : Type v} → [inst : Semiring R] → [inst_1 : CommSemiring S] → (R →+* S) → S → Polynomial R →+* S",
      "doc": "`eval₂` as a `RingHom` ",
      "short": "eval₂RingHom",
      "signature_source": "def eval₂RingHom (f : R →+* S) (x : S) : R[X] →+* S :=",
      "body_source": "{ eval₂AddMonoidHom f x with\n    map_one' := eval₂_one _ _\n    map_mul' := fun _ _ => eval₂_mul _ _ }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Polynomial.eval₂_eq_eval_map": {
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.eval","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":565,"column":0},"end":{"line":568,"column":24}},
      "name": "Polynomial.eval₂_eq_eval_map",
      "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {S : Type v} [inst : Semiring R] {p : Polynomial R} [inst_1 : Semiring S] (f : R →+* S) {x : S},\n  Polynomial.eval₂ f x p = Polynomial.eval x (Polynomial.map f p)",
      "doc": "",
      "short": "eval₂_eq_eval_map",
      "signature_source": "theorem eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x :=",
      "body_source": "by\n  induction p using Polynomial.induction_on' with\n  | add p q hp hq => simp [hp, hq]\n  | monomial n r => simp",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean",
      "has_source": true,
      "has_refs": true
    },
    "Polynomial.map": {
      "refs": [{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Polynomial.C","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.X","module":"Mathlib.Algebra.Polynomial.Basic","kind":"def"},{"where":"body","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"RingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":493,"column":0},"end":{"line":495,"column":20}},
      "name": "Polynomial.map",
      "module": "Mathlib.Algebra.Polynomial.Eval.Defs",
      "kind": "def",
      "elaborated_type": "{R : Type u} → {S : Type v} → [inst : Semiring R] → [inst_1 : Semiring S] → (R →+* S) → Polynomial R → Polynomial S",
      "doc": "`map f p` maps a polynomial `p` across a ring hom `f` ",
      "short": "map",
      "signature_source": "def map : R[X] → S[X] :=",
      "body_source": "eval₂ (C.comp f) X",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
