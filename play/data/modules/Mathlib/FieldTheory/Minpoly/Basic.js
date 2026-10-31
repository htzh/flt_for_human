window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.Minpoly.Basic"] = {
  "module": "Mathlib.FieldTheory.Minpoly.Basic",
  "cards": {
    "minpoly": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"body","name":"Polynomial.Monic","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"body","name":"Polynomial.degree","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"body","name":"Polynomial.eval₂","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"WellFounded.min","module":"Mathlib.Order.WellFounded","kind":"def"},{"where":"body","name":"WithBot","module":"Mathlib.Order.TypeTags","kind":"def"},{"where":"body","name":"Classical.propDecidable","module":"Init.Classical","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":31,"column":0},"end":{"line":42,"column":58}},
      "name": "minpoly",
      "module": "Mathlib.FieldTheory.Minpoly.Basic",
      "kind": "def",
      "elaborated_type": "(A : Type u_1) → {B : Type u_2} → [inst : CommRing A] → [inst_1 : Ring B] → [Algebra A B] → B → Polynomial A",
      "doc": "Suppose `x : B`, where `B` is an `A`-algebra.\n\nThe minimal polynomial `minpoly A x` of `x`\nis a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,\nif such exists (`IsIntegral A x`) or zero otherwise.\n\nFor example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then\nthe minimal polynomial of `f` is `minpoly 𝕜 f`.\n",
      "short": "minpoly",
      "signature_source": "@[stacks 09GM]\nnoncomputable def minpoly (x : B) : A[X] :=",
      "body_source": "if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
