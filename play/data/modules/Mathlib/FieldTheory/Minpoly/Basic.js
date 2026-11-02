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
    },
    "minpoly.aeval": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.aeval","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"minpoly","module":"Mathlib.FieldTheory.Minpoly.Basic","kind":"def"}],
      "range": {"start":{"line":87,"column":0},"end":{"line":93,"column":22}},
      "name": "minpoly.aeval",
      "module": "Mathlib.FieldTheory.Minpoly.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ (A : Type u_1) {B : Type u_2} [inst : CommRing A] [inst_1 : Ring B] [inst_2 : Algebra A B] (x : B),\n  (Polynomial.aeval x) (minpoly A x) = 0",
      "doc": "An element is a root of its minimal polynomial. ",
      "short": "aeval",
      "signature_source": "@[simp]\ntheorem aeval : aeval x (minpoly A x) = 0 :=",
      "body_source": "by\n  delta minpoly\n  split_ifs with hx\n  · exact (degree_lt_wf.min_mem _ hx).2\n  · exact aeval_zero _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "minpoly.irreducible": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Irreducible","module":"Mathlib.Algebra.Group.Irreducible.Defs","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"minpoly","module":"Mathlib.FieldTheory.Minpoly.Basic","kind":"def"}],
      "range": {"start":{"line":268,"column":0},"end":{"line":278,"column":21}},
      "name": "minpoly.irreducible",
      "module": "Mathlib.FieldTheory.Minpoly.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : Ring B] [inst_2 : Algebra A B] {x : B} [IsDomain A]\n  [IsDomain B], IsIntegral A x → Irreducible (minpoly A x)",
      "doc": "A minimal polynomial is irreducible. ",
      "short": "irreducible",
      "signature_source": "theorem irreducible (hx : IsIntegral A x) : Irreducible (minpoly A x) :=",
      "body_source": "by\n  refine (irreducible_of_monic (monic hx) <| ne_one A x).2 fun f g hf hg he => ?_\n  rw [← hf.isUnit_iff, ← hg.isUnit_iff]\n  by_contra! h\n  have heval := congr_arg (Polynomial.aeval x) he\n  rw [aeval A x, aeval_mul, mul_eq_zero] at heval\n  rcases heval with heval | heval\n  · exact aeval_ne_zero_of_dvdNotUnit_minpoly hx hf ⟨hf.ne_zero, g, h.2, he.symm⟩ heval\n  · refine aeval_ne_zero_of_dvdNotUnit_minpoly hx hg ⟨hg.ne_zero, f, h.1, ?_⟩ heval\n    rw [mul_comm, he]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "minpoly.monic": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"Polynomial.Monic","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"minpoly","module":"Mathlib.FieldTheory.Minpoly.Basic","kind":"def"}],
      "range": {"start":{"line":53,"column":0},"end":{"line":57,"column":37}},
      "name": "minpoly.monic",
      "module": "Mathlib.FieldTheory.Minpoly.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : Ring B] [inst_2 : Algebra A B] {x : B},\n  IsIntegral A x → (minpoly A x).Monic",
      "doc": "A minimal polynomial is monic. ",
      "short": "monic",
      "signature_source": "theorem monic (hx : IsIntegral A x) : Monic (minpoly A x) :=",
      "body_source": "by\n  delta minpoly\n  rw [dite_eq_left hx]\n  exact (degree_lt_wf.min_mem _ hx).1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
