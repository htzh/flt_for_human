window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Trace.Defs"] = {
  "module": "Mathlib.RingTheory.Trace.Defs",
  "cards": {
    "Algebra.trace": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"Algebra.lmul","module":"Mathlib.Algebra.Algebra.Bilinear","kind":"def"},{"where":"body","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"LinearMap.comp","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"LinearMap.trace","module":"Mathlib.LinearAlgebra.Trace","kind":"def"},{"where":"body","name":"Module.End","module":"Mathlib.Algebra.Module.LinearMap.End","kind":"abbrev"}],
      "range": {"start":{"line":68,"column":0},"end":{"line":72,"column":51}},
      "name": "Algebra.trace",
      "module": "Mathlib.RingTheory.Trace.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) → (S : Type u_2) → [inst : CommRing R] → [inst_1 : CommRing S] → [inst_2 : Algebra R S] → S →ₗ[R] R",
      "doc": "The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,\nas an `R`-linear map. ",
      "short": "trace",
      "signature_source": "@[stacks 0BIF \"Trace\"]\nnoncomputable def trace : S →ₗ[R] R :=",
      "body_source": "(LinearMap.trace R S).comp (lmul R S).toLinearMap",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Trace/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
