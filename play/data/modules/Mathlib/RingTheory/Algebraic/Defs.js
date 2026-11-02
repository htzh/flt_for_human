window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Algebraic.Defs"] = {
  "module": "Mathlib.RingTheory.Algebraic.Defs",
  "cards": {
    "Transcendental": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"IsAlgebraic","module":"Mathlib.RingTheory.Algebraic.Defs","kind":"def"}],
      "range": {"start":{"line":48,"column":0},"end":{"line":50,"column":18}},
      "name": "Transcendental",
      "module": "Mathlib.RingTheory.Algebraic.Defs",
      "kind": "def",
      "elaborated_type": "(R : Type u) → {A : Type v} → [inst : CommRing R] → [inst_1 : Ring A] → [Algebra R A] → A → Prop",
      "doc": "An element of an R-algebra is transcendental over R if it is not algebraic over R. ",
      "short": "Transcendental",
      "signature_source": "def Transcendental (x : A) : Prop :=",
      "body_source": "¬IsAlgebraic R x",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Defs.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
