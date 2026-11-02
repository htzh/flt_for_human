window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Group.Action.Pi"] = {
  "module": "Mathlib.Algebra.Group.Action.Pi",
  "cards": {
    "Pi.isScalarTower": {
      "refs": [{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"SMul","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":44,"column":0},"end":{"line":47,"column":57}},
      "name": "Pi.isScalarTower",
      "module": "Mathlib.Algebra.Group.Action.Pi",
      "kind": "theorem",
      "elaborated_type": "∀ {ι : Type u_1} {M : Type u_2} {N : Type u_3} {α : ι → Type u_4} [inst : SMul M N] [inst_1 : (i : ι) → SMul N (α i)]\n  [inst_2 : (i : ι) → SMul M (α i)] [∀ (i : ι), IsScalarTower M N (α i)], IsScalarTower M N ((i : ι) → α i)",
      "doc": "",
      "short": "isScalarTower",
      "signature_source": "@[to_additive]\ninstance isScalarTower [SMul M N] [∀ i, SMul N (α i)] [∀ i, SMul M (α i)]\n    [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (∀ i, α i) where\n  smul_assoc x y z := funext fun i ↦ smul_assoc x y (z i)",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Pi.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
