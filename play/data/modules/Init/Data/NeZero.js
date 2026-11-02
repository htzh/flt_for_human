window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.NeZero"] = {
  "module": "Init.Data.NeZero",
  "cards": {
    "NeZero": {
      "refs": [{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":28,"column":0},"end":{"line":31,"column":13}},
      "name": "NeZero",
      "module": "Init.Data.NeZero",
      "kind": "inductive",
      "elaborated_type": "{R : Type u_1} → [Zero R] → R → Prop",
      "doc": "A type-class version of `n ≠ 0`.  ",
      "short": "NeZero",
      "signature_source": "class NeZero (n : R) : Prop where\n  /-- The proposition that `n` is not zero. -/\n  out : n ≠ 0",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/NeZero.lean",
      "has_source": true,
      "has_refs": true
    },
    "NeZero.ne": {
      "refs": [{"where":"type","name":"Ne","module":"Init.Core","kind":"def"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":33,"column":0},"end":{"line":34,"column":7}},
      "name": "NeZero.ne",
      "module": "Init.Data.NeZero",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 0",
      "doc": "",
      "short": "ne",
      "signature_source": "theorem NeZero.ne (n : R) [h : NeZero n] : n ≠ 0 :=",
      "body_source": "h.out",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/NeZero.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
