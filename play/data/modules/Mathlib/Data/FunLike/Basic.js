window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.FunLike.Basic"] = {
  "module": "Mathlib.Data.FunLike.Basic",
  "cards": {
    "FunLike": {
      "refs": [{"where":"body","name":"DFunLike","module":"Mathlib.Data.FunLike.Basic","kind":"inductive"}],
      "range": {"start":{"line":153,"column":0},"end":{"line":159,"column":47}},
      "name": "FunLike",
      "module": "Mathlib.Data.FunLike.Basic",
      "kind": "abbrev",
      "elaborated_type": "Sort u_1 → Sort u_2 → Sort u_3 → Sort (max (max (max 1 u_1) u_2) u_3)",
      "doc": "The class `FunLike F α β` (`Fun`ction-`Like`) expresses that terms of type `F`\nhave an injective coercion to functions from `α` to `β`.\n`FunLike` is the non-dependent version of `DFunLike`.\nThis typeclass is used in the definition of the homomorphism typeclasses,\nsuch as `ZeroHomClass`, `MulHomClass`, `MonoidHomClass`, ....\n",
      "short": "FunLike",
      "signature_source": "abbrev FunLike F α β :=",
      "body_source": "DFunLike F α fun _ => β",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/FunLike/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
