window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Init.Data.Rat.Basic"] = {
  "module": "Init.Data.Rat.Basic",
  "cards": {
    "Rat": {
      "refs": [],
      "range": {"start":{"line":27,"column":0},"end":{"line":45,"column":32}},
      "name": "Rat",
      "module": "Init.Data.Rat.Basic",
      "kind": "inductive",
      "elaborated_type": "Type",
      "doc": "Rational numbers, implemented as a pair of integers `num / den` such that the\ndenominator is positive and the numerator and denominator are coprime.\n",
      "short": "Rat",
      "signature_source": "-- `Rat` is not tagged with the `ext` attribute, since this is more often than not undesirable\n@[suggest_for ℚ]\nstructure Rat where\n  /-- Constructs a rational number from components.\n  We rename the constructor to `mk'` to avoid a clash with the smart constructor. -/\n  mk' ::\n  /-- The numerator of the rational number is an integer. -/\n  num : Int\n  /-- The denominator of the rational number is a natural number. -/\n  den : Nat := 1\n  /-- The denominator is nonzero. -/\n  den_nz : den ≠ 0 := by decide\n  /-- The numerator and denominator are coprime: it is in \"reduced form\". -/\n  reduced : num.natAbs.Coprime den := by decide\n  deriving DecidableEq, Hashable",
      "body_source": "",
      "source_file": "~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Rat/Basic.lean",
      "has_source": true,
      "has_refs": false
    }
  }
};
