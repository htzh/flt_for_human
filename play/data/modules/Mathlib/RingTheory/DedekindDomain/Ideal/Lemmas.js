window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas"] = {
  "module": "Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas",
  "cards": {
    "IsDedekindDomain.HeightOneSpectrum": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":490,"column":0},"end":{"line":496,"column":22}},
      "name": "IsDedekindDomain.HeightOneSpectrum",
      "module": "Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_1) → [CommRing R] → Type u_1",
      "doc": "The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of\n`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. ",
      "short": "HeightOneSpectrum",
      "signature_source": "@[ext, nolint unusedArguments]\nstructure HeightOneSpectrum where\n  asIdeal : Ideal R\n  isPrime : asIdeal.IsPrime\n  ne_bot : asIdeal ≠ ⊥",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
