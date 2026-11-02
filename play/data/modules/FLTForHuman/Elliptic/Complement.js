window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.Elliptic.Complement"] = {
  "module": "FLTForHuman.Elliptic.Complement",
  "cards": {
    "FLTForHuman.Elliptic.normEDS_mul_complEDS": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"complEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":90,"column":0},"end":{"line":98,"column":44}},
      "name": "FLTForHuman.Elliptic.normEDS_mul_complEDS",
      "module": "FLTForHuman.Elliptic.Complement",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m n : ℤ), normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m)",
      "doc": "The complement `complEDS` witnesses `normEDS m ∣ normEDS (n * m)`. ",
      "short": "normEDS_mul_complEDS",
      "signature_source": "theorem normEDS_mul_complEDS (b c d : R) (m n : ℤ) :\n    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) :=",
      "body_source": "by\n  obtain rfl | hm := eq_or_ne m 0\n  · simp\n  · rw [normEDS_eq_aeval (b := b) (c := c) (d := d),\n      complEDS_eq_aeval (b := b) (c := c) (d := d), ← map_mul]\n    congr 1\n    exact universalNormEDS_mul_complEDS hm n",
      "source_file": "lean/FLTForHuman/Elliptic/Complement.lean",
      "has_source": true,
      "has_refs": true
    },
    "FLTForHuman.Elliptic.normEDS_mul_complEDS_div": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"complEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":100,"column":0},"end":{"line":103,"column":68}},
      "name": "FLTForHuman.Elliptic.normEDS_mul_complEDS_div",
      "module": "FLTForHuman.Elliptic.Complement",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  m ≠ 0 → ∀ (n : ℤ), m ∣ n → normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n",
      "doc": "",
      "short": "normEDS_mul_complEDS_div",
      "signature_source": "lemma normEDS_mul_complEDS_div (b c d : R) (m : ℤ) (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :\n    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n :=",
      "body_source": "by\n  obtain ⟨n, rfl⟩ := dvd\n  rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]",
      "source_file": "lean/FLTForHuman/Elliptic/Complement.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
