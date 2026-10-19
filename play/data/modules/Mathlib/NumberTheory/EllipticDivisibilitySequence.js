window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.NumberTheory.EllipticDivisibilitySequence"] = {
  "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
  "cards": {
    "IsEllipticDvdSequence": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"IsDvdSequence","module":"Mathlib.Data.Nat.DvdSequence","kind":"def"},{"where":"body","name":"IsEllipticSequence","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"semigroupDvd","module":"Mathlib.Algebra.Divisibility.Basic","kind":"def"}],
      "range": {"start":{"line":313,"column":0},"end":{"line":315,"column":40}},
      "name": "IsEllipticDvdSequence",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → Prop",
      "doc": "The proposition that a sequence indexed by `ℤ` is an EDS. ",
      "short": "IsEllipticDvdSequence",
      "signature_source": "def IsEllipticDvdSequence : Prop :=",
      "body_source": "IsEllipticSequence W ∧ IsDvdSequence W",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "IsEllipticNet": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"IsEllipticNet.rel","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"}],
      "range": {"start":{"line":303,"column":0},"end":{"line":305,"column":48}},
      "name": "IsEllipticNet",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → Prop",
      "doc": "The proposition that a sequence indexed by `ℤ` is an elliptic net. ",
      "short": "IsEllipticNet",
      "signature_source": "def IsEllipticNet : Prop :=",
      "body_source": "∀ p q r s : ℤ, IsEllipticNet.rel W p q r s = 0",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "IsEllipticNet.atom": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Int.tdiv","module":"Init.Data.Int.DivMod.Basic","kind":"def"}],
      "range": {"start":{"line":106,"column":0},"end":{"line":109,"column":41}},
      "name": "IsEllipticNet.atom",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → ℤ → ℤ → R",
      "doc": "The elliptic atom `Wₐ(a, b)` that defines an elliptic net. Note that this is defined in terms of\ntruncated integer division, and hence should only be used when `a` and `b` have the same parity. ",
      "short": "atom",
      "signature_source": "def atom (a b : ℤ) : R :=",
      "body_source": "W ((a + b).tdiv 2) * W ((a - b).tdiv 2)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "IsEllipticNet.atomRel": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"IsEllipticNet.atom","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"}],
      "range": {"start":{"line":154,"column":0},"end":{"line":158,"column":77}},
      "name": "IsEllipticNet.atomRel",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → ℤ → ℤ → ℤ → ℤ → R",
      "doc": "The elliptic relator `ERₐ(a, b, c, d)` obtained by a change of variables in `ER(p, q, r, s)`\n(see `IsEllipticNet.rel_eq` and `IsEllipticNet.atomRel_eq`). Note that this is defined in terms of\nelliptic atoms, and hence should only be used when `a`, `b`, `c`, and `d` have the same parity. ",
      "short": "atomRel",
      "signature_source": "def atomRel (a b c d : ℤ) : R :=",
      "body_source": "atom W a b * atom W c d - atom W a c * atom W b d + atom W a d * atom W b c",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "IsEllipticNet.atomRel_eq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsEllipticNet.atomRel","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"IsEllipticNet.rel","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"HMod.hMod","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"List.Pairwise","module":"Init.Data.List.Basic","kind":"inductive"}],
      "range": {"start":{"line":279,"column":0},"end":{"line":281,"column":16}},
      "name": "IsEllipticNet.atomRel_eq",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (W : ℤ → R) {a b c d : ℤ},\n  List.Pairwise (fun x1 x2 => x1 % 2 = x2 % 2) [a, b, c, d] →\n    IsEllipticNet.atomRel W a b c d = IsEllipticNet.rel W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d",
      "doc": "",
      "short": "atomRel_eq",
      "signature_source": "lemma atomRel_eq {a b c d : ℤ} (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) :\n    atomRel W a b c d = rel W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d :=",
      "body_source": "by\n  grind [rel_eq]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "IsEllipticNet.rel": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":265,"column":0},"end":{"line":268,"column":47}},
      "name": "IsEllipticNet.rel",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → ℤ → ℤ → ℤ → ℤ → R",
      "doc": "The elliptic relator `ER(p, q, r, s)` that defines an elliptic net. ",
      "short": "rel",
      "signature_source": "def rel (p q r s : ℤ) : R :=",
      "body_source": "W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q +\n    W (q + r + s) * W (q - r) * W (p + s) * W p",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "IsEllipticNet.rel_eq": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsEllipticNet.atomRel","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"IsEllipticNet.rel","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":270,"column":0},"end":{"line":273,"column":75}},
      "name": "IsEllipticNet.rel_eq",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (W : ℤ → R) (p q r s : ℤ),\n  IsEllipticNet.rel W p q r s = IsEllipticNet.atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s",
      "doc": "",
      "short": "rel_eq",
      "signature_source": "lemma rel_eq (p q r s : ℤ) : rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s :=",
      "body_source": "by\n  simp_rw [rel, atomRel, atom, add_add_add_comm _ s, add_assoc _ s, ← two_mul, ← mul_add,\n    add_sub_add_comm, add_sub_assoc, sub_self, add_zero, ← mul_sub,\n    Int.mul_tdiv_cancel_left _ two_ne_zero, mul_comm <| _ * W p, mul_assoc]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "IsEllipticSequence": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"IsEllipticNet.rel","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"}],
      "range": {"start":{"line":307,"column":0},"end":{"line":309,"column":46}},
      "name": "IsEllipticSequence",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → (ℤ → R) → Prop",
      "doc": "The proposition that a sequence indexed by `ℤ` is an elliptic sequence. ",
      "short": "IsEllipticSequence",
      "signature_source": "def IsEllipticSequence : Prop :=",
      "body_source": "∀ p q r : ℤ, IsEllipticNet.rel W p q r 0 = 0",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "complEDS": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"complEDS'","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Int.cast","module":"Init.Data.Int.Basic","kind":"def"},{"where":"body","name":"Int.natAbs","module":"Init.Data.Int.Basic","kind":"def"},{"where":"body","name":"Int.sign","module":"Init.Data.Int.Basic","kind":"def"}],
      "range": {"start":{"line":687,"column":0},"end":{"line":692,"column":37}},
      "name": "complEDS",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → ℤ → R",
      "doc": "The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses\n`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ ℤ`.\n\nThis extends `complEDS'` by defining its values at negative integers. ",
      "short": "complEDS",
      "signature_source": "def complEDS (n : ℤ) : R :=",
      "body_source": "n.sign * complEDS' b c d k n.natAbs",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "complEDS'": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":653,"column":0},"end":{"line":664,"column":85}},
      "name": "complEDS'",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → ℕ → R",
      "doc": "The complement sequence `Wᶜ : ℤ × ℕ → R` for a normalised EDS `W : ℤ → R` that witnesses\n`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ ℤ`.\n\nThis is defined in terms of `normEDS` and agrees with `complEDS₂` when `n = 2`. ",
      "short": "complEDS'",
      "signature_source": "def complEDS' : ℕ → R\n  | 0 => 0\n  | 1 => 1\n  | (n + 2) => let m :=",
      "body_source": "n / 2 + 1\n    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else\n      have : m + 1 < n + 2 := by grind\n      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -\n        complEDS' (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "complEDS₂": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"body","name":"preNormEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":498,"column":0},"end":{"line":504,"column":98}},
      "name": "complEDS₂",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → R",
      "doc": "The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses\n`W(k) ∣ W(2 * k)`. In other words, `W(k) * Wᶜ₂(k) = W(2 * k)` for all `k ∈ ℤ`.\n\nThis is defined in terms of `preNormEDS`. ",
      "short": "complEDS₂",
      "signature_source": "def complEDS₂ (k : ℤ) : R :=",
      "body_source": "(preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -\n    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"body","name":"preNormEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":541,"column":0},"end":{"line":546,"column":52}},
      "name": "normEDS",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → R",
      "doc": "The canonical example of a normalised EDS `W : ℤ → R`, with initial values\n`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.\n\nThis is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`. ",
      "short": "normEDS",
      "signature_source": "def normEDS (n : ℤ) : R :=",
      "body_source": "preNormEDS (b ^ 4) c d n * if Even n then b else 1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "normEDS_dvd_normEDS_two_mul": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"semigroupDvd","module":"Mathlib.Algebra.Divisibility.Basic","kind":"def"},{"where":"type","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":582,"column":0},"end":{"line":583,"column":49}},
      "name": "normEDS_dvd_normEDS_two_mul",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ), normEDS b c d k ∣ normEDS b c d (2 * k)",
      "doc": "",
      "short": "normEDS_dvd_normEDS_two_mul",
      "signature_source": "lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=",
      "body_source": "⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_even": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":592,"column":0},"end":{"line":596,"column":7}},
      "name": "normEDS_even",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  normEDS b c d (2 * m) * b =\n    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -\n      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2",
      "doc": "",
      "short": "normEDS_even",
      "signature_source": "lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =\n    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -\n      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 :=",
      "body_source": "by\n  rw [← normEDS_mul_complEDS₂, mul_assoc, complEDS₂_mul_b]\n  ring1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_four": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":569,"column":0},"end":{"line":571,"column":45}},
      "name": "normEDS_four",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R), normEDS b c d 4 = d * b",
      "doc": "",
      "short": "normEDS_four",
      "signature_source": "@[simp]\nlemma normEDS_four : normEDS b c d 4 = d * b :=",
      "body_source": "by\n  simp [normEDS, show ¬Odd (4 : ℤ) by decide]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_mul_complEDS₂": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"complEDS₂","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":577,"column":0},"end":{"line":580,"column":53}},
      "name": "normEDS_mul_complEDS₂",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (k : ℤ), normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k)",
      "doc": "",
      "short": "normEDS_mul_complEDS₂",
      "signature_source": "lemma normEDS_mul_complEDS₂ (k : ℤ) :\n    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) :=",
      "body_source": "by\n  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,\n    mul_one, ite_self, ite_eq_left <| even_two_mul k]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_neg": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":573,"column":0},"end":{"line":575,"column":54}},
      "name": "normEDS_neg",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (n : ℤ), normEDS b c d (-n) = -normEDS b c d n",
      "doc": "",
      "short": "normEDS_neg",
      "signature_source": "@[simp]\nlemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n :=",
      "body_source": "by\n  simp_rw [normEDS, preNormEDS_neg, even_neg, neg_mul]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_odd": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":598,"column":0},"end":{"line":604,"column":21}},
      "name": "normEDS_odd",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  normEDS b c d (2 * m + 1) =\n    normEDS b c d (m + 2) * normEDS b c d m ^ 3 - normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3",
      "doc": "",
      "short": "normEDS_odd",
      "signature_source": "lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) =\n    normEDS b c d (m + 2) * normEDS b c d m ^ 3 -\n      normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 :=",
      "body_source": "by\n  simp_rw [normEDS, preNormEDS_odd, ite_eq_right m.not_even_two_mul_add_one, Int.even_add,\n    Int.even_sub,\n    even_two, iff_true, Int.not_even_one, iff_false]\n  split_ifs <;> ring1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_one": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":557,"column":0},"end":{"line":559,"column":16}},
      "name": "normEDS_one",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R), normEDS b c d 1 = 1",
      "doc": "",
      "short": "normEDS_one",
      "signature_source": "@[simp]\nlemma normEDS_one : normEDS b c d 1 = 1 :=",
      "body_source": "by\n  simp [normEDS]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_three": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":565,"column":0},"end":{"line":567,"column":46}},
      "name": "normEDS_three",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R), normEDS b c d 3 = c",
      "doc": "",
      "short": "normEDS_three",
      "signature_source": "@[simp]\nlemma normEDS_three : normEDS b c d 3 = c :=",
      "body_source": "by\n  simp [normEDS, show ¬Even (3 : ℤ) by decide]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_two": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":561,"column":0},"end":{"line":563,"column":16}},
      "name": "normEDS_two",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R), normEDS b c d 2 = b",
      "doc": "",
      "short": "normEDS_two",
      "signature_source": "@[simp]\nlemma normEDS_two : normEDS b c d 2 = b :=",
      "body_source": "by\n  simp [normEDS]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "normEDS_zero": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":553,"column":0},"end":{"line":555,"column":16}},
      "name": "normEDS_zero",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R), normEDS b c d 0 = 0",
      "doc": "",
      "short": "normEDS_zero",
      "signature_source": "@[simp]\nlemma normEDS_zero : normEDS b c d 0 = 0 :=",
      "body_source": "by\n  simp [normEDS]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "preNormEDS": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"preNormEDS'","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"Int.cast","module":"Init.Data.Int.Basic","kind":"def"},{"where":"body","name":"Int.natAbs","module":"Init.Data.Int.Basic","kind":"def"},{"where":"body","name":"Int.sign","module":"Init.Data.Int.Basic","kind":"def"}],
      "range": {"start":{"line":428,"column":0},"end":{"line":433,"column":37}},
      "name": "preNormEDS",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → R",
      "doc": "The auxiliary sequence for a normalised EDS `W : ℤ → R`, with initial values\n`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`.\n\nThis extends `preNormEDS'` by defining its values at negative integers. ",
      "short": "preNormEDS",
      "signature_source": "def preNormEDS (n : ℤ) : R :=",
      "body_source": "n.sign * preNormEDS' b c d n.natAbs",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion",
        "DivisionPolynomials"
      ]
    },
    "preNormEDS'": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"body","name":"InvImage","module":"Init.Core","kind":"def"},{"where":"body","name":"Unit","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"WellFounded.Nat.fix","module":"Init.WF","kind":"def"}],
      "range": {"start":{"line":378,"column":0},"end":{"line":393,"column":75}},
      "name": "preNormEDS'",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℕ → R",
      "doc": "The auxiliary sequence for a normalised EDS `W : ℕ → R`, with initial values\n`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`. ",
      "short": "preNormEDS'",
      "signature_source": "def preNormEDS' : ℕ → R\n  | 0 => 0\n  | 1 => 1\n  | 2 => 1\n  | 3 => c\n  | 4 => d\n  | (n + 5) => let m :=",
      "body_source": "n / 2\n    if hn : Even n then\n      preNormEDS' (m + 4) * preNormEDS' (m + 2) ^ 3 * (if Even m then b else 1) -\n        preNormEDS' (m + 1) * preNormEDS' (m + 3) ^ 3 * (if Even m then 1 else b)\n    else\n      have : m + 5 < n + 5 := by grind\n      preNormEDS' (m + 2) ^ 2 * preNormEDS' (m + 3) * preNormEDS' (m + 5) -\n        preNormEDS' (m + 1) * preNormEDS' (m + 3) * preNormEDS' (m + 4) ^ 2",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "preNormEDS_even": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"preNormEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":465,"column":0},"end":{"line":478,"column":9}},
      "name": "preNormEDS_even",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  preNormEDS b c d (2 * m) =\n    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -\n      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2",
      "doc": "",
      "short": "preNormEDS_even",
      "signature_source": "lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) =\n    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -\n      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 :=",
      "body_source": "by\n  induction m using Int.negInduction with\n  | nat m =>\n    rcases m with _ | _ | _ | m\n    iterate 3 simp\n    simp_rw [Nat.cast_succ, Int.add_sub_cancel, show (m : ℤ) + 1 + 1 + 1 = m + 1 + 2 by rfl,\n      Int.add_sub_cancel]\n    norm_cast\n    simpa only [preNormEDS_ofNat] using preNormEDS'_even ..\n  | neg ih m =>\n    simp_rw [mul_neg, ← sub_neg_eq_add, ← neg_sub', ← neg_add', preNormEDS_neg, ih]\n    ring1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    },
    "preNormEDS_odd": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Even","module":"Mathlib.Algebra.Group.Even","kind":"def"},{"where":"type","name":"preNormEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":480,"column":0},"end":{"line":496,"column":9}},
      "name": "preNormEDS_odd",
      "module": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  preNormEDS b c d (2 * m + 1) =\n    (preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * if Even m then b else 1) -\n      preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * if Even m then 1 else b",
      "doc": "",
      "short": "preNormEDS_odd",
      "signature_source": "lemma preNormEDS_odd (m : ℤ) : preNormEDS b c d (2 * m + 1) =\n    preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) -\n      preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b) :=",
      "body_source": "by\n  induction m using Int.negInduction with\n  | nat m =>\n    rcases m with _ | _ | _\n    iterate 2 simp\n    simp_rw [Nat.cast_succ, Int.add_sub_cancel, Int.even_add_one, not_not, Int.even_coe_nat]\n    norm_cast\n    simpa only [preNormEDS_ofNat] using preNormEDS'_odd ..\n  | neg ih m =>\n    rcases m with _ | m\n    · simp\n    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,\n      show -(m + 1 : ℤ) + 2 = -(m - 1) by ring1, show -(m + 1 : ℤ) - 1 = -(m + 2) by rfl,\n      show -(m + 1 : ℤ) + 1 = -m by ring1, preNormEDS_neg, even_neg, Int.even_add_one, ite_not, ih]\n    ring1",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
