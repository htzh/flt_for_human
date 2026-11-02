window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.Defs.Laurent"] = {
  "module": "FLTForHuman.ModularCurve.Defs.Laurent",
  "cards": {
    "ModularCurve.coeffEmb": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"},{"where":"body","name":"ModularCurve.coeffMap","module":"FLTForHuman.ModularCurve.Defs.Laurent","kind":"def"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"}],
      "range": {"start":{"line":266,"column":0},"end":{"line":269,"column":27}},
      "name": "ModularCurve.coeffEmb",
      "module": "FLTForHuman.ModularCurve.Defs.Laurent",
      "kind": "def",
      "elaborated_type": "(L : Type u_1) → [inst : Field L] → [Algebra ℚ L] → LaurentSeries ℚ →+* LaurentSeries L",
      "doc": "The coefficient embedding `ℚ → K` extended coefficientwise to Laurent\nseries: the way the base field `ℚ` sits inside `LaurentSeries K`. ",
      "short": "coeffEmb",
      "signature_source": "def coeffEmb : LaurentSeries ℚ →+* LaurentSeries L :=",
      "body_source": "coeffMap (algebraMap ℚ L)",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/Laurent.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.coeffMap": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"HahnSeries.map","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"def"}],
      "range": {"start":{"line":160,"column":0},"end":{"line":176,"column":25}},
      "name": "ModularCurve.coeffMap",
      "module": "FLTForHuman.ModularCurve.Defs.Laurent",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {S : Type u_2} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → LaurentSeries R →+* LaurentSeries S",
      "doc": "Extend a coefficient map `f : R →+* S` coefficientwise to Laurent series. ",
      "short": "coeffMap",
      "signature_source": "def coeffMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where\n  toFun x := x.map f\n  map_zero' := by\n    ext k\n    simp\n  map_one' := by\n    ext k\n    simp [HahnSeries.coeff_one, apply_ite f]\n  map_add' x y := by\n    ext k\n    simp\n  map_mul' x y := by\n    have h := HahnSeries.map_mul (f := (f : R →ₙ+* S)) (x := x) (y := y)\n    have hx : ∀ z : LaurentSeries R, z.map (f : R →ₙ+* S) = z.map f := fun z =>\n      HahnSeries.ext rfl\n    rwa [hx, hx, hx] at h",
      "body_source": "",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/Laurent.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.qExpand": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"body","name":"AddMonoidHom.mulLeft","module":"Mathlib.Algebra.Ring.Basic","kind":"def"},{"where":"body","name":"HahnSeries.embDomainRingHom","module":"Mathlib.RingTheory.HahnSeries.Multiplication","kind":"def"},{"where":"body","name":"Nat.cast","module":"Init.Data.Cast","kind":"def"}],
      "range": {"start":{"line":78,"column":0},"end":{"line":84,"column":59}},
      "name": "ModularCurve.qExpand",
      "module": "FLTForHuman.ModularCurve.Defs.Laurent",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) → [inst : CommRing R] → (N : ℕ) → [NeZero N] → LaurentSeries R →+* LaurentSeries R",
      "doc": "The `q`-substitution `q ↦ q ^ N`, as a ring endomorphism of Laurent series:\non a monomial `q ^ k` it is `q ^ (N * k)`, and coefficients are unchanged. ",
      "short": "qExpand",
      "signature_source": "def qExpand (N : ℕ) [NeZero N] : LaurentSeries R →+* LaurentSeries R :=",
      "body_source": "HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))\n    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))\n    (fun g g' => mul_le_mul_iff_of_pos_left\n      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/Laurent.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
