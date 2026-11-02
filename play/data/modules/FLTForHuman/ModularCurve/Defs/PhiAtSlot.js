window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.Defs.PhiAtSlot"] = {
  "module": "FLTForHuman.ModularCurve.Defs.PhiAtSlot",
  "cards": {
    "ModularCurve.phiAtSeed": {
      "refs": [{"where":"type","name":"ModularCurve.ModularPolynomialData","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"body","name":"ModularCurve.ModularPolynomialData.Φ","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"abbrev"},{"where":"body","name":"Int.castRingHom","module":"Mathlib.Data.Int.Cast.Lemmas","kind":"def"},{"where":"body","name":"Polynomial.eval₂RingHom","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"body","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":144,"column":0},"end":{"line":148,"column":60}},
      "name": "ModularCurve.phiAtSeed",
      "module": "FLTForHuman.ModularCurve.Defs.PhiAtSlot",
      "kind": "def",
      "elaborated_type": "{R : Type u_2} →\n  [inst : CommRing R] → {n : ℕ} → [inst_1 : NeZero n] → ModularCurve.ModularPolynomialData n → R → Polynomial R",
      "doc": "Evaluate `Φ` at `X = x`, as a polynomial in `Y`: the coefficient ring is\n`R` via the unique `ℤ →+* R`. ",
      "short": "phiAtSeed",
      "signature_source": "def phiAtSeed {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (data : ModularPolynomialData n) (x : R) :\n    Polynomial R :=",
      "body_source": "data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.phiAtSeed_jqN_eval": {
      "refs": [{"where":"type","name":"ModularCurve.ModularPolynomialData","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"inductive"},{"where":"type","name":"ModularCurve.jqN","module":"FLTForHuman.ModularCurve.Defs.Jq","kind":"def"},{"where":"type","name":"ModularCurve.phiAtSeed","module":"FLTForHuman.ModularCurve.Defs.PhiAtSlot","kind":"def"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"Polynomial.eval","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"},{"where":"type","name":"Rat","module":"Init.Data.Rat.Basic","kind":"inductive"}],
      "range": {"start":{"line":186,"column":0},"end":{"line":190,"column":33}},
      "name": "ModularCurve.phiAtSeed_jqN_eval",
      "module": "FLTForHuman.ModularCurve.Defs.PhiAtSlot",
      "kind": "theorem",
      "elaborated_type": "∀ (n : ℕ) [inst : NeZero n] (data : ModularCurve.ModularPolynomialData n) (M : ℕ) [inst_1 : NeZero M],\n  Polynomial.eval (ModularCurve.jqN (M * n)) (ModularCurve.phiAtSeed data (ModularCurve.jqN M)) = 0",
      "doc": "`phiAtSeed` vanishes at `(jqN M, jqN (M * n))`. ",
      "short": "phiAtSeed_jqN_eval",
      "signature_source": "theorem phiAtSeed_jqN_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :\n    (phiAtSeed data (jqN M)).eval (jqN (M * n)) = 0 :=",
      "body_source": "by\n  have h := phiAtSeed_eval_map data jq (jqN n) (qExpand ℚ M) (phiAtSeed_jq_eval n data)\n  rwa [jqN, qExpand_qExpand] at h",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.phiAtSeed_map": {
      "refs": [{"where":"type","name":"ModularCurve.ModularPolynomialData","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"inductive"},{"where":"type","name":"ModularCurve.phiAtSeed","module":"FLTForHuman.ModularCurve.Defs.PhiAtSlot","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"}],
      "range": {"start":{"line":150,"column":0},"end":{"line":158,"column":8}},
      "name": "ModularCurve.phiAtSeed_map",
      "module": "FLTForHuman.ModularCurve.Defs.PhiAtSlot",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_2} {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] {n : ℕ} [inst_2 : NeZero n]\n  (data : ModularCurve.ModularPolynomialData n) (x : R) (f : R →+* S),\n  Polynomial.map f (ModularCurve.phiAtSeed data x) = ModularCurve.phiAtSeed data (f x)",
      "doc": "`phiAtSeed` is natural in the coefficient ring. ",
      "short": "phiAtSeed_map",
      "signature_source": "theorem phiAtSeed_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]\n    (data : ModularPolynomialData n) (x : R) (f : R →+* S) :\n    (phiAtSeed data x).map f = phiAtSeed data (f x) :=",
      "body_source": "by\n  rw [phiAtSeed, phiAtSeed, Polynomial.map_map]\n  congr 1\n  refine Polynomial.ringHom_ext' ?_ ?_\n  · exact RingHom.ext_int _ _\n  · simp",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.phiAtSeed_monic": {
      "refs": [{"where":"type","name":"ModularCurve.ModularPolynomialData","module":"FLTForHuman.ModularCurve.Defs.Polynomial","kind":"inductive"},{"where":"type","name":"ModularCurve.phiAtSeed","module":"FLTForHuman.ModularCurve.Defs.PhiAtSlot","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Nontrivial","module":"Mathlib.Basic.Nontrivial.Defs","kind":"inductive"},{"where":"type","name":"Polynomial.Monic","module":"Mathlib.Algebra.Polynomial.Degree.Defs","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"NeZero","module":"Init.Data.NeZero","kind":"inductive"}],
      "range": {"start":{"line":160,"column":0},"end":{"line":163,"column":18}},
      "name": "ModularCurve.phiAtSeed_monic",
      "module": "FLTForHuman.ModularCurve.Defs.PhiAtSlot",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_2} [inst : CommRing R] [Nontrivial R] {n : ℕ} [inst_2 : NeZero n]\n  (data : ModularCurve.ModularPolynomialData n) (x : R), (ModularCurve.phiAtSeed data x).Monic",
      "doc": "`phiAtSeed` is monic. ",
      "short": "phiAtSeed_monic",
      "signature_source": "theorem phiAtSeed_monic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]\n    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).Monic :=",
      "body_source": "data.monic.map _",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
