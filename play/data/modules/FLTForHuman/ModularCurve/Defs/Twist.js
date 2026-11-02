window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.ModularCurve.Defs.Twist"] = {
  "module": "FLTForHuman.ModularCurve.Defs.Twist",
  "cards": {
    "ModularCurve.qTwist": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Units","module":"Mathlib.Algebra.Group.Units.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"ModularCurve.qTwistFun","module":"FLTForHuman.ModularCurve.Defs.Twist","kind":"def"}],
      "range": {"start":{"line":52,"column":0},"end":{"line":82,"column":89}},
      "name": "ModularCurve.qTwist",
      "module": "FLTForHuman.ModularCurve.Defs.Twist",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [inst : CommRing R] → Rˣ → LaurentSeries R →+* LaurentSeries R",
      "doc": "`qTwistFun u` as a ring endomorphism of Laurent series: the substitution\n`q ↦ u q`. ",
      "short": "qTwist",
      "signature_source": "def qTwist (u : Rˣ) : LaurentSeries R →+* LaurentSeries R where\n  toFun := qTwistFun u\n  map_one' := by\n    ext k\n    rw [qTwistFun_coeff, HahnSeries.coeff_one]\n    split_ifs with h\n    · subst h; simp\n    · rw [mul_zero]\n  map_mul' f g := by\n    ext k\n\n    have hset : pwoAntidiagonal (qTwistFun u f).isPWO_support\n        (qTwistFun u g).isPWO_support k =\n        pwoAntidiagonal f.isPWO_support g.isPWO_support k := by\n      ext ij\n      simp only [mem_pwoAntidiagonal, support_qTwistFun]\n    rw [qTwistFun_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, hset, Finset.mul_sum]\n    refine Finset.sum_congr rfl fun ij hij => ?_\n    obtain ⟨-, -, hsum⟩ := mem_pwoAntidiagonal.mp hij\n    rw [qTwistFun_coeff, qTwistFun_coeff, mul_mul_mul_comm, ← Units.val_mul, ← zpow_add,\n      hsum]\n  map_zero' := by\n    ext k\n    rw [qTwistFun_coeff, HahnSeries.coeff_zero, mul_zero]\n  map_add' f g := by\n    ext k\n    rw [HahnSeries.coeff_add]\n    show (qTwistFun u (f + g)).coeff k = (qTwistFun u f).coeff k + (qTwistFun u g).coeff k\n    rw [qTwistFun_coeff, qTwistFun_coeff, qTwistFun_coeff, HahnSeries.coeff_add, mul_add]",
      "body_source": "",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/Twist.lean",
      "has_source": true,
      "has_refs": true
    },
    "ModularCurve.qTwistFun": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"LaurentSeries","module":"Mathlib.RingTheory.LaurentSeries","kind":"abbrev"},{"where":"type","name":"Units","module":"Mathlib.Algebra.Group.Units.Defs","kind":"inductive"},{"where":"body","name":"HahnSeries.coeff","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"abbrev"},{"where":"body","name":"Units.val","module":"Mathlib.Algebra.Group.Units.Defs","kind":"abbrev"},{"where":"body","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":31,"column":0},"end":{"line":37,"column":43}},
      "name": "ModularCurve.qTwistFun",
      "module": "FLTForHuman.ModularCurve.Defs.Twist",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [inst : CommRing R] → Rˣ → LaurentSeries R → LaurentSeries R",
      "doc": "The twist `q ↦ u q` on coefficients: the coefficient of `q ^ k` is rescaled\nby `u ^ k`. ",
      "short": "qTwistFun",
      "signature_source": "def qTwistFun (u : Rˣ) (f : LaurentSeries R) : LaurentSeries R where\n  coeff k := (u ^ k : Rˣ) * f.coeff k\n  isPWO_support' := f.isPWO_support'.mono fun k hk => by\n    simp only [Function.mem_support] at hk ⊢\n    exact fun h => hk (by rw [h, mul_zero])",
      "body_source": "",
      "source_file": "lean/FLTForHuman/ModularCurve/Defs/Twist.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
