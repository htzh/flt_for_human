window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.Elliptic.Net"] = {
  "module": "FLTForHuman.Elliptic.Net",
  "cards": {
    "FLTForHuman.Elliptic.invar_normEDS": {
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.invarDenom","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"FLTForHuman.Elliptic.invarNum","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":39,"column":0},"end":{"line":43,"column":63}},
      "name": "FLTForHuman.Elliptic.invar_normEDS",
      "module": "FLTForHuman.Elliptic.Net",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (s m n : ℤ),\n  FLTForHuman.Elliptic.invarNum (normEDS b c d) s m * FLTForHuman.Elliptic.invarDenom (normEDS b c d) s n =\n    FLTForHuman.Elliptic.invarNum (normEDS b c d) s n * FLTForHuman.Elliptic.invarDenom (normEDS b c d) s m",
      "doc": "FLT's `invar_normEDS`. ",
      "short": "invar_normEDS",
      "signature_source": "lemma invar_normEDS (b c d : R) (s m n : ℤ) :\n    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =\n      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=",
      "body_source": "invar_of_net (fun p q r s => net_normEDS b c d p q r s) s m n",
      "source_file": "lean/FLTForHuman/Elliptic/Net.lean",
      "has_source": true,
      "has_refs": true
    },
    "FLTForHuman.Elliptic.invar₂_normEDS": {
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.invarDenom","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"FLTForHuman.Elliptic.invarNum","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":53,"column":0},"end":{"line":80,"column":12}},
      "name": "FLTForHuman.Elliptic.invar₂_normEDS",
      "module": "FLTForHuman.Elliptic.Net",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  FLTForHuman.Elliptic.invarNum (normEDS b c d) 1 m * c =\n    FLTForHuman.Elliptic.invarDenom (normEDS b c d) 1 m * (d + b ^ 4)",
      "doc": "FLT's `invar₂_normEDS`. ",
      "short": "invar₂_normEDS",
      "signature_source": "lemma invar₂_normEDS (b c d : R) (m : ℤ) :\n    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) :=",
      "body_source": "by\n  have h := invar₂_normEDS_of_mem_nonZeroDivisors\n    (c := X (R := ℤ) Param.C) (d := X (R := ℤ) Param.D)\n    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) Param.B)) m\n  have key : ∀ x : ℤ, (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (universalNormEDS x) = normEDS b c d x := by\n    intro x\n    show (fun y : ℤ => (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (universalNormEDS y)) x = normEDS b c d x\n    rw [← normEDS_eq_aeval]\n  have hnum : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (invarNum (normEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)) 1 m)\n      = invarNum (normEDS b c d) 1 m := by\n    change (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (invarNum universalNormEDS 1 m) = invarNum (normEDS b c d) 1 m\n    simp only [invarNum, map_add, map_mul, map_pow, key]\n  have hden : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (invarDenom (normEDS (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)) 1 m)\n      = invarDenom (normEDS b c d) 1 m := by\n    change (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (invarDenom universalNormEDS 1 m) = invarDenom (normEDS b c d) 1 m\n    simp only [invarDenom, map_mul, key]\n  have := congr(MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d) $h)\n  simp only [map_mul, map_add, map_pow, MvPolynomial.aeval_X] at this\n  rw [hnum, hden] at this\n  exact this",
      "source_file": "lean/FLTForHuman/Elliptic/Net.lean",
      "has_source": true,
      "has_refs": true
    },
    "FLTForHuman.Elliptic.net_normEDS": {
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.net","module":"FLTForHuman.Elliptic.EllSequence","kind":"abbrev"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"}],
      "range": {"start":{"line":21,"column":0},"end":{"line":37,"column":13}},
      "name": "FLTForHuman.Elliptic.net_normEDS",
      "module": "FLTForHuman.Elliptic.Net",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (p q r s : ℤ), FLTForHuman.Elliptic.net (normEDS b c d) p q r s = 0",
      "doc": "`normEDS` satisfies the full net property `rel = 0`. ",
      "short": "net_normEDS",
      "signature_source": "lemma net_normEDS (b c d : R) (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 :=",
      "body_source": "by\n  rw [normEDS_eq_aeval]\n  change IsEllipticNet.rel\n    ((MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d)) ∘ universalNormEDS)\n    p q r s = 0\n  rw [← IsEllipticNet.map_rel]\n  rw [show IsEllipticNet.rel (universalNormEDS) p q r s = 0 from\n    net_of_isEllipticSequence (normEDS_isEllipticSequence\n        (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D))\n      (mem_nonZeroDivisors_of_ne_zero (by\n        rw [normEDS_one (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)]\n        exact one_ne_zero))\n      (mem_nonZeroDivisors_of_ne_zero (by\n        rw [normEDS_two (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D)]\n        exact MvPolynomial.X_ne_zero _)) p q r s,\n    map_zero]",
      "source_file": "lean/FLTForHuman/Elliptic/Net.lean",
      "has_source": true,
      "has_refs": true
    },
    "FLTForHuman.Elliptic.redInvar_normEDS": {
      "refs": [{"where":"type","name":"FLTForHuman.Elliptic.redInvarDenom","module":"FLTForHuman.Elliptic.RedInvar","kind":"def"},{"where":"type","name":"FLTForHuman.Elliptic.redInvarNum","module":"FLTForHuman.Elliptic.DivisionPolynomial","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":96,"column":0},"end":{"line":125,"column":12}},
      "name": "FLTForHuman.Elliptic.redInvar_normEDS",
      "module": "FLTForHuman.Elliptic.Net",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] (b c d : R) (m : ℤ),\n  FLTForHuman.Elliptic.redInvarNum b c d m = FLTForHuman.Elliptic.redInvarDenom b c d m * (d + b ^ 4)",
      "doc": "FLT's `redInvar_normEDS`. ",
      "short": "redInvar_normEDS",
      "signature_source": "lemma redInvar_normEDS (b c d : R) (m : ℤ) :\n    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) :=",
      "body_source": "by\n  have h := redInvar_normEDS_of_mem_nonZeroDivisors\n    (b := X (R := ℤ) Param.B) (c := X (R := ℤ) Param.C) (d := X (R := ℤ) Param.D)\n    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) Param.B))\n    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) Param.C)) m\n  have hnum : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (redInvarNum (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m)\n      = redInvarNum b c d m := by\n    have h' := map_redInvarNum (R := MvPolynomial Param ℤ) (S := R)\n      ((MvPolynomial.aeval (R := ℤ) (Param.rec (motive := fun _ => R) b c d) :\n        MvPolynomial Param ℤ →+* R))\n      (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m\n    simpa only [AlgHom.coe_toRingHom, aeval_universal_X] using h'\n  have hden : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (redInvarDenom (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m)\n      = redInvarDenom b c d m := by\n    have h' := map_redInvarDenom (R := MvPolynomial Param ℤ) (S := R)\n      ((MvPolynomial.aeval (R := ℤ) (Param.rec (motive := fun _ => R) b c d) :\n        MvPolynomial Param ℤ →+* R))\n      (X (R := ℤ) Param.B) (X (R := ℤ) Param.C) (X (R := ℤ) Param.D) m\n    simpa only [AlgHom.coe_toRingHom, aeval_universal_X] using h'\n  have hpow : (MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d))\n      (X (R := ℤ) Param.D + (X (R := ℤ) Param.B) ^ 4) = d + b ^ 4 := by\n    simp only [map_add, map_pow, MvPolynomial.aeval_X]\n  have := congr(MvPolynomial.aeval (Param.rec (motive := fun _ => R) b c d) $h)\n  simp only [map_mul] at this\n  rw [hnum, hden, hpow] at this\n  exact this",
      "source_file": "lean/FLTForHuman/Elliptic/Net.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
