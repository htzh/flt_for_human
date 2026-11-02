window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Field.Defs"] = {
  "module": "Mathlib.Algebra.Field.Defs",
  "cards": {
    "DivisionRing": {
      "refs": [],
      "range": {"start":{"line":106,"column":0},"end":{"line":153,"column":84}},
      "name": "DivisionRing",
      "module": "Mathlib.Algebra.Field.Defs",
      "kind": "inductive",
      "elaborated_type": "Type u_2 → Type u_2",
      "doc": "A `DivisionRing` is a `Ring` with multiplicative inverses for nonzero elements.\n\nAn instance of `DivisionRing K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.\nThose two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need\nto control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).\nSee also note [forgetful inheritance]. Similarly, there are maps `nnratCast ℚ≥0 → K` and\n`nnqsmul : ℚ≥0 → K → K` to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance.\n\nIf the division ring has positive characteristic `p`, our division by zero convention forces\n`ratCast (1 / p) = 1 / 0 = 0`. ",
      "short": "DivisionRing",
      "signature_source": "class DivisionRing (K : Type*)\n  extends Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K where\n  /-- For a nonzero `a`, `a⁻¹` is a right multiplicative inverse. -/\n  protected mul_inv_cancel : ∀ (a : K), a ≠ 0 → a * a⁻¹ = 1\n  /-- The inverse of `0` is `0` by convention. -/\n  protected inv_zero : (0 : K)⁻¹ = 0\n  protected nnratCast := NNRat.castRec\n  /-- However `NNRat.cast` is defined, it must be equal to `a / b`.\n\n  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/\n  protected nnratCast_def (q : ℚ≥0) : (NNRat.cast q : K) = q.num / q.den := by intros; rfl\n  /-- Scalar multiplication by a nonnegative rational number.\n\n  Unless there is a risk of a `Module ℚ≥0 _` instance diamond, write `nnqsmul := _`. This will set\n  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.\n\n  Do not use directly. Instead use the `•` notation. -/\n  protected nnqsmul : ℚ≥0 → K → K\n  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.\n\n  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/\n  protected nnqsmul_def (q : ℚ≥0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl\n  protected ratCast := Rat.castRec\n  /-- However `Rat.cast q` is defined, it must be propositionally equal to `q.num / q.den`.\n\n  Do not use this lemma directly. Use `Rat.cast_def` instead. -/\n  protected ratCast_def (q : ℚ) : (Rat.cast q : K) = q.num / q.den := by intros; rfl\n  /-- Scalar multiplication by a rational number.\n\n  Unless there is a risk of a `Module ℚ _` instance diamond, write `qsmul := _`. This will set\n  `qsmul` to `(Rat.cast · * ·)` thanks to unification in the default proof of `qsmul_def`.\n\n  Do not use directly. Instead use the `•` notation. -/\n  protected qsmul : ℚ → K → K\n  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.\n\n  Do not use this lemma directly. Use `Rat.cast_def` instead. -/\n  protected qsmul_def (a : ℚ) (x : K) : qsmul a x = Rat.cast a * x := by intros; rfl",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Field/Defs.lean",
      "has_source": true,
      "has_refs": false
    },
    "Field": {
      "refs": [],
      "range": {"start":{"line":170,"column":0},"end":{"line":180,"column":59}},
      "name": "Field",
      "module": "Mathlib.Algebra.Field.Defs",
      "kind": "inductive",
      "elaborated_type": "Type u → Type u",
      "doc": "A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.\n\nAn instance of `Field K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.\nThose two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need\nto control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).\nSee also note [forgetful inheritance].\n\nIf the field has positive characteristic `p`, our division by zero convention forces\n`ratCast (1 / p) = 1 / 0 = 0`. ",
      "short": "Field",
      "signature_source": "@[stacks 09FD \"first part\"]\nclass Field (K : Type u) extends CommRing K, DivisionRing K",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Field/Defs.lean",
      "has_source": true,
      "has_refs": false
    }
  }
};
