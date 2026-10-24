window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Derivation.Basic"] = {
  "module": "Mathlib.RingTheory.Derivation.Basic",
  "cards": {
    "Derivation": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"}],
      "range": {"start":{"line":40,"column":0},"end":{"line":49,"column":92}},
      "name": "Derivation",
      "module": "Mathlib.RingTheory.Derivation.Basic",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_1) →\n  (A : Type u_2) →\n    (M : Type u_3) →\n      [inst : CommSemiring R] →\n        [inst_1 : CommSemiring A] →\n          [inst_2 : AddCommMonoid M] → [Algebra R A] → [_root_.Module A M] → [_root_.Module R M] → Type (max u_2 u_3)",
      "doc": "`D : Derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`\nequality. We also require that `D 1 = 0`. See `Derivation.mk'` for a constructor that deduces this\nassumption from the Leibniz rule when `M` is cancellative.\n\nTODO: update this when bimodules are defined. ",
      "short": "Derivation",
      "signature_source": "structure Derivation (R : Type*) (A : Type*) (M : Type*)\n    [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M] [Module R M]\n    extends A →ₗ[R] M where\n  protected map_one_eq_zero' : toLinearMap 1 = 0\n  protected leibniz' (a b : A) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Derivation.leibniz": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":117,"column":0},"end":{"line":119,"column":16}},
      "name": "Derivation.leibniz",
      "module": "Mathlib.RingTheory.Derivation.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {A : Type u_2} {M : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]\n  [inst_2 : AddCommMonoid M] [inst_3 : Algebra R A] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M]\n  (D : Derivation R A M) (a b : A), D (a * b) = a • D b + b • D a",
      "doc": "",
      "short": "leibniz",
      "signature_source": "@[simp]\ntheorem leibniz : D (a * b) = a • D b + b • D a :=",
      "body_source": "D.leibniz' _ _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Derivation.leibniz_pow": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":138,"column":0},"end":{"line":147,"column":50}},
      "name": "Derivation.leibniz_pow",
      "module": "Mathlib.RingTheory.Derivation.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {A : Type u_2} {M : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]\n  [inst_2 : AddCommMonoid M] [inst_3 : Algebra R A] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M]\n  (D : Derivation R A M) (a : A) (n : ℕ), D (a ^ n) = n • a ^ (n - 1) • D a",
      "doc": "",
      "short": "leibniz_pow",
      "signature_source": "@[simp]\ntheorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a :=",
      "body_source": "by\n  induction n with\n  | zero => rw [pow_zero, map_one_eq_zero, zero_smul]\n  | succ n ihn =>\n    rcases eq_zero_or_pos n with (rfl | hpos)\n    · simp\n    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ', Nat.sub_add_cancel hpos]\n      simp only [pow_succ', leibniz, ihn, smul_comm a n (_ : M), smul_smul a, add_smul, this,\n        Nat.add_succ_sub_one, add_zero, one_nsmul]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Derivation.map_algebraMap": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Derivation","module":"Mathlib.RingTheory.Derivation.Basic","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"}],
      "range": {"start":{"line":130,"column":0},"end":{"line":132,"column":86}},
      "name": "Derivation.map_algebraMap",
      "module": "Mathlib.RingTheory.Derivation.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {A : Type u_2} {M : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]\n  [inst_2 : AddCommMonoid M] [inst_3 : Algebra R A] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module R M]\n  (D : Derivation R A M) (r : R), D ((algebraMap R A) r) = 0",
      "doc": "",
      "short": "map_algebraMap",
      "signature_source": "@[simp]\ntheorem map_algebraMap : D (algebraMap R A r) = 0 :=",
      "body_source": "by\n  rw [← mul_one r, map_mul, map_one, ← smul_def, map_smul, map_one_eq_zero, smul_zero]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
