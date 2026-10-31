window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Ideal.Quotient.Operations"] = {
  "module": "Mathlib.RingTheory.Ideal.Quotient.Operations",
  "cards": {
    "Ideal.mk_ker": {
      "refs": [{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.IsTwoSided","module":"Mathlib.RingTheory.Ideal.Defs","kind":"inductive"},{"where":"type","name":"Ideal.Quotient.mk","module":"Mathlib.RingTheory.Ideal.Quotient.Defs","kind":"def"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHom.ker","module":"Mathlib.RingTheory.Ideal.Maps","kind":"def"}],
      "range": {"start":{"line":132,"column":0},"end":{"line":135,"column":66}},
      "name": "Ideal.mk_ker",
      "module": "Mathlib.RingTheory.Ideal.Quotient.Operations",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : Ring R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHom.ker (Ideal.Quotient.mk I) = I",
      "doc": "",
      "short": "mk_ker",
      "signature_source": "@[simp]\ntheorem mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) = I :=",
      "body_source": "by\n  ext\n  rw [ker, mem_comap, Submodule.mem_bot, Quotient.eq_zero_iff_mem]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.kerLift": {
      "refs": [{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHom.ker","module":"Mathlib.RingTheory.Ideal.Maps","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Ideal.Quotient.lift","module":"Mathlib.RingTheory.Ideal.Quotient.Defs","kind":"def"}],
      "range": {"start":{"line":36,"column":0},"end":{"line":42,"column":45}},
      "name": "RingHom.kerLift",
      "module": "Mathlib.RingTheory.Ideal.Quotient.Operations",
      "kind": "def",
      "elaborated_type": "{R : Type u} → {S : Type v} → [inst : Ring R] → [inst_1 : Semiring S] → (f : R →+* S) → R ⧸ RingHom.ker f →+* S",
      "doc": "The induced map from the quotient by the kernel to the codomain.\n\nThis is an isomorphism if `f` has a right inverse (`quotientKerEquivOfRightInverse`) /\nis surjective (`quotientKerEquivOfSurjective`).\n",
      "short": "kerLift",
      "signature_source": "def kerLift : R ⧸ ker f →+* S :=",
      "body_source": "Ideal.Quotient.lift _ f fun _ => mem_ker.mp",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.quotientKerEquivOfRightInverse": {
      "refs": [{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingEquiv","module":"Mathlib.Algebra.Ring.Equiv","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHom.ker","module":"Mathlib.RingTheory.Ideal.Maps","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Function.RightInverse","module":"Init.Data.Function","kind":"def"},{"where":"body","name":"Ideal.Quotient.mk","module":"Mathlib.RingTheory.Ideal.Quotient.Defs","kind":"def"},{"where":"body","name":"RingHom.kerLift","module":"Mathlib.RingTheory.Ideal.Quotient.Operations","kind":"def"},{"where":"body","name":"Function.comp","module":"Init.Prelude","kind":"def"}],
      "range": {"start":{"line":65,"column":0},"end":{"line":76,"column":21}},
      "name": "RingHom.quotientKerEquivOfRightInverse",
      "module": "Mathlib.RingTheory.Ideal.Quotient.Operations",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {S : Type v} →\n    [inst : Ring R] →\n      [inst_1 : Semiring S] → {f : R →+* S} → {g : S → R} → Function.RightInverse g ⇑f → R ⧸ RingHom.ker f ≃+* S",
      "doc": "The **first isomorphism theorem for commutative rings**, computable version. ",
      "short": "quotientKerEquivOfRightInverse",
      "signature_source": "def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) :\n    R ⧸ ker f ≃+* S :=",
      "body_source": "{ kerLift f with\n    toFun := kerLift f\n    invFun := Ideal.Quotient.mk (ker f) ∘ g\n    left_inv := by\n      rintro ⟨x⟩\n      apply kerLift_injective\n      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,\n        Function.comp_apply, hf (f x)]\n    right_inv := hf }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.quotientKerEquivOfSurjective": {
      "refs": [{"where":"type","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingEquiv","module":"Mathlib.Algebra.Ring.Equiv","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"RingHom.ker","module":"Mathlib.RingTheory.Ideal.Maps","kind":"def"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Function.Surjective","module":"Init.Data.Function","kind":"def"},{"where":"body","name":"RingHom.quotientKerEquivOfRightInverse","module":"Mathlib.RingTheory.Ideal.Quotient.Operations","kind":"def"},{"where":"body","name":"Classical.choose","module":"Init.Classical","kind":"def"},{"where":"body","name":"Function.RightInverse","module":"Init.Data.Function","kind":"def"}],
      "range": {"start":{"line":88,"column":0},"end":{"line":90,"column":75}},
      "name": "RingHom.quotientKerEquivOfSurjective",
      "module": "Mathlib.RingTheory.Ideal.Quotient.Operations",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {S : Type v} →\n    [inst : Ring R] → [inst_1 : Semiring S] → {f : R →+* S} → Function.Surjective ⇑f → R ⧸ RingHom.ker f ≃+* S",
      "doc": "The **first isomorphism theorem** for commutative rings, surjective case. ",
      "short": "quotientKerEquivOfSurjective",
      "signature_source": "noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=",
      "body_source": "quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
