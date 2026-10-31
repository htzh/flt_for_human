window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Ideal.Cotangent"] = {
  "module": "Mathlib.RingTheory.Ideal.Cotangent",
  "cards": {
    "Ideal.Cotangent": {
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"body","name":"HasQuotient.Quotient","module":"Mathlib.Algebra.Quotient","kind":"abbrev"},{"where":"body","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.addCommGroup","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.hasQuotient","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"body","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"body","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":41,"column":0},"end":{"line":43,"column":18}},
      "name": "Ideal.Cotangent",
      "module": "Mathlib.RingTheory.Ideal.Cotangent",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : CommRing R] → Ideal R → Type u",
      "doc": "`I ⧸ I ^ 2` as a quotient of `I`. ",
      "short": "Cotangent",
      "signature_source": "def Cotangent : Type _ :=",
      "body_source": "I ⧸ (I • ⊤ : Submodule R I)\nderiving Inhabited",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Cotangent.lean",
      "has_source": true,
      "has_refs": true
    },
    "Ideal.Cotangent.smul_eq_zero_of_mem": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.Cotangent","module":"Mathlib.RingTheory.Ideal.Cotangent","kind":"def"},{"where":"type","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":107,"column":0},"end":{"line":111,"column":32}},
      "name": "Ideal.Cotangent.smul_eq_zero_of_mem",
      "module": "Mathlib.RingTheory.Ideal.Cotangent",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] {I : Ideal R} {x : R}, x ∈ I → ∀ (m : I.Cotangent), x • m = 0",
      "doc": "",
      "short": "smul_eq_zero_of_mem",
      "signature_source": "lemma Cotangent.smul_eq_zero_of_mem {I : Ideal R}\n    {x} (hx : x ∈ I) (m : I.Cotangent) : x • m = 0 :=",
      "body_source": "by\n  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m\n  rw [← map_smul, Ideal.toCotangent_eq_zero, pow_two]\n  exact Ideal.mul_mem_mul hx m.2",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Cotangent.lean",
      "has_source": true,
      "has_refs": true
    },
    "Ideal.map_toCotangent_ker": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.Cotangent","module":"Mathlib.RingTheory.Ideal.Cotangent","kind":"def"},{"where":"type","name":"LinearMap.ker","module":"Mathlib.Algebra.Module.Submodule.Ker","kind":"def"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"RingHomSurjective.ids","module":"Mathlib.Algebra.Ring.CompTypeclasses","kind":"theorem"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"Submodule.idemSemiring","module":"Mathlib.Algebra.Algebra.Operations","kind":"def"},{"where":"type","name":"Submodule.map","module":"Mathlib.Algebra.Module.Submodule.Map","kind":"def"},{"where":"type","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"Submodule.subtype","module":"Mathlib.Algebra.Module.Submodule.LinearMap","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":57,"column":0},"end":{"line":59,"column":43}},
      "name": "Ideal.map_toCotangent_ker",
      "module": "Mathlib.RingTheory.Ideal.Cotangent",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] (I : Ideal R), Submodule.map (Submodule.subtype I) I.toCotangent.ker = I ^ 2",
      "doc": "",
      "short": "map_toCotangent_ker",
      "signature_source": "theorem map_toCotangent_ker : (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2 :=",
      "body_source": "by\n  rw [Ideal.toCotangent, Submodule.ker_mkQ, pow_two, Submodule.map_smul'' I ⊤ (Submodule.subtype I),\n    smul_eq_mul, Submodule.map_subtype_top]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Cotangent.lean",
      "has_source": true,
      "has_refs": true
    },
    "Ideal.toCotangent": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.Cotangent","module":"Mathlib.RingTheory.Ideal.Cotangent","kind":"def"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.addCommGroup","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.mkQ","module":"Mathlib.LinearAlgebra.Quotient.Defs","kind":"def"},{"where":"body","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"body","name":"HSMul.hSMul","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":52,"column":0},"end":{"line":54,"column":56}},
      "name": "Ideal.toCotangent",
      "module": "Mathlib.RingTheory.Ideal.Cotangent",
      "kind": "def",
      "elaborated_type": "{R : Type u} → [inst : CommRing R] → (I : Ideal R) → ↥I →ₗ[R] I.Cotangent",
      "doc": "The quotient map from `I` to `I ⧸ I ^ 2`. ",
      "short": "toCotangent",
      "signature_source": "@[simps! -isSimp apply]\ndef toCotangent : I →ₗ[R] I.Cotangent :=",
      "body_source": "Submodule.mkQ _",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Cotangent.lean",
      "has_source": true,
      "has_refs": true
    },
    "Ideal.toCotangent_eq": {
      "refs": [{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"Ideal.Cotangent","module":"Mathlib.RingTheory.Ideal.Cotangent","kind":"def"},{"where":"type","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"type","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"type","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"Submodule.idemSemiring","module":"Mathlib.Algebra.Algebra.Operations","kind":"def"},{"where":"type","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":65,"column":0},"end":{"line":67,"column":29}},
      "name": "Ideal.toCotangent_eq",
      "module": "Mathlib.RingTheory.Ideal.Cotangent",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} [inst : CommRing R] (I : Ideal R) {x y : ↥I}, I.toCotangent x = I.toCotangent y ↔ ↑x - ↑y ∈ I ^ 2",
      "doc": "",
      "short": "toCotangent_eq",
      "signature_source": "theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 :=",
      "body_source": "by\n  rw [← sub_eq_zero]\n  exact I.mem_toCotangent_ker",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Cotangent.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
