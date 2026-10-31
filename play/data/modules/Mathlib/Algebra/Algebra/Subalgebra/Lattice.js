window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Algebra.Subalgebra.Lattice"] = {
  "module": "Mathlib.Algebra.Algebra.Subalgebra.Lattice",
  "cards": {
    "Algebra.adjoin": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"body","name":"Set.range","module":"Mathlib.Data.Set.Operations","kind":"def"},{"where":"body","name":"Subsemiring","module":"Mathlib.Algebra.Ring.Subsemiring.Defs","kind":"inductive"},{"where":"body","name":"Subsemiring.closure","module":"Mathlib.Algebra.Ring.Subsemiring.Basic","kind":"def"}],
      "range": {"start":{"line":30,"column":0},"end":{"line":34,"column":79}},
      "name": "Algebra.adjoin",
      "module": "Mathlib.Algebra.Algebra.Subalgebra.Lattice",
      "kind": "def",
      "elaborated_type": "(R : Type u) →\n  {A : Type v} → [inst : CommSemiring R] → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → Set A → Subalgebra R A",
      "doc": "The minimal subalgebra that includes `s`. ",
      "short": "adjoin",
      "signature_source": "@[simps -isSimp toSubsemiring]\ndef adjoin (s : Set A) : Subalgebra R A :=",
      "body_source": "{ Subsemiring.closure (Set.range (algebraMap R A) ∪ s) with\n    algebraMap_mem' := fun r => Subsemiring.subset_closure <| Or.inl ⟨r, rfl⟩ }",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
