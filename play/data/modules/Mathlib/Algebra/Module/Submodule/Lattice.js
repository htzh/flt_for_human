window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Algebra.Module.Submodule.Lattice"] = {
  "module": "Mathlib.Algebra.Module.Submodule.Lattice",
  "cards": {
    "Submodule.completeLattice": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"CompleteLattice","module":"Mathlib.Order.CompleteLattice.Defs","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"InfSet.sInf","module":"Mathlib.Order.SetNotation","kind":"abbrev"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Set.ofPred","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Submodule.isGLB_sInf","module":"Mathlib.Algebra.Module.Submodule.Lattice","kind":"theorem"},{"where":"body","name":"Min.min","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":197,"column":0},"end":{"line":208,"column":38}},
      "name": "Submodule.completeLattice",
      "module": "Mathlib.Algebra.Module.Submodule.Lattice",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} →\n  {M : Type u_3} →\n    [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → CompleteLattice (Submodule R M)",
      "doc": "",
      "short": "completeLattice",
      "signature_source": "instance completeLattice : CompleteLattice (Submodule R M) where\n  sup a b := sInf { x | a ≤ x ∧ b ≤ x }\n  le_sup_left _ _ := Set.subset_iInter₂ fun _ ⟨h, _⟩ ↦ h\n  le_sup_right _ _ := Set.subset_iInter₂ fun _ ⟨_, h⟩ ↦ h\n  sup_le _ _ _ h₁ h₂ := Set.biInter_subset_of_mem ⟨h₁, h₂⟩\n  inf := (· ⊓ ·)\n  le_inf _ _ _ := Set.subset_inter\n  inf_le_left _ _ := Set.inter_subset_left\n  inf_le_right _ _ := Set.inter_subset_right\n  sSup S := sInf {sm | ∀ s ∈ S, s ≤ sm}\n  isLUB_sSup _ := isGLB_upperBounds.mp Submodule.isGLB_sInf\n  isGLB_sInf _ := Submodule.isGLB_sInf",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Lattice.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.mem_bot": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Bot.bot","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"}],
      "range": {"start":{"line":73,"column":0},"end":{"line":75,"column":23}},
      "name": "Submodule.mem_bot",
      "module": "Mathlib.Algebra.Module.Submodule.Lattice",
      "kind": "theorem",
      "elaborated_type": "∀ (R : Type u_1) {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},\n  x ∈ ⊥ ↔ x = 0",
      "doc": "",
      "short": "mem_bot",
      "signature_source": "@[simp]\ntheorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=",
      "body_source": "Set.mem_singleton_iff",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Lattice.lean",
      "has_source": true,
      "has_refs": true
    },
    "Submodule.mem_top": {
      "refs": [{"where":"type","name":"AddCommMonoid","module":"Mathlib.Algebra.Group.Monoid","kind":"inductive"},{"where":"type","name":"Module","module":"Mathlib.Algebra.Module.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Top.top","module":"Mathlib.Order.Notation","kind":"abbrev"}],
      "range": {"start":{"line":143,"column":0},"end":{"line":143,"column":66}},
      "name": "Submodule.mem_top",
      "module": "Mathlib.Algebra.Module.Submodule.Lattice",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},\n  x ∈ ⊤",
      "doc": "",
      "short": "mem_top",
      "signature_source": "@[simp] lemma mem_top {x : M} : x ∈ (⊤ : Submodule R M) :=",
      "body_source": "trivial",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Lattice.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
