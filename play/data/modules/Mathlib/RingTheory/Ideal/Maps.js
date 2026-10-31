window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Ideal.Maps"] = {
  "module": "Mathlib.RingTheory.Ideal.Maps",
  "cards": {
    "Ideal.comap": {
      "refs": [{"where":"type","name":"FunLike","module":"Mathlib.Data.FunLike.Basic","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"RingHomClass","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"body","name":"Set.preimage","module":"Mathlib.Data.Set.Operations","kind":"def"}],
      "range": {"start":{"line":46,"column":0},"end":{"line":55,"column":29}},
      "name": "Ideal.comap",
      "module": "Mathlib.RingTheory.Ideal.Maps",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {S : Type v} →\n    {F : Type u_1} →\n      [inst : Semiring R] →\n        [inst_1 : Semiring S] → [inst_2 : FunLike F R S] → F → [RingHomClass F R S] → Ideal S → Ideal R",
      "doc": "`I.comap f` is the preimage of `I` under `f`. ",
      "short": "comap",
      "signature_source": "def comap [RingHomClass F R S] (I : Ideal S) : Ideal R where\n  carrier := f ⁻¹' I\n  add_mem' {x y} hx hy := by\n    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢\n    exact add_mem hx hy\n  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]\n  smul_mem' c x hx := by\n    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *\n    exact mul_mem_left I _ hx",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.ker": {
      "refs": [{"where":"type","name":"FunLike","module":"Mathlib.Data.FunLike.Basic","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"RingHomClass","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"body","name":"Bot.bot","module":"Mathlib.Order.Notation","kind":"abbrev"},{"where":"body","name":"Ideal.comap","module":"Mathlib.RingTheory.Ideal.Maps","kind":"def"}],
      "range": {"start":{"line":745,"column":0},"end":{"line":747,"column":17}},
      "name": "RingHom.ker",
      "module": "Mathlib.RingTheory.Ideal.Maps",
      "kind": "def",
      "elaborated_type": "{R : Type u} →\n  {S : Type v} →\n    {F : Type u_1} →\n      [inst : Semiring R] → [inst_1 : Semiring S] → [inst_2 : FunLike F R S] → [rcf : RingHomClass F R S] → F → Ideal R",
      "doc": "Kernel of a ring homomorphism as an ideal of the domain. ",
      "short": "ker",
      "signature_source": "def ker : Ideal R :=",
      "body_source": "Ideal.comap f ⊥",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean",
      "has_source": true,
      "has_refs": true
    },
    "RingHom.mem_ker": {
      "refs": [{"where":"type","name":"FunLike","module":"Mathlib.Data.FunLike.Basic","kind":"abbrev"},{"where":"type","name":"Ideal","module":"Mathlib.RingTheory.Ideal.Defs","kind":"abbrev"},{"where":"type","name":"RingHom.ker","module":"Mathlib.RingTheory.Ideal.Maps","kind":"def"},{"where":"type","name":"RingHomClass","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":752,"column":0},"end":{"line":753,"column":100}},
      "name": "RingHom.mem_ker",
      "module": "Mathlib.RingTheory.Ideal.Maps",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]\n  [rcf : RingHomClass F R S] {f : F} {r : R}, r ∈ RingHom.ker f ↔ f r = 0",
      "doc": "An element is in the kernel if and only if it maps to zero. ",
      "short": "mem_ker",
      "signature_source": "@[simp] theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 :=",
      "body_source": "by rw [ker, Ideal.mem_comap, Submodule.mem_bot]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
