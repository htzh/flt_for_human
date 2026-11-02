window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic"] = {
  "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic",
  "cards": {
    "IsIntegral.fg_adjoin_singleton": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.adjoin","module":"Mathlib.Algebra.Algebra.Subalgebra.Lattice","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"OrderEmbedding","module":"Mathlib.Order.Hom.Basic","kind":"abbrev"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"},{"where":"type","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"type","name":"Submodule.FG","module":"Mathlib.RingTheory.Finiteness.Defs","kind":"def"}],
      "range": {"start":{"line":104,"column":0},"end":{"line":109,"column":63}},
      "name": "IsIntegral.fg_adjoin_singleton",
      "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {B : Type u_3} [inst : CommRing R] [inst_1 : Ring B] [inst_2 : Algebra R B] {x : B},\n  IsIntegral R x → (Subalgebra.toSubmodule R[x]).FG",
      "doc": "",
      "short": "fg_adjoin_singleton",
      "signature_source": "theorem IsIntegral.fg_adjoin_singleton [Algebra R B] {x : B} (hx : IsIntegral R x) :\n    (Algebra.adjoin R {x}).toSubmodule.FG :=",
      "body_source": "by\n  classical\n  rcases hx with ⟨f, hfm, hfx⟩\n  use (Finset.range <| f.natDegree).image (x ^ ·)\n  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "IsIntegral.tower_top": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":156,"column":0},"end":{"line":161,"column":96}},
      "name": "IsIntegral.tower_top",
      "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]\n  [inst_3 : Algebra R A] [inst_4 : Algebra R B] [inst_5 : Algebra A B] [IsScalarTower R A B] {x : B},\n  IsIntegral R x → IsIntegral A x",
      "doc": "If `R → A → B` is an algebra tower,\nthen if the entire tower is an integral extension so is `A → B`. ",
      "short": "tower_top",
      "signature_source": "theorem IsIntegral.tower_top [Algebra A B] [IsScalarTower R A B] {x : B}\n    (hx : IsIntegral R x) : IsIntegral A x :=",
      "body_source": "let ⟨p, hp, hpx⟩ := hx\n  ⟨p.map <| algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "isIntegral_algHom_iff": {
      "refs": [{"where":"type","name":"AlgHom","module":"Mathlib.Algebra.Algebra.Hom","kind":"inductive"},{"where":"type","name":"AlgHom.funLike","module":"Mathlib.Algebra.Algebra.Hom","kind":"def"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Function.Injective","module":"Init.Data.Function","kind":"def"}],
      "range": {"start":{"line":79,"column":0},"end":{"line":81,"column":77}},
      "name": "isIntegral_algHom_iff",
      "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} [inst : CommRing R] {A : Type u_6} {B : Type u_7} [inst_1 : Ring A] [inst_2 : Ring B]\n  [inst_3 : Algebra R A] [inst_4 : Algebra R B] (f : A →ₐ[R] B),\n  Function.Injective ⇑f → ∀ {x : A}, IsIntegral R (f x) ↔ IsIntegral R x",
      "doc": "",
      "short": "isIntegral_algHom_iff",
      "signature_source": "theorem isIntegral_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f) {x : A} :\n    IsIntegral R (f x) ↔ IsIntegral R x :=",
      "body_source": "by\n  simp [IsIntegral, ← RingHom.IsIntegralElem.map_iff (g := (f : A →+* B)) hf]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "isIntegral_algebraMap": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"}],
      "range": {"start":{"line":33,"column":0},"end":{"line":34,"column":37}},
      "name": "isIntegral_algebraMap",
      "module": "Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {x : R},\n  IsIntegral R ((algebraMap R A) x)",
      "doc": "",
      "short": "isIntegral_algebraMap",
      "signature_source": "theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=",
      "body_source": "(algebraMap R A).isIntegralElem_map",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
