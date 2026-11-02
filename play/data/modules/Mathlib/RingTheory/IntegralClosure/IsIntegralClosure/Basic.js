window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic"] = {
  "module": "Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic",
  "cards": {
    "isIntegral_trans": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":475,"column":0},"end":{"line":496,"column":32}},
      "name": "isIntegral_trans",
      "module": "Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]\n  [inst_3 : Algebra A B] [inst_4 : Algebra R B] [inst_5 : Algebra R A] [IsScalarTower R A B] [Algebra.IsIntegral R A]\n  (x : B), IsIntegral A x → IsIntegral R x",
      "doc": "If A is an R-algebra all of whose elements are integral over R,\nand x is an element of an A-algebra that is integral over A, then x is integral over R. ",
      "short": "isIntegral_trans",
      "signature_source": "theorem isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx : IsIntegral A x) :\n    IsIntegral R x :=",
      "body_source": "by\n  rcases hx with ⟨p, pmonic, hp⟩\n  let S := adjoin R (p.coeffs : Set A)\n  have : Module.Finite R S := ⟨(Subalgebra.toSubmodule S).fg_top.mpr <|\n    fg_adjoin_of_finite p.coeffs.finite_toSet fun a _ ↦ Algebra.IsIntegral.isIntegral a⟩\n  let p' : S[X] := p.toSubring S.toSubring subset_adjoin\n  have hSx : IsIntegral S x := ⟨p', (p.monic_toSubring _ _).mpr pmonic, by\n    rw [IsScalarTower.algebraMap_eq S A B, ← eval₂_map]\n    convert! hp; apply p.map_toSubring S.toSubring⟩\n  let Sx := Subalgebra.toSubmodule (S[x])\n  let MSx : Module S Sx := SMulMemClass.toModule _ -- the next line times out without this\n  have : Module.Finite S Sx := .of_fg hSx.fg_adjoin_singleton\n  refine .of_mem_of_fg ((S[x]).restrictScalars R) ?_ _\n    ((Subalgebra.mem_restrictScalars R).mpr <| subset_adjoin rfl)\n  rw [← Module.Finite.iff_fg]\n  let : SMul S Sx := { MSx with } -- need this even though MSx is there\n  have : IsScalarTower R S Sx :=\n    Submodule.isScalarTower Sx -- Lean looks for `Module A Sx` without this\n  exact Module.Finite.trans S Sx",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
