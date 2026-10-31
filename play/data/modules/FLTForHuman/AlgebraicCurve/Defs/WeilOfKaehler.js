window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler"] = {
  "module": "FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler",
  "cards": {
    "AlgebraicCurve.ResiduePairingSurjective": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.Divisor","module":"FLTForHuman.AlgebraicCurve.Defs.Divisor","kind":"abbrev"},{"where":"body","name":"AlgebraicCurve.HasPrincipalDivisors","module":"FLTForHuman.AlgebraicCurve.Defs.Divisor","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.LSpace","module":"FLTForHuman.AlgebraicCurve.Defs.AdelicIndex","kind":"abbrev"},{"where":"body","name":"AlgebraicCurve.Place","module":"FLTForHuman.AlgebraicCurve.Defs.Place","kind":"inductive"},{"where":"body","name":"AlgebraicCurve.adeleSpace","module":"FLTForHuman.AlgebraicCurve.Defs.AdelicIndex","kind":"def"},{"where":"body","name":"AlgebraicCurve.omegaSpace","module":"FLTForHuman.AlgebraicCurve.Defs.AdelicIndex","kind":"def"},{"where":"body","name":"AlgebraicCurve.residuePairing","module":"FLTForHuman.AlgebraicCurve.Defs.AdelicIndex","kind":"def"},{"where":"body","name":"LinearMap","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"inductive"},{"where":"body","name":"LinearMap.addCommMonoid","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"LinearMap.module","module":"Mathlib.Algebra.Module.LinearMap.Defs","kind":"def"},{"where":"body","name":"Module.Dual","module":"Mathlib.LinearAlgebra.Dual.Defs","kind":"abbrev"},{"where":"body","name":"Pi.Function.module","module":"Mathlib.Algebra.Module.Pi","kind":"def"},{"where":"body","name":"Pi.addCommMonoid","module":"Mathlib.Algebra.Group.Pi.Basic","kind":"def"},{"where":"body","name":"RingHom.id","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"Submodule","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"inductive"},{"where":"body","name":"Submodule.addCommMonoid","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Submodule.module","module":"Mathlib.Algebra.Module.Submodule.Defs","kind":"def"},{"where":"body","name":"Function.Surjective","module":"Init.Data.Function","kind":"def"},{"where":"body","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Ne","module":"Init.Core","kind":"def"}],
      "range": {"start":{"line":133,"column":0},"end":{"line":137,"column":51}},
      "name": "AlgebraicCurve.ResiduePairingSurjective",
      "module": "FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler",
      "kind": "def",
      "elaborated_type": "(K : Type u_1) → (F : Type u_2) → [inst : Field K] → [inst_1 : Field F] → [Algebra K F] → Prop",
      "doc": "",
      "short": "ResiduePairingSurjective",
      "signature_source": "def ResiduePairingSurjective : Prop :=",
      "body_source": "∀ [HasPrincipalDivisors K F] (W D : Divisor K F)\n    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (_hφ0 : φ ≠ 0)\n    (_hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W),\n    Function.Surjective (residuePairing K F W D hφ)",
      "source_file": "lean/FLTForHuman/AlgebraicCurve/Defs/WeilOfKaehler.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
