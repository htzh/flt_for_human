window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed"] = {
  "module": "Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed",
  "cards": {
    "minpoly.isIntegrallyClosed_eq_field_fractions'": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"},{"where":"type","name":"IsDomain","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsFractionRing","module":"Mathlib.RingTheory.Localization.FractionRing","kind":"abbrev"},{"where":"type","name":"IsIntegral","module":"Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","kind":"def"},{"where":"type","name":"IsIntegrallyClosed","module":"Mathlib.RingTheory.IntegralClosure.IntegrallyClosed","kind":"abbrev"},{"where":"type","name":"IsScalarTower","module":"Mathlib.Algebra.Group.Action.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.map","module":"Mathlib.Algebra.Polynomial.Eval.Defs","kind":"def"},{"where":"type","name":"minpoly","module":"Mathlib.FieldTheory.Minpoly.Basic","kind":"def"}],
      "range": {"start":{"line":54,"column":0},"end":{"line":60,"column":99}},
      "name": "minpoly.isIntegrallyClosed_eq_field_fractions'",
      "module": "Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [IsDomain R] [inst_3 : Algebra R S]\n  (K : Type u_3) [inst_4 : Field K] [inst_5 : Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R] [IsDomain S]\n  [inst_9 : Algebra K S] [IsScalarTower R K S] {s : S},\n  IsIntegral R s → minpoly K s = Polynomial.map (algebraMap R K) (minpoly R s)",
      "doc": "For integrally closed domains, the minimal polynomial over the ring is the same as the minimal\npolynomial over the fraction field. Compared to `minpoly.isIntegrallyClosed_eq_field_fractions`,\nthis version is useful if the element is in a ring that is already a `K`-algebra. ",
      "short": "isIntegrallyClosed_eq_field_fractions'",
      "signature_source": "theorem isIntegrallyClosed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S]\n    {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) :=",
      "body_source": "by\n  let L := FractionRing S\n  rw [← isIntegrallyClosed_eq_field_fractions K L hs, algebraMap_eq (IsFractionRing.injective S L)]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
