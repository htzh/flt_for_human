window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.EssentialFiniteness"] = {
  "module": "Mathlib.RingTheory.EssentialFiniteness",
  "cards": {
    "Algebra.EssFiniteType": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":32,"column":0},"end":{"line":42,"column":87}},
      "name": "Algebra.EssFiniteType",
      "module": "Mathlib.RingTheory.EssentialFiniteness",
      "kind": "inductive",
      "elaborated_type": "(R : Type u_1) → (S : Type u_2) → [inst : CommRing R] → [inst_1 : CommRing S] → [Algebra R S] → Prop",
      "doc": "An `R`-algebra is essentially of finite type if\nit is the localization of an algebra of finite type.\nSee `essFiniteType_iff_exists_subalgebra`.\n\nFor field extensions, this is equivalent to being finitely generated as a field.\nSee `IntermediateField.fg_top_iff`.\n",
      "short": "EssFiniteType",
      "signature_source": "class EssFiniteType : Prop where\n  cond : ∃ s : Finset S,\n    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (s : Set S)) S)) S",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/EssentialFiniteness.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
