window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Etale.Basic"] = {
  "module": "Mathlib.RingTheory.Etale.Basic",
  "cards": {
    "Algebra.FormallyEtale": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"}],
      "range": {"start":{"line":44,"column":0},"end":{"line":49,"column":59}},
      "name": "Algebra.FormallyEtale",
      "module": "Mathlib.RingTheory.Etale.Basic",
      "kind": "inductive",
      "elaborated_type": "(R : Type u) → (A : Type v) → [inst : CommRing R] → [inst_1 : CommRing A] → [Algebra R A] → Prop",
      "doc": "An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{A/R})` are zero.\nFor the infinitesimal lifting definition, see `FormallyEtale.iff_comp_bijective`. ",
      "short": "FormallyEtale",
      "signature_source": "@[mk_iff, stacks 00UQ]\nclass FormallyEtale : Prop where\n  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]\n  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Algebra.FormallyEtale.of_isLocalization": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.FormallyEtale","module":"Mathlib.RingTheory.Etale.Basic","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"IsLocalization","module":"Mathlib.RingTheory.Localization.Defs","kind":"abbrev"},{"where":"type","name":"Submonoid","module":"Mathlib.Algebra.Group.Submonoid.Defs","kind":"inductive"}],
      "range": {"start":{"line":179,"column":0},"end":{"line":181,"column":80}},
      "name": "Algebra.FormallyEtale.of_isLocalization",
      "module": "Mathlib.RingTheory.Etale.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u_2} {Rₘ : Type u_4} [inst : CommRing R] [inst_1 : CommRing Rₘ] (M : Submonoid R) [inst_2 : Algebra R Rₘ]\n  [IsLocalization M Rₘ], Algebra.FormallyEtale R Rₘ",
      "doc": "",
      "short": "of_isLocalization",
      "signature_source": "theorem of_isLocalization : FormallyEtale R Rₘ :=",
      "body_source": "FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr\n    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
