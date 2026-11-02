window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.HahnSeries.Basic"] = {
  "module": "Mathlib.RingTheory.HahnSeries.Basic",
  "cards": {
    "HahnSeries": {
      "refs": [{"where":"type","name":"PartialOrder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":50,"column":0},"end":{"line":56,"column":49}},
      "name": "HahnSeries",
      "module": "Mathlib.RingTheory.HahnSeries.Basic",
      "kind": "inductive",
      "elaborated_type": "(Γ : Type u_1) → (R : Type u_2) → [PartialOrder Γ] → [Zero R] → Type (max u_1 u_2)",
      "doc": "If `Γ` is linearly ordered and `R` has zero, then `R⟦Γ⟧` consists of\nformal series over `Γ` with coefficients in `R`, whose supports are well-founded. ",
      "short": "HahnSeries",
      "signature_source": "@[ext]\nstructure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where\n  /-- The coefficient function of a Hahn Series. -/\n  coeff : Γ → R\n  isPWO_support' : (Function.support coeff).IsPWO",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "HahnSeries.single": {
      "refs": [{"where":"type","name":"HahnSeries","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"inductive"},{"where":"type","name":"PartialOrder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"},{"where":"type","name":"ZeroHom","module":"Mathlib.Algebra.Group.Hom.Defs","kind":"inductive"},{"where":"type","name":"Zero","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"Pi.single","module":"Mathlib.Algebra.Notation.Pi.Basic","kind":"def"},{"where":"body","name":"Classical.propDecidable","module":"Init.Classical","kind":"def"}],
      "range": {"start":{"line":193,"column":0},"end":{"line":198,"column":48}},
      "name": "HahnSeries.single",
      "module": "Mathlib.RingTheory.HahnSeries.Basic",
      "kind": "def",
      "elaborated_type": "{Γ : Type u_1} → {R : Type u_3} → [inst : PartialOrder Γ] → [inst_1 : Zero R] → Γ → ZeroHom R (HahnSeries Γ R)",
      "doc": "`single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. ",
      "short": "single",
      "signature_source": "def single (a : Γ) : ZeroHom R R⟦Γ⟧ where\n  toFun r :=\n    { coeff := Pi.single a r\n      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }\n  map_zero' := HahnSeries.ext (Pi.single_zero _)",
      "body_source": "",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
