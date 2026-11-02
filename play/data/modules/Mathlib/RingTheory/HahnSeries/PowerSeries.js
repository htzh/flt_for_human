window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.HahnSeries.PowerSeries"] = {
  "module": "Mathlib.RingTheory.HahnSeries.PowerSeries",
  "cards": {
    "HahnSeries.ofPowerSeries": {
      "refs": [{"where":"type","name":"HahnSeries","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"inductive"},{"where":"type","name":"IsStrictOrderedRing","module":"Mathlib.Algebra.Order.Ring.Defs","kind":"inductive"},{"where":"type","name":"PartialOrder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"},{"where":"type","name":"PowerSeries","module":"Mathlib.RingTheory.PowerSeries.Basic","kind":"abbrev"},{"where":"type","name":"RingHom","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"inductive"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Unit","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"HahnSeries.embDomainRingHom","module":"Mathlib.RingTheory.HahnSeries.Multiplication","kind":"def"},{"where":"body","name":"Nat.castAddMonoidHom","module":"Mathlib.Data.Nat.Cast.Basic","kind":"def"},{"where":"body","name":"RingEquiv.symm","module":"Mathlib.Algebra.Ring.Equiv","kind":"def"},{"where":"body","name":"RingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":89,"column":0},"end":{"line":93,"column":44}},
      "name": "HahnSeries.ofPowerSeries",
      "module": "Mathlib.RingTheory.HahnSeries.PowerSeries",
      "kind": "def",
      "elaborated_type": "(Γ : Type u_1) →\n  (R : Type u_2) →\n    [inst : Semiring R] →\n      [inst_1 : Semiring Γ] →\n        [inst_2 : PartialOrder Γ] → [inst_3 : IsStrictOrderedRing Γ] → PowerSeries R →+* HahnSeries Γ R",
      "doc": "Casts a power series as a Hahn series with coefficients from a strictly ordered semiring. ",
      "short": "ofPowerSeries",
      "signature_source": "def ofPowerSeries : PowerSeries R →+* R⟦Γ⟧ :=",
      "body_source": "(HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>\n        Nat.cast_le).comp\n    (RingEquiv.toRingHom toPowerSeries.symm)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/PowerSeries.lean",
      "has_source": true,
      "has_refs": true
    },
    "HahnSeries.powerSeriesAlgebra": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommSemiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"HahnSeries","module":"Mathlib.RingTheory.HahnSeries.Basic","kind":"inductive"},{"where":"type","name":"IsStrictOrderedRing","module":"Mathlib.Algebra.Order.Ring.Defs","kind":"inductive"},{"where":"type","name":"PartialOrder","module":"Mathlib.Order.Defs.PartialOrder","kind":"inductive"},{"where":"type","name":"PowerSeries","module":"Mathlib.RingTheory.PowerSeries.Basic","kind":"abbrev"},{"where":"type","name":"Semiring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Unit","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"Algebra.algebraMap","module":"Mathlib.Algebra.Algebra.Defs","kind":"abbrev"},{"where":"body","name":"HahnSeries.ofPowerSeries","module":"Mathlib.RingTheory.HahnSeries.PowerSeries","kind":"def"},{"where":"body","name":"RingHom.comp","module":"Mathlib.Algebra.Ring.Hom.Defs","kind":"def"}],
      "range": {"start":{"line":217,"column":0},"end":{"line":219,"column":78}},
      "name": "HahnSeries.powerSeriesAlgebra",
      "module": "Mathlib.RingTheory.HahnSeries.PowerSeries",
      "kind": "def",
      "elaborated_type": "(Γ : Type u_1) →\n  (R : Type u_2) →\n    [inst : CommSemiring R] →\n      [inst_1 : Semiring Γ] →\n        [inst_2 : PartialOrder Γ] →\n          [inst_3 : IsStrictOrderedRing Γ] →\n            {S : Type u_4} → [inst_4 : CommSemiring S] → [Algebra S (PowerSeries R)] → Algebra S (HahnSeries Γ R)",
      "doc": "",
      "short": "powerSeriesAlgebra",
      "signature_source": "instance powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)] :\n    Algebra S R⟦Γ⟧ :=",
      "body_source": "RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/PowerSeries.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
