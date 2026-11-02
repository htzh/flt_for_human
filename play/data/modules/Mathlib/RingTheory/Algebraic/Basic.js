window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Algebraic.Basic"] = {
  "module": "Mathlib.RingTheory.Algebraic.Basic",
  "cards": {
    "Polynomial.algEquivOfTranscendental": {
      "refs": [{"where":"type","name":"AlgEquiv","module":"Mathlib.Algebra.Algebra.Equiv","kind":"inductive"},{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.adjoin","module":"Mathlib.Algebra.Algebra.Subalgebra.Lattice","kind":"def"},{"where":"type","name":"Algebra.id","module":"Mathlib.Algebra.Algebra.Defs","kind":"def"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Polynomial","module":"Mathlib.Algebra.Polynomial.Basic","kind":"inductive"},{"where":"type","name":"Polynomial.algebraOfAlgebra","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Set","module":"Mathlib.Data.Set.Defs","kind":"def"},{"where":"type","name":"Subalgebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"inductive"},{"where":"type","name":"Subalgebra.algebra","module":"Mathlib.Algebra.Algebra.Subalgebra.Basic","kind":"def"},{"where":"type","name":"Transcendental","module":"Mathlib.RingTheory.Algebraic.Defs","kind":"def"},{"where":"body","name":"AlgEquiv.ofBijective","module":"Mathlib.Algebra.Algebra.Equiv","kind":"def"},{"where":"body","name":"Polynomial.aeval","module":"Mathlib.Algebra.Polynomial.AlgebraMap","kind":"def"}],
      "range": {"start":{"line":590,"column":0},"end":{"line":600,"column":27}},
      "name": "Polynomial.algEquivOfTranscendental",
      "module": "Mathlib.RingTheory.Algebraic.Basic",
      "kind": "def",
      "elaborated_type": "(R : Type u_1) →\n  {S : Type u_2} →\n    [inst : CommRing R] →\n      [inst_1 : Ring S] → [inst_2 : Algebra R S] → (s : S) → Transcendental R s → Polynomial R ≃ₐ[R] ↥R[s]",
      "doc": "Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence\nbetween `R[X]` and `R[s]` given by sending `X` to `s`. ",
      "short": "algEquivOfTranscendental",
      "signature_source": "noncomputable def algEquivOfTranscendental (s : S) (h : Transcendental R s) :\n    R[X] ≃ₐ[R] R[s] :=",
      "body_source": "AlgEquiv.ofBijective (aeval ⟨s, self_mem_adjoin_singleton R s⟩) <| by\n    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩\n    · rwa [Subalgebra.transcendental_iff_transcendental_val]\n    rw [← AlgHom.range_eq_top, _root_.eq_top_iff]\n    rintro ⟨t, ht⟩ _\n    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht\n    exact ⟨r, by ext; simp⟩",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean",
      "has_source": true,
      "has_refs": true
    },
    "Transcendental.pow": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Ring","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Transcendental","module":"Mathlib.RingTheory.Algebraic.Defs","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":377,"column":0},"end":{"line":378,"column":61}},
      "name": "Transcendental.pow",
      "module": "Mathlib.RingTheory.Algebraic.Basic",
      "kind": "theorem",
      "elaborated_type": "∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {r : A},\n  Transcendental R r → ∀ {n : ℕ}, 0 < n → Transcendental R (r ^ n)",
      "doc": "",
      "short": "pow",
      "signature_source": "theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :\n    Transcendental R (r ^ n) :=",
      "body_source": "fun ht' ↦ ht <| ht'.of_pow hn",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
