window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.RingTheory.Etale.Field"] = {
  "module": "Mathlib.RingTheory.Etale.Field",
  "cards": {
    "Algebra.FormallyEtale.of_isSeparable": {
      "refs": [{"where":"type","name":"Algebra","module":"Mathlib.Algebra.Algebra.Defs","kind":"inductive"},{"where":"type","name":"Algebra.FormallyEtale","module":"Mathlib.RingTheory.Etale.Basic","kind":"inductive"},{"where":"type","name":"Algebra.IsSeparable","module":"Mathlib.FieldTheory.Separable","kind":"inductive"},{"where":"type","name":"Field","module":"Mathlib.Algebra.Field.Defs","kind":"inductive"}],
      "range": {"start":{"line":98,"column":0},"end":{"line":156,"column":81}},
      "name": "Algebra.FormallyEtale.of_isSeparable",
      "module": "Mathlib.RingTheory.Etale.Field",
      "kind": "theorem",
      "elaborated_type": "∀ (K : Type u_1) (L : Type u_2) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [Algebra.IsSeparable K L],\n  Algebra.FormallyEtale K L",
      "doc": "",
      "short": "of_isSeparable",
      "signature_source": "lemma of_isSeparable [Algebra.IsSeparable K L] : FormallyEtale K L :=",
      "body_source": "by\n  -- We shall show that any `f : L → B/I` can be lifted to `L → B` if `I^2 = ⊥`.\n  refine FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h ↦ ?_\n  -- But we already know that there exists a unique lift for every finite subfield of `L`\n  -- by `of_isSeparable_aux`, so we can glue them all together.\n  refine ⟨FormallyUnramified.iff_comp_injective_of_small.mp\n    (FormallyUnramified.of_isSeparable K L) I h, ?_⟩\n  intro f\n  have : ∀ k : L, ∃! g : K⟮k⟯ →ₐ[K] B,\n      (Ideal.Quotient.mkₐ K I).comp g = f.comp (IsScalarTower.toAlgHom K _ L) := by\n    intro k\n    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮k⟯) L)\n    have := IntermediateField.adjoin.finiteDimensional\n      (Algebra.IsSeparable.isSeparable K k).isIntegral\n    have := FormallyEtale.of_isSeparable_aux K (K⟮k⟯)\n    have := FormallyEtale.comp_bijective (R := K) (A := K⟮k⟯) I h\n    exact this.existsUnique _\n  choose g hg₁ hg₂ using this\n  have hg₃ : ∀ x y (h : x ∈ K⟮y⟯), g y ⟨x, h⟩ = g x (IntermediateField.AdjoinSimple.gen K x) := by\n    intro x y h\n    have e : K⟮x⟯ ≤ K⟮y⟯ := by\n      rw [IntermediateField.adjoin_le_iff]\n      rintro _ rfl\n      exact h\n    rw [← hg₂ _ ((g _).comp (IntermediateField.inclusion e))]\n    · rfl\n    apply AlgHom.ext\n    rw [← AlgHom.comp_assoc, hg₁, AlgHom.comp_assoc]\n    simp -implicitDefEqProofs\n  have H : ∀ x y : L, ∃ α : L, x ∈ K⟮α⟯ ∧ y ∈ K⟮α⟯ := by\n    intro x y\n    have : FiniteDimensional K K⟮x, y⟯ := by\n      apply IntermediateField.finiteDimensional_adjoin\n      intro x _; exact (Algebra.IsSeparable.isSeparable K x).isIntegral\n    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮x, y⟯) L)\n    obtain ⟨⟨α, hα⟩, e⟩ := Field.exists_primitive_element K K⟮x, y⟯\n    apply_fun (IntermediateField.map (IntermediateField.val _)) at e\n    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map] at e\n    simp only [IntermediateField.coe_val, Set.image_singleton,\n      IntermediateField.fieldRange_val] at e\n    have hx : x ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)\n    have hy : y ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)\n    exact ⟨α, hx, hy⟩\n  refine ⟨⟨⟨⟨⟨fun x ↦ g x (IntermediateField.AdjoinSimple.gen K x), ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩\n  · change g 1 1 = 1; rw [map_one]\n  · intro x y\n    obtain ⟨α, hx, hy⟩ := H x y\n    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_mul, ← hg₃ _ _ (mul_mem hx hy)]\n    rfl\n  · change g 0 0 = 0; rw [map_zero]\n  · intro x y\n    obtain ⟨α, hx, hy⟩ := H x y\n    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_add, ← hg₃ _ _ (add_mem hx hy)]\n    rfl\n  · intro r\n    change g _ (algebraMap K _ r) = _\n    rw [AlgHom.commutes]\n  · ext x\n    simpa using AlgHom.congr_fun (hg₁ x) (IntermediateField.AdjoinSimple.gen K x)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Field.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
