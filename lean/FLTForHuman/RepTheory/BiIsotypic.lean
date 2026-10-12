/-
  The multiplicity-one engine for the type algebra.

  `BiIsotypic` proves that for a finite-dimensional `k`-representation `τ` of a group
  `K` over an algebraically closed field `k`, the two-sided translates of the
  algebra-invariants of a `τ`-isotypic module span the whole module
  (`span_translates_invariants_eq_top'`), and assembles the contraction (`exists_matrix_of_commute`,
  `mem_span_range_of_isIsotypicOfType_dual'`) and the pairing
  (`pairing_symm_of_mem_typeSpan`) that make the two kernels of the projected identity
  equal. This is the real mathematics of the right-convolution commutation proof; the
  `leftRep`/`rightRep`/`invMap` block spells the two-sided action on functions and
  `mem_typeSpan_leftRep_of_inv_mem` is the `h(x⁻¹)` half of bi-finiteness.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean:2210–3200`
  (the `BiIsotypic` namespace, pinned `aa2d8b3`). The pin declares the whole namespace
  `private`; here it is the shared engine and is public, so the statements are verbatim
  and every declaration lands as a promotion. The engine stays stated over
  `Representation k K W`, exactly as the pin writes it — no adèlic spelling.
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

-- The pin's `haveI` walls feed instance search (the isotypic-component algebra).
set_option linter.style.haveILetI false

set_option autoImplicit false

noncomputable section

namespace BiIsotypic

open Module

variable {k K W : Type*} [Field k] [Group K] [AddCommGroup W] [Module k W]

section Density

variable [IsAlgClosed k] [FiniteDimensional k W] (τ : Representation k K W) [τ.IsIrreducible]

omit [IsAlgClosed k] [FiniteDimensional k W] [τ.IsIrreducible] in

theorem asAlgebraHom_mem_span_range (r : MonoidAlgebra k K) :
    (τ.asAlgebraHom r : W →ₗ[k] W) ∈
      Submodule.span k (Set.range fun g : K => (τ g : W →ₗ[k] W)) := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  refine Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

set_option backward.isDefEq.respectTransparency false in

theorem mem_span_range (φ : W →ₗ[k] W) :
    φ ∈ Submodule.span k (Set.range fun g : K => (τ g : W →ₗ[k] W)) := by
  classical
  have hS := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
    (A := MonoidAlgebra k K) (V := τ.asModule)

  let φ' : τ.asModule →ₗ[Module.End (MonoidAlgebra k K) τ.asModule] τ.asModule :=
    { toFun := fun m => τ.asModuleEquiv.symm (φ (τ.asModuleEquiv m))
      map_add' := fun x y => by simp
      map_smul' := fun e m => by
        obtain ⟨c, rfl⟩ := hS.2 e
        change τ.asModuleEquiv.symm (φ (τ.asModuleEquiv
            ((algebraMap k (Module.End (MonoidAlgebra k K) τ.asModule) c) m))) =
          (algebraMap k (Module.End (MonoidAlgebra k K) τ.asModule) c)
            (τ.asModuleEquiv.symm (φ (τ.asModuleEquiv m)))
        rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearEquiv.map_smul,
          LinearMap.map_smul, LinearEquiv.map_smul] }
  let b := Module.finBasis k W
  obtain ⟨r, hr⟩ := jacobson_density (R := MonoidAlgebra k K) (M := τ.asModule) φ'
    (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
  have hφ : φ = (τ.asAlgebraHom r : W →ₗ[k] W) := by
    refine b.ext fun i => ?_
    have hi := hr (τ.asModuleEquiv.symm (b i))
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have := congrArg τ.asModuleEquiv hi
    simpa [φ'] using this
  rw [hφ]
  exact asAlgebraHom_mem_span_range τ r

theorem exists_finsupp_sum_eq (φ : W →ₗ[k] W) :
    ∃ c : K →₀ k, (c.sum fun g a => a • (τ g : W →ₗ[k] W)) = φ := by
  have h := mem_span_range τ φ
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h
  exact h

end Density

section Contraction

variable {X : Type*} [AddCommGroup X] [Module k X] {ι : Type*} [Fintype ι]

theorem sum_apply_coord_eq {ι' : Type*} [Fintype ι'] (B : W →ₗ[k] Module.Dual k W →ₗ[k] X)
    (b : Basis ι k W) (b' : Basis ι' k W) :
    (∑ q, B (b' q) (b'.coord q)) = ∑ p, B (b p) (b.coord p) := by
  classical
  symm
  calc (∑ p, B (b p) (b.coord p))
      = ∑ p, B (b p) (∑ q, (b.coord p) (b' q) • b'.coord q) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Basis.sum_dual_apply_smul_coord]
    _ = ∑ q, B (∑ p, (b.coord p) (b' q) • b p) (b'.coord q) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
        rw [Finset.sum_comm]
    _ = ∑ q, B (b' q) (b'.coord q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 1
        simp [Basis.coord_apply]

theorem sum_apply_map_eq (B : W →ₗ[k] Module.Dual k W →ₗ[k] X) (b : Basis ι k W)
    (A : W ≃ₗ[k] W) :
    (∑ q, B (A (b q)) ((b.coord q) ∘ₗ (A.symm : W →ₗ[k] W))) = ∑ p, B (b p) (b.coord p) := by
  classical
  have h := sum_apply_coord_eq (k := k) B b (b.map A)
  refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h
  have h1 : A (b q) = b.map A q := by simp
  have h2 : (b.coord q) ∘ₗ (A.symm : W →ₗ[k] W) = (b.map A).coord q := by
    ext v; simp [Basis.coord_apply]
  rw [h1, h2]

end Contraction

section Engine

variable [IsAlgClosed k] [FiniteDimensional k W] (τ : Representation k K W) [τ.IsIrreducible]
variable {N : Type*} [AddCommGroup N] [Module k N] [FiniteDimensional k N]
  (L R : Representation k K N)

omit [IsAlgClosed k] [FiniteDimensional k W] [τ.IsIrreducible] in
set_option backward.isDefEq.respectTransparency false in

theorem exists_equiv_pi' {M : Type*} [AddCommGroup M] [Module k M]
    [Module (MonoidAlgebra k K) M] [IsScalarTower k (MonoidAlgebra k K) M]
    [IsSemisimpleModule (MonoidAlgebra k K) M]
    (hi : IsIsotypicOfType (MonoidAlgebra k K) M τ.asModule) (eL : M ≃ₗ[k] N)
    (heL : ∀ (g : K) (m : M), eL (MonoidAlgebra.of k K g • m) = L g (eL m)) :
    ∃ (n : ℕ) (Ψ : N ≃ₗ[k] (Fin n → W)), ∀ (g : K) (x : N) (i : Fin n),
      Ψ (L g x) i = τ g (Ψ x i) := by
  haveI : Module.Finite k M := Module.Finite.equiv eL.symm
  haveI : Module.Finite (MonoidAlgebra k K) M :=
    Module.Finite.of_restrictScalars_finite k (MonoidAlgebra k K) M
  obtain ⟨n, ⟨e⟩⟩ := hi.linearEquiv_fun
  refine ⟨n, eL.symm ≪≫ₗ e.restrictScalars k ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => τ.asModuleEquiv), fun g x i => ?_⟩
  have hx : L g x = eL (MonoidAlgebra.of k K g • eL.symm x) := by
    rw [heL, LinearEquiv.apply_symm_apply]
  simp only [hx, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.restrictScalars_apply, map_smul, Pi.smul_apply,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

omit [IsAlgClosed k] [FiniteDimensional k W] [τ.IsIrreducible] in
set_option backward.isDefEq.respectTransparency false in

theorem exists_equiv_pi [hs : IsSemisimpleModule (MonoidAlgebra k K) L.asModule]
    (hi : IsIsotypicOfType (MonoidAlgebra k K) L.asModule τ.asModule) :
    ∃ (n : ℕ) (Ψ : N ≃ₗ[k] (Fin n → W)), ∀ (g : K) (x : N) (i : Fin n),
      Ψ (L g x) i = τ g (Ψ x i) :=
  exists_equiv_pi' τ L hi L.asModuleEquiv fun g m => by
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

omit [FiniteDimensional k N] in

theorem exists_matrix_of_commute {n : ℕ} (Ψ : N ≃ₗ[k] (Fin n → W))
    (hΨ : ∀ (g : K) (x : N) (i : Fin n), Ψ (L g x) i = τ g (Ψ x i))
    (T : N →ₗ[k] N) (hT : ∀ g, T ∘ₗ L g = L g ∘ₗ T) :
    ∃ c : Fin n → Fin n → k, ∀ (x : N) (i : Fin n), Ψ (T x) i = ∑ j, c i j • Ψ x j := by
  classical

  have hblock : ∀ i j : Fin n, ∃ c : k, ∀ w : W,
      Ψ (T (Ψ.symm (Pi.single j w))) i = c • w := by
    intro i j
    let f : W →ₗ[k] W :=
      (LinearMap.proj i).comp ((Ψ : N →ₗ[k] (Fin n → W)).comp (T.comp
        ((Ψ.symm : (Fin n → W) →ₗ[k] N).comp (LinearMap.single k (fun _ : Fin n => W) j))))
    have hf : ∀ (g : K) (w : W), f (τ g w) = τ g (f w) := by
      intro g w
      have h1 : Ψ.symm (Pi.single j (τ g w)) = L g (Ψ.symm (Pi.single j w)) := by
        apply Ψ.injective
        ext i'
        rw [LinearEquiv.apply_symm_apply, hΨ, LinearEquiv.apply_symm_apply]
        by_cases h : i' = j
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      have h2 : T (L g (Ψ.symm (Pi.single j w))) = L g (T (Ψ.symm (Pi.single j w))) := by
        simpa using congrArg (fun φ : N →ₗ[k] N => φ (Ψ.symm (Pi.single j w))) (hT g)
      simp only [f, LinearMap.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe,
        LinearMap.proj_apply, h1, h2, hΨ]
    let F : τ.IntertwiningMap τ := f.intertwiningMap_of_isIntertwiningMap τ τ hf
    obtain ⟨c, hc⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := τ)).2 F
    refine ⟨c, fun w => ?_⟩
    have h1 : (F : W → W) w = c • w := by
      rw [← hc, Representation.IntertwiningMap.algebraMap_apply,
        Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.coe_one, id]
    simpa [F, f] using h1
  choose c hc using hblock
  refine ⟨c, fun x i => ?_⟩

  have hx : x = ∑ j, Ψ.symm (Pi.single j (Ψ x j)) := by
    apply Ψ.injective
    rw [map_sum]
    simp only [LinearEquiv.apply_symm_apply]
    exact (Finset.univ_sum_single (Ψ x)).symm
  conv_lhs => rw [hx]
  simp only [map_sum, Finset.sum_apply, hc]

omit [IsAlgClosed k] [FiniteDimensional k W] [τ.IsIrreducible] [FiniteDimensional k N] in
set_option backward.isDefEq.respectTransparency false in

theorem mem_span_range_of_isIsotypicOfType_dual' {M : Type*} [AddCommGroup M] [Module k M]
    [Module (MonoidAlgebra k K) M] [IsScalarTower k (MonoidAlgebra k K) M]
    [IsSemisimpleModule (MonoidAlgebra k K) M]
    (hi : IsIsotypicOfType (MonoidAlgebra k K) M τ.dual.asModule) (eR : M ≃ₗ[k] N)
    (heR : ∀ (g : K) (m : M), eR (MonoidAlgebra.of k K g • m) = R g (eR m)) (x : N) :
    x ∈ Submodule.span k {y : N | ∃ T : Module.Dual k W →ₗ[k] N,
      (∀ (g : K) (μ : Module.Dual k W), T (τ.dual g μ) = R g (T μ)) ∧ y ∈ LinearMap.range T} := by
  set P : Submodule k N := Submodule.span k {y : N | ∃ T : Module.Dual k W →ₗ[k] N,
      (∀ (g : K) (μ : Module.Dual k W), T (τ.dual g μ) = R g (T μ)) ∧ y ∈ LinearMap.range T}
  have htop := IsSemisimpleModule.sSup_simples_eq_top (R := MonoidAlgebra k K) (M := M)
  have hx : eR.symm x ∈ sSup {m : Submodule (MonoidAlgebra k K) M |
      IsSimpleModule (MonoidAlgebra k K) m} := by
    rw [htop]; exact Submodule.mem_top
  rw [sSup_eq_iSup'] at hx
  suffices h : ∀ m ∈ (⨆ m : {m : Submodule (MonoidAlgebra k K) M |
      IsSimpleModule (MonoidAlgebra k K) m}, (m : Submodule (MonoidAlgebra k K) M)),
      eR m ∈ P by
    simpa using h _ hx
  intro m hm
  induction hm using Submodule.iSup_induction' with
  | mem S y hy =>
    obtain ⟨S, hS⟩ := S
    haveI : IsSimpleModule (MonoidAlgebra k K) S := hS
    obtain ⟨e⟩ := hi S

    let T : Module.Dual k W →ₗ[k] N :=
      (eR : M →ₗ[k] N) ∘ₗ ((S.subtype ∘ₗ (e.symm : τ.dual.asModule →ₗ[
        MonoidAlgebra k K] S)).restrictScalars k) ∘ₗ
        (τ.dual.asModuleEquiv.symm : Module.Dual k W →ₗ[k] τ.dual.asModule)
    refine Submodule.subset_span ⟨T, fun g μ => ?_, ⟨τ.dual.asModuleEquiv (e ⟨y, hy⟩), ?_⟩⟩
    · simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
        Representation.asModuleEquiv_symm_map_rho, map_smul, Submodule.subtype_apply, heR]
    · simp [T]
  | zero => simp
  | add y z _ _ hy hz => simpa using P.add_mem hy hz

omit [IsAlgClosed k] [FiniteDimensional k W] [τ.IsIrreducible] [FiniteDimensional k N] in
set_option backward.isDefEq.respectTransparency false in

theorem mem_span_range_of_isIsotypicOfType_dual
    [hs : IsSemisimpleModule (MonoidAlgebra k K) R.asModule]
    (hi : IsIsotypicOfType (MonoidAlgebra k K) R.asModule τ.dual.asModule) (x : N) :
    x ∈ Submodule.span k {y : N | ∃ T : Module.Dual k W →ₗ[k] N,
      (∀ (g : K) (μ : Module.Dual k W), T (τ.dual g μ) = R g (T μ)) ∧ y ∈ LinearMap.range T} :=
  mem_span_range_of_isIsotypicOfType_dual' τ R hi R.asModuleEquiv (fun g m => by
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]) x

set_option backward.isDefEq.respectTransparency false in

theorem span_translates_invariants_eq_top'
    {ML : Type*} [AddCommGroup ML] [Module k ML] [Module (MonoidAlgebra k K) ML]
    [IsScalarTower k (MonoidAlgebra k K) ML] [IsSemisimpleModule (MonoidAlgebra k K) ML]
    (hL : IsIsotypicOfType (MonoidAlgebra k K) ML τ.asModule) (eL : ML ≃ₗ[k] N)
    (heL : ∀ (g : K) (m : ML), eL (MonoidAlgebra.of k K g • m) = L g (eL m))
    {MR : Type*} [AddCommGroup MR] [Module k MR] [Module (MonoidAlgebra k K) MR]
    [IsScalarTower k (MonoidAlgebra k K) MR] [IsSemisimpleModule (MonoidAlgebra k K) MR]
    (hR : IsIsotypicOfType (MonoidAlgebra k K) MR τ.dual.asModule) (eR : MR ≃ₗ[k] N)
    (heR : ∀ (g : K) (m : MR), eR (MonoidAlgebra.of k K g • m) = R g (eR m))
    (hLR : ∀ a b : K, L a ∘ₗ R b = R b ∘ₗ L a) :
    Submodule.span k {y : N | ∃ (a : K) (n₀ : N), (∀ g : K, L g (R g n₀) = n₀) ∧ y = L a n₀}
      = ⊤ := by
  classical
  set P : Submodule k N :=
    Submodule.span k {y : N | ∃ (a : K) (n₀ : N), (∀ g : K, L g (R g n₀) = n₀) ∧ y = L a n₀}

  obtain ⟨n, Ψ, hΨ⟩ := exists_equiv_pi' τ L hL eL heL
  have hRc : ∀ b : K, ∃ c : Fin n → Fin n → k, ∀ (x : N) (i : Fin n),
      Ψ (R b x) i = ∑ j, c i j • Ψ x j :=
    fun b => exists_matrix_of_commute τ L Ψ hΨ (R b) fun g => (hLR g b).symm
  choose σc hσc using hRc

  let B₀ : (Module.Dual k W →ₗ[k] (Fin n → k)) → W →ₗ[k] Module.Dual k W →ₗ[k] (Fin n → W) :=
    fun s => LinearMap.mk₂ k (fun w μ i => s μ i • w)
      (fun w₁ w₂ μ => by ext i; simp [smul_add])
      (fun a w μ => by ext i; simp [smul_comm a])
      (fun w μ₁ μ₂ => by ext i; simp [add_smul])
      (fun a w μ => by ext i; simp [mul_smul])
  let Φ : (Module.Dual k W →ₗ[k] (Fin n → k)) → W →ₗ[k] Module.Dual k W →ₗ[k] N := fun s =>
    (B₀ s).compr₂ (Ψ.symm : (Fin n → W) →ₗ[k] N)
  have hΦ : ∀ s w μ, Φ s w μ = Ψ.symm (fun i => s μ i • w) := fun _ _ _ => rfl

  have hΦL : ∀ s w μ (a : K), L a (Φ s w μ) = Φ s (τ a w) μ := by
    intro s w μ a
    rw [hΦ, hΦ]; apply Ψ.injective; ext i
    rw [hΨ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul]

  have hΦR : ∀ s, (∀ (b : K) (μ : Module.Dual k W) (i : Fin n),
      s (τ.dual b μ) i = ∑ j, σc b i j * s μ j) →
      ∀ w μ (b : K), R b (Φ s w μ) = Φ s w (τ.dual b μ) := by
    intro s hs w μ b
    rw [hΦ, hΦ]; apply Ψ.injective; ext i
    rw [hσc, LinearEquiv.apply_symm_apply]
    simp only [LinearEquiv.apply_symm_apply, hs, Finset.sum_smul, smul_smul]

  have hP : ∀ (n₀ : N), (∀ g : K, L g (R g n₀) = n₀) → ∀ (c : K →₀ k),
      (c.sum fun g a => a • (L g : N →ₗ[k] N)) n₀ ∈ P := by
    intro n₀ hn₀ c
    rw [Finsupp.sum, LinearMap.sum_apply]
    refine P.sum_mem fun g _ => ?_
    rw [LinearMap.smul_apply]
    exact P.smul_mem _ (Submodule.subset_span ⟨g, n₀, hn₀, rfl⟩)

  have hkey : ∀ s, (∀ (b : K) (μ : Module.Dual k W) (i : Fin n),
      s (τ.dual b μ) i = ∑ j, σc b i j * s μ j) → ∀ w μ, Φ s w μ ∈ P := by
    intro s hs w μ
    let b := Module.finBasis k W

    let u : N := ∑ q, Φ s (b q) (b.coord q)
    have hu : ∀ g : K, L g (R g u) = u := by
      intro g
      simp only [u, map_sum, hΦR s hs, hΦL]

      let A : W ≃ₗ[k] W := LinearEquiv.ofLinearMap (τ g) (τ g⁻¹)
        (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_eq_id])
        (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_eq_id])
      have hA : ∀ q, τ.dual g (b.coord q) = (b.coord q) ∘ₗ (A.symm : W →ₗ[k] W) := by
        intro q; rw [Representation.dual_apply]; rfl
      simp only [hA]
      exact sum_apply_map_eq (Φ s) b A

    have hstep : ∀ p, Φ s w (b.coord p) ∈ P := by
      intro p
      obtain ⟨c, hc⟩ := exists_finsupp_sum_eq τ
        ((LinearMap.lsmul k W).flip w ∘ₗ (b.coord p) : W →ₗ[k] W)
      have hcomb : (c.sum fun g a => a • (L g : N →ₗ[k] N)) u = Φ s w (b.coord p) := by
        have hlin : ∀ v μ', (c.sum fun g a => a • (L g : N →ₗ[k] N)) (Φ s v μ') =
            Φ s ((c.sum fun g a => a • (τ g : W →ₗ[k] W)) v) μ' := by
          intro v μ'
          simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hΦL, map_sum,
            LinearMap.map_smul₂]
        simp only [u, map_sum, hlin, hc, LinearMap.comp_apply, LinearMap.flip_apply,
          LinearMap.lsmul_apply, Basis.coord_apply, Basis.repr_self, LinearMap.map_smul₂]
        rw [Finset.sum_eq_single p]
        · simp
        · intro q _ hq; simp [hq]
        · intro h; exact absurd (Finset.mem_univ p) h
      rw [← hcomb]
      exact hP u hu c
    have hμ : μ = ∑ p, μ (b p) • b.coord p := (b.sum_dual_apply_smul_coord μ).symm
    rw [hμ, map_sum]
    exact P.sum_mem fun p _ => by rw [map_smul]; exact P.smul_mem _ (hstep p)

  rw [eq_top_iff]
  rintro x -
  have hx := mem_span_range_of_isIsotypicOfType_dual' τ R hR eR heR x
  refine Submodule.span_le.mpr ?_ hx
  rintro y ⟨T, hT, μ, rfl⟩
  let b := Module.finBasis k W

  let s : Fin (Module.finrank k W) → Module.Dual k W →ₗ[k] (Fin n → k) := fun p =>
    (LinearMap.pi fun i => (b.coord p) ∘ₗ (LinearMap.proj i) ∘ₗ (Ψ : N →ₗ[k] (Fin n → W))) ∘ₗ T
  have hs : ∀ p (b' : K) (μ' : Module.Dual k W) (i : Fin n),
      s p (τ.dual b' μ') i = ∑ j, σc b' i j * s p μ' j := by
    intro p b' μ' i
    simp only [s, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe, hT, hσc, map_sum, map_smul, smul_eq_mul]
  have hTμ : T μ = ∑ p, Φ (s p) (b p) μ := by
    apply Ψ.injective; ext i
    simp only [map_sum, Finset.sum_apply, hΦ, LinearEquiv.apply_symm_apply]
    simp only [s, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe, Basis.coord_apply]
    exact (b.sum_repr (Ψ (T μ) i)).symm
  change T μ ∈ P
  rw [hTμ]
  exact P.sum_mem fun p _ => hkey (s p) (hs p) (b p) μ

set_option backward.isDefEq.respectTransparency false in

theorem span_translates_invariants_eq_top
    [IsSemisimpleModule (MonoidAlgebra k K) L.asModule]
    (hL : IsIsotypicOfType (MonoidAlgebra k K) L.asModule τ.asModule)
    [IsSemisimpleModule (MonoidAlgebra k K) R.asModule]
    (hR : IsIsotypicOfType (MonoidAlgebra k K) R.asModule τ.dual.asModule)
    (hLR : ∀ a b : K, L a ∘ₗ R b = R b ∘ₗ L a) :
    Submodule.span k {y : N | ∃ (a : K) (n₀ : N), (∀ g : K, L g (R g n₀) = n₀) ∧ y = L a n₀}
      = ⊤ :=
  span_translates_invariants_eq_top' τ L R hL L.asModuleEquiv (fun g m => by
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]) hR
    R.asModuleEquiv (fun g m => by
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]) hLR

end Engine

section Ambient

variable [IsAlgClosed k] [FiniteDimensional k W] (τ : Representation k K W) [τ.IsIrreducible]
variable {V : Type*} [AddCommGroup V] [Module k V]

omit [IsAlgClosed k] in

theorem isIrreducible_dual : τ.dual.IsIrreducible := by
  have hτ : τ.IsIrreducible := inferInstance

  haveI : Nontrivial (Subrepresentation τ) := hτ.toNontrivial
  have hbt : (⊥ : Subrepresentation τ) ≠ ⊤ := bot_ne_top
  have hW : Nontrivial W := by
    rw [← Submodule.nontrivial_iff (R := k), nontrivial_iff]
    exact ⟨⊥, ⊤, fun h => hbt (Subrepresentation.toSubmodule_injective h)⟩
  have hW' : Nontrivial (Module.Dual k W) :=
    Module.nontrivial_of_finrank_pos (R := k)
      (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos)
  haveI : Nontrivial (Subrepresentation τ.dual) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule k (Module.Dual k W)) h'
  refine ⟨fun S => ?_⟩

  let C : Subrepresentation τ :=
    ⟨S.toSubmodule.dualCoannihilator, fun g w hw => by
      rw [Submodule.mem_dualCoannihilator] at hw ⊢
      intro μ hμ
      have hμ' : τ.dual g⁻¹ μ ∈ S.toSubmodule := S.apply_mem_toSubmodule g⁻¹ hμ
      have := hw _ hμ'
      rwa [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply] at this⟩
  have hfd : FiniteDimensional k S.toSubmodule := inferInstance
  rcases hτ.eq_bot_or_eq_top C with hC | hC
  · right
    apply Subrepresentation.toSubmodule_injective
    have hC' : S.toSubmodule.dualCoannihilator = ⊥ :=
      congrArg Subrepresentation.toSubmodule hC
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule), hC',
      Submodule.dualAnnihilator_bot]
    rfl
  · left
    apply Subrepresentation.toSubmodule_injective
    have hC' : S.toSubmodule.dualCoannihilator = ⊤ :=
      congrArg Subrepresentation.toSubmodule hC
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule), hC',
      Submodule.dualAnnihilator_top]
    rfl

variable {U : Type*} [AddCommGroup U] [Module k U]

noncomputable def mapA (σ : Representation k K U) (ρ : Representation k K V) (T : U →ₗ[k] V)
    (hT : ∀ (g : K) (u : U), T (σ g u) = ρ g (T u)) :
    σ.asModule →ₗ[MonoidAlgebra k K] ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (T.intertwiningMap_of_isIntertwiningMap σ ρ hT)

omit [IsAlgClosed k] [FiniteDimensional k W] in
theorem mapA_apply (σ : Representation k K U) (ρ : Representation k K V) (T : U →ₗ[k] V)
    (hT : ∀ (g : K) (u : U), T (σ g u) = ρ g (T u)) (u : U) :
    (mapA σ ρ T hT (σ.asModuleEquiv.symm u) : V) = T u := rfl

noncomputable def simples (σ : Representation k K U) (ρ : Representation k K V) :
    Set (Submodule (MonoidAlgebra k K) ρ.asModule) :=
  {m | ∃ (T : U →ₗ[k] V) (hT : ∀ (g : K) (u : U), T (σ g u) = ρ g (T u)),
    m = LinearMap.range (mapA σ ρ T hT) ∧ m ≠ ⊥}

omit [IsAlgClosed k] [FiniteDimensional k W] in
set_option backward.isDefEq.respectTransparency false in
theorem ker_mapA_eq_bot (σ : Representation k K U) [σ.IsIrreducible] (ρ : Representation k K V)
    (T : U →ₗ[k] V) (hT : ∀ (g : K) (u : U), T (σ g u) = ρ g (T u))
    (h : LinearMap.range (mapA σ ρ T hT) ≠ ⊥) : LinearMap.ker (mapA σ ρ T hT) = ⊥ := by
  rcases eq_bot_or_eq_top (LinearMap.ker (mapA σ ρ T hT)) with h' | h'
  · exact h'
  · exact absurd (LinearMap.range_eq_bot.mpr (LinearMap.ker_eq_top.mp h')) h

noncomputable def hull (σ : Representation k K U) (ρ : Representation k K V) :
    Submodule (MonoidAlgebra k K) ρ.asModule :=
  ⨆ m ∈ simples σ ρ, m

omit [IsAlgClosed k] [FiniteDimensional k W] in
set_option backward.isDefEq.respectTransparency false in

theorem isSemisimpleModule_hull (σ : Representation k K U) [σ.IsIrreducible]
    (ρ : Representation k K V) : IsSemisimpleModule (MonoidAlgebra k K) ↥(hull σ ρ) :=
  isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (R := MonoidAlgebra k K)
    (M := ρ.asModule) (s := simples σ ρ) (p := fun m => m) fun m hm => by
      obtain ⟨T, hT, rfl, hm⟩ := hm
      haveI := IsSimpleModule.congr (LinearEquiv.ofInjective (mapA σ ρ T hT)
        (LinearMap.ker_eq_bot.mp (ker_mapA_eq_bot σ ρ T hT hm))).symm
      exact inferInstance

omit [IsAlgClosed k] [FiniteDimensional k W] in
set_option backward.isDefEq.respectTransparency false in

theorem asSubmodule_le_hull (σ : Representation k K U) (ρ : Representation k K V)
    (N : Subrepresentation ρ)
    (hle : N.toSubmodule ≤ Submodule.span k {y : V | ∃ T : U →ₗ[k] V,
      (∀ (g : K) (u : U), T (σ g u) = ρ g (T u)) ∧ y ∈ LinearMap.range T}) :
    N.asSubmodule ≤ hull σ ρ := by
  have key : ∀ y : V, y ∈ Submodule.span k {y : V | ∃ T : U →ₗ[k] V,
      (∀ (g : K) (u : U), T (σ g u) = ρ g (T u)) ∧ y ∈ LinearMap.range T} →
      ρ.asModuleEquiv.symm y ∈ hull σ ρ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨T, hT, u, rfl⟩ := hy
      by_cases hT0 : LinearMap.range (mapA σ ρ T hT) = ⊥
      · have h0 : mapA σ ρ T hT (σ.asModuleEquiv.symm u) = 0 := by
          have := LinearMap.mem_range_self (mapA σ ρ T hT) (σ.asModuleEquiv.symm u)
          rw [hT0] at this
          simpa using this
        have h0' : T u = 0 := (mapA_apply σ ρ T hT u).symm.trans (by rw [h0])
        rw [h0', map_zero]
        exact Submodule.zero_mem _
      · have hmem : LinearMap.range (mapA σ ρ T hT) ∈ simples σ ρ := ⟨T, hT, rfl, hT0⟩
        have hle₁ : LinearMap.range (mapA σ ρ T hT) ≤ hull σ ρ := by
          unfold hull
          exact le_biSup (fun m => m) hmem
        exact hle₁ (LinearMap.mem_range_self (mapA σ ρ T hT) (σ.asModuleEquiv.symm u))
    | zero => simp
    | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [Representation.asModuleEquiv_symm_map_smul]
      exact Submodule.smul_mem _ _ hy
  intro x hx
  have hx' : (ρ.asModuleEquiv x : V) ∈ N.toSubmodule := hx
  simpa using key _ (hle hx')

omit [IsAlgClosed k] [FiniteDimensional k W] in
set_option backward.isDefEq.respectTransparency false in

theorem isSemisimpleModule_asSubmodule (σ : Representation k K U) [σ.IsIrreducible]
    (ρ : Representation k K V) (N : Subrepresentation ρ) (h : N.asSubmodule ≤ hull σ ρ) :
    IsSemisimpleModule (MonoidAlgebra k K) ↥N.asSubmodule := by
  haveI := isSemisimpleModule_hull σ ρ
  exact IsSemisimpleModule.congr
    (M := ↥(Submodule.comap (hull σ ρ).subtype N.asSubmodule))
    (Submodule.comapSubtypeEquivOfLe h).symm

omit [IsAlgClosed k] [FiniteDimensional k W] in
set_option backward.isDefEq.respectTransparency false in

theorem isIsotypicOfType_asSubmodule (σ : Representation k K U) [σ.IsIrreducible]
    (ρ : Representation k K V) (N : Subrepresentation ρ) (h : N.asSubmodule ≤ hull σ ρ) :
    IsIsotypicOfType (MonoidAlgebra k K) ↥N.asSubmodule σ.asModule := by
  classical
  haveI : ∀ m : simples σ ρ, IsSimpleModule (MonoidAlgebra k K) m := by
    rintro ⟨m, T, hT, rfl, hm⟩
    exact IsSimpleModule.congr (N := σ.asModule)
      (LinearEquiv.ofInjective (mapA σ ρ T hT)
        (LinearMap.ker_eq_bot.mp (ker_mapA_eq_bot σ ρ T hT hm))).symm
  intro m hm
  haveI := hm
  haveI : IsSimpleModule (MonoidAlgebra k K) ↥(m.map N.asSubmodule.subtype) :=
    IsSimpleModule.congr (N := ↥m)
      (Submodule.equivMapOfInjective N.asSubmodule.subtype N.asSubmodule.injective_subtype m).symm
  have hm' : m.map N.asSubmodule.subtype ≤ sSup (simples σ ρ) := by
    rw [sSup_eq_iSup]
    rintro _ ⟨x, _, rfl⟩
    exact h x.2
  obtain ⟨S₀, hS₀, ⟨e'⟩⟩ := Submodule.linearEquiv_of_le_sSup (R := MonoidAlgebra k K)
    (m.map N.asSubmodule.subtype) _ hm'
  obtain ⟨T, hT, rfl, hT0⟩ := hS₀
  exact ⟨(Submodule.equivMapOfInjective N.asSubmodule.subtype N.asSubmodule.injective_subtype
    m).trans (e'.trans (LinearEquiv.ofInjective (mapA σ ρ T hT)
      (LinearMap.ker_eq_bot.mp (ker_mapA_eq_bot σ ρ T hT hT0))).symm)⟩

noncomputable def subrep (ρ : Representation k K V) (N : Submodule k V)
    (hN : ∀ (g : K) (x : V), x ∈ N → ρ g x ∈ N) : Subrepresentation ρ :=
  ⟨N, fun g _ hx => hN g _ hx⟩

noncomputable def subEquiv (ρ : Representation k K V) (N : Subrepresentation ρ) :
    ↥N.asSubmodule ≃ₗ[k] ↥N.toSubmodule where
  toFun x := ⟨ρ.asModuleEquiv x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨ρ.asModuleEquiv.symm y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsAlgClosed k] [FiniteDimensional k W] in
theorem subEquiv_of_smul (ρ : Representation k K V) (N : Subrepresentation ρ) (g : K)
    (m : ↥N.asSubmodule) :
    subEquiv ρ N (MonoidAlgebra.of k K g • m) = N.toRepresentation g (subEquiv ρ N m) := by
  apply Subtype.ext
  change ρ.asModuleEquiv ((MonoidAlgebra.of k K g • m : ↥N.asSubmodule) : ρ.asModule) =
    ρ g (ρ.asModuleEquiv (m : ρ.asModule))
  rw [Submodule.coe_smul, Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

set_option backward.isDefEq.respectTransparency false in

theorem le_span_translates_invariants (Lf Rf : Representation k K V)
    (hLR : ∀ a b : K, Lf a ∘ₗ Rf b = Rf b ∘ₗ Lf a) (N : Submodule k V)
    [FiniteDimensional k N] (hNL : ∀ (g : K) (x : V), x ∈ N → Lf g x ∈ N)
    (hNR : ∀ (g : K) (x : V), x ∈ N → Rf g x ∈ N)
    (hNτ : N ≤ Submodule.span k {y : V | ∃ T : W →ₗ[k] V,
      (∀ (g : K) (w : W), T (τ g w) = Lf g (T w)) ∧ y ∈ LinearMap.range T})
    (hNτ' : N ≤ Submodule.span k {y : V | ∃ T : Module.Dual k W →ₗ[k] V,
      (∀ (g : K) (μ : Module.Dual k W), T (τ.dual g μ) = Rf g (T μ)) ∧ y ∈ LinearMap.range T}) :
    N ≤ Submodule.span k
      {y : V | ∃ (a : K) (n₀ : V), n₀ ∈ N ∧ (∀ g : K, Lf g (Rf g n₀) = n₀) ∧ y = Lf a n₀} := by
  haveI := isIrreducible_dual τ
  haveI : FiniteDimensional k ↥(subrep Lf N hNL).toSubmodule := ‹FiniteDimensional k N›
  have hL := asSubmodule_le_hull τ Lf (subrep Lf N hNL) hNτ
  have hR := asSubmodule_le_hull τ.dual Rf (subrep Rf N hNR) hNτ'
  haveI := isSemisimpleModule_asSubmodule τ Lf (subrep Lf N hNL) hL
  haveI := isSemisimpleModule_asSubmodule τ.dual Rf (subrep Rf N hNR) hR
  have hLi := isIsotypicOfType_asSubmodule τ Lf (subrep Lf N hNL) hL
  have hRi := isIsotypicOfType_asSubmodule τ.dual Rf (subrep Rf N hNR) hR
  have hcomm : ∀ a b : K, (subrep Lf N hNL).toRepresentation a ∘ₗ
      (subrep Rf N hNR).toRepresentation b =
      (subrep Rf N hNR).toRepresentation b ∘ₗ (subrep Lf N hNL).toRepresentation a := by
    intro a b
    ext x
    exact congrArg (fun φ : V →ₗ[k] V => φ (x : V)) (hLR a b)
  have h := span_translates_invariants_eq_top' τ (subrep Lf N hNL).toRepresentation
    (subrep Rf N hNR).toRepresentation hLi (subEquiv Lf (subrep Lf N hNL))
    (subEquiv_of_smul Lf (subrep Lf N hNL)) hRi (subEquiv Rf (subrep Rf N hNR))
    (subEquiv_of_smul Rf (subrep Rf N hNR)) hcomm
  intro x hx
  have hx' := Submodule.eq_top_iff'.mp h ⟨x, hx⟩
  have := Submodule.apply_mem_span_image_of_mem_span (N.subtype) hx'
  refine Submodule.span_mono ?_ this
  rintro _ ⟨y, ⟨a, n₀, hn₀, rfl⟩, rfl⟩
  exact ⟨a, n₀, n₀.2, fun g => congrArg Subtype.val (hn₀ g), rfl⟩

end Ambient

section MultiPlace

variable [IsAlgClosed k]
variable {V : Type*} [AddCommGroup V] [Module k V]

noncomputable def typeSpan {H U : Type*} [Group H] [AddCommGroup U] [Module k U]
    (ρ' : Representation k H V) (σ : Representation k H U) : Submodule k V :=
  Submodule.span k {y : V | ∃ T : U →ₗ[k] V,
    (∀ (g : H) (u : U), T (σ g u) = ρ' g (T u)) ∧ y ∈ LinearMap.range T}

noncomputable def orbitSpan {H : Type*} [Group H] (ρ' : Representation k H V) (y : V) :
    Submodule k V :=
  Submodule.span k (Set.range fun g : H => ρ' g y)

noncomputable def orbitSpan₂ {H : Type*} [Group H] (L R : Representation k H V) (y : V) :
    Submodule k V :=
  Submodule.span k {z : V | ∃ (a b : H), z = L a (R b y)}

omit [IsAlgClosed k] in

theorem apply_mem_typeSpan {H U : Type*} [Group H] [AddCommGroup U] [Module k U]
    (ρ' : Representation k H V) (σ : Representation k H U) (g : H) {y : V}
    (hy : y ∈ typeSpan ρ' σ) : ρ' g y ∈ typeSpan ρ' σ := by
  unfold typeSpan at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨T, hT, u, rfl⟩ := hy
    exact Submodule.subset_span ⟨T, hT, σ g u, hT g u⟩
  | zero => simp
  | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
  | smul c y _ hy => simpa using Submodule.smul_mem _ c hy

omit [IsAlgClosed k] in

theorem map_mem_typeSpan {H U : Type*} [Group H] [AddCommGroup U] [Module k U]
    (ρ' : Representation k H V) (σ : Representation k H U) (φ : V →ₗ[k] V)
    (hφ : ∀ g : H, φ ∘ₗ ρ' g = ρ' g ∘ₗ φ) {y : V} (hy : y ∈ typeSpan ρ' σ) :
    φ y ∈ typeSpan ρ' σ := by
  unfold typeSpan at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨T, hT, u, rfl⟩ := hy
    refine Submodule.subset_span ⟨φ ∘ₗ T, fun g u => ?_, u, rfl⟩
    change φ (T (σ g u)) = ρ' g (φ (T u))
    rw [hT, ← LinearMap.comp_apply, hφ g]
    rfl
  | zero => simp
  | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
  | smul c y _ hy => simpa using Submodule.smul_mem _ c hy

omit [IsAlgClosed k] in

theorem finiteDimensional_orbitSpan {H U : Type*} [Group H] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] (ρ' : Representation k H V) (σ : Representation k H U) {y : V}
    (hy : y ∈ typeSpan ρ' σ) : FiniteDimensional k (orbitSpan ρ' y) := by
  suffices h : ∃ P : Submodule k V, FiniteDimensional k P ∧ ∀ g : H, ρ' g y ∈ P by
    obtain ⟨P, hP, hyP⟩ := h
    exact Submodule.finiteDimensional_of_le (Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hyP g))
  unfold typeSpan at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨T, hT, u, rfl⟩ := hy
    exact ⟨LinearMap.range T, inferInstance, fun g => ⟨σ g u, hT g u⟩⟩
  | zero => exact ⟨⊥, inferInstance, fun g => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨P, hP, hyP⟩ := hy
    obtain ⟨Q, hQ, hzQ⟩ := hz
    exact ⟨P ⊔ Q, inferInstance, fun g => by
      rw [map_add]; exact Submodule.add_mem_sup (hyP g) (hzQ g)⟩
  | smul c y _ hy =>
    obtain ⟨P, hP, hyP⟩ := hy
    exact ⟨P, hP, fun g => by rw [map_smul]; exact P.smul_mem c (hyP g)⟩

omit [IsAlgClosed k] in

theorem finiteDimensional_orbitSpan₂ {H : Type*} [Group H] (L R : Representation k H V) (y : V)
    (hR : FiniteDimensional k (orbitSpan R y))
    (hL : ∀ x ∈ orbitSpan R y, FiniteDimensional k (orbitSpan L x)) :
    FiniteDimensional k (orbitSpan₂ L R y) := by
  classical
  obtain ⟨s, hs⟩ : (orbitSpan R y).FG := by
    rw [← Submodule.map_subtype_top (orbitSpan R y)]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have hsub : ∀ x ∈ s, x ∈ orbitSpan R y := fun x hx => hs ▸ Submodule.subset_span hx
  haveI : ∀ x : s, FiniteDimensional k (orbitSpan L (x : V)) := fun x => hL x (hsub x x.2)
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.mpr ?_ :
    orbitSpan₂ L R y ≤ ⨆ x : s, orbitSpan L (x : V))
  rintro _ ⟨a, b, rfl⟩
  have hb : R b y ∈ Submodule.span k (s : Set V) := hs ▸ Submodule.subset_span ⟨b, rfl⟩
  have : ∀ z ∈ Submodule.span k (s : Set V), L a z ∈ ⨆ x : s, orbitSpan L (x : V) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      exact (le_iSup (fun x : s => orbitSpan L (x : V)) ⟨z, hz⟩)
        (Submodule.subset_span ⟨a, rfl⟩)
    | zero => simp
    | add z z' _ _ hz hz' => simpa using Submodule.add_mem _ hz hz'
    | smul c z _ hz => simpa using Submodule.smul_mem _ c hz
  exact this _ hb

variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ w, Group (H w)]
variable {Wt : ι → Type*} [∀ w, AddCommGroup (Wt w)] [∀ w, Module k (Wt w)]
  [∀ w, FiniteDimensional k (Wt w)]
  (τ : ∀ w, Representation k (H w) (Wt w)) [∀ w, (τ w).IsIrreducible]
  (Lf Rf : ∀ w, Representation k (H w) V)

theorem le_of_invariants_mem
    (hLR : ∀ (w w' : ι) (a : H w) (b : H w'), Lf w a ∘ₗ Rf w' b = Rf w' b ∘ₗ Lf w a)
    (hLL : ∀ (w w' : ι), w ≠ w' → ∀ (a : H w) (b : H w'),
      Lf w a ∘ₗ Lf w' b = Lf w' b ∘ₗ Lf w a)
    (hRR : ∀ (w w' : ι), w ≠ w' → ∀ (a : H w) (b : H w'),
      Rf w a ∘ₗ Rf w' b = Rf w' b ∘ₗ Rf w a)
    (𝓥 : Submodule k V) (h𝓥L : ∀ (w : ι) (a : H w) (x : V), x ∈ 𝓥 → Lf w a x ∈ 𝓥)
    (h𝓥R : ∀ (w : ι) (b : H w) (x : V), x ∈ 𝓥 → Rf w b x ∈ 𝓥)
    (h𝓥τ : ∀ w, 𝓥 ≤ typeSpan (Lf w) (τ w)) (h𝓥τ' : ∀ w, 𝓥 ≤ typeSpan (Rf w) (τ w).dual)
    (X : Submodule k V) (hXL : ∀ (w : ι) (a : H w) (x : V), x ∈ X → Lf w a x ∈ X)
    (hX : ∀ n ∈ 𝓥, (∀ (w : ι) (g : H w), Lf w g (Rf w g n) = n) → n ∈ X) :
    𝓥 ≤ X := by
  classical
  suffices key : ∀ (S : Finset ι), ∀ n ∈ 𝓥,
      (∀ w, w ∉ S → ∀ g : H w, Lf w g (Rf w g n) = n) → n ∈ X by
    intro n hn
    exact key Finset.univ n hn (fun w hw => absurd (Finset.mem_univ w) hw)
  intro S
  induction S using Finset.induction with
  | empty => exact fun n hn hinv => hX n hn fun w g => hinv w (by simp) g
  | insert w S hwS ih =>
    intro n hn hinv
    have hLR' : ∀ (w₁ w₂ : ι) (a : H w₁) (b : H w₂) (x : V),
        Lf w₁ a (Rf w₂ b x) = Rf w₂ b (Lf w₁ a x) :=
      fun w₁ w₂ a b x => LinearMap.congr_fun (hLR w₁ w₂ a b) x
    have hLL' : ∀ (w₁ w₂ : ι), w₁ ≠ w₂ → ∀ (a : H w₁) (b : H w₂) (x : V),
        Lf w₁ a (Lf w₂ b x) = Lf w₂ b (Lf w₁ a x) :=
      fun w₁ w₂ h a b x => LinearMap.congr_fun (hLL w₁ w₂ h a b) x
    have hRR' : ∀ (w₁ w₂ : ι), w₁ ≠ w₂ → ∀ (a : H w₁) (b : H w₂) (x : V),
        Rf w₁ a (Rf w₂ b x) = Rf w₂ b (Rf w₁ a x) :=
      fun w₁ w₂ h a b x => LinearMap.congr_fun (hRR w₁ w₂ h a b) x

    have hNle : orbitSpan₂ (Lf w) (Rf w) n ≤ 𝓥 := Submodule.span_le.mpr (by
      rintro _ ⟨a, b, rfl⟩
      exact h𝓥L w a _ (h𝓥R w b _ hn))
    have hNL : ∀ (g : H w) (x : V), x ∈ orbitSpan₂ (Lf w) (Rf w) n →
        Lf w g x ∈ orbitSpan₂ (Lf w) (Rf w) n := by
      intro g x hx
      refine (Submodule.map_span_le (Lf w g) _ (orbitSpan₂ (Lf w) (Rf w) n) |>.mpr ?_) ⟨x, hx, rfl⟩
      rintro _ ⟨a, b, rfl⟩
      exact Submodule.subset_span ⟨g * a, b, by rw [map_mul]; rfl⟩
    have hNR : ∀ (g : H w) (x : V), x ∈ orbitSpan₂ (Lf w) (Rf w) n →
        Rf w g x ∈ orbitSpan₂ (Lf w) (Rf w) n := by
      intro g x hx
      refine (Submodule.map_span_le (Rf w g) _ (orbitSpan₂ (Lf w) (Rf w) n) |>.mpr ?_) ⟨x, hx, rfl⟩
      rintro _ ⟨a, b, rfl⟩
      exact Submodule.subset_span ⟨a, g * b, by rw [map_mul, ← hLR']; rfl⟩
    haveI : FiniteDimensional k (orbitSpan₂ (Lf w) (Rf w) n) := by
      refine finiteDimensional_orbitSpan₂ (Lf w) (Rf w) n
        (finiteDimensional_orbitSpan (Rf w) (τ w).dual (h𝓥τ' w hn)) fun x hx => ?_
      refine finiteDimensional_orbitSpan (Lf w) (τ w) (h𝓥τ w ?_)
      refine (Submodule.span_le.mpr ?_ : orbitSpan (Rf w) n ≤ 𝓥) hx
      rintro _ ⟨b, rfl⟩
      exact h𝓥R w b _ hn
    have hgen := le_span_translates_invariants (τ w) (Lf w) (Rf w) (hLR w w)
      (orbitSpan₂ (Lf w) (Rf w) n) hNL hNR (hNle.trans (h𝓥τ w)) (hNle.trans (h𝓥τ' w))
    have hn' : n ∈ orbitSpan₂ (Lf w) (Rf w) n :=
      Submodule.subset_span ⟨1, 1, by rw [map_one, map_one]; rfl⟩
    refine (Submodule.span_le.mpr ?_ : _ ≤ X) (hgen hn')
    rintro _ ⟨a, n₀, hn₀, hinv₀, rfl⟩
    refine hXL w a _ (ih n₀ (hNle hn₀) fun w' hw' g => ?_)
    by_cases hww : w' = w
    · subst hww
      exact hinv₀ g
    ·
      have hw'S : w' ∉ insert w S := by simp [hww, hw']
      have : ∀ z ∈ orbitSpan₂ (Lf w) (Rf w) n, Lf w' g (Rf w' g z) = z := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨a', b', rfl⟩ := hz
          rw [← hLR' w w' a' g, hRR' w' w hww g b', hLL' w' w hww g a', hLR' w' w g b',
            hinv w' hw'S g]
        | zero => simp
        | add z z' _ _ hz hz' => rw [map_add, map_add, hz, hz']
        | smul c z _ hz => rw [map_smul, map_smul, hz]
      exact this n₀ hn₀

attribute [irreducible] typeSpan orbitSpan orbitSpan₂

end MultiPlace

section Pairing

variable [IsAlgClosed k]
variable {V : Type*} [AddCommGroup V] [Module k V]

def identitySubmodule (C : Submodule k V) (K : V → V → V) (fa : V)
    (hKaddL : ∀ ψ₁ ψ₂, ψ₁ ∈ C → ψ₂ ∈ C → K (ψ₁ + ψ₂) fa = K ψ₁ fa + K ψ₂ fa)
    (hKsmulL : ∀ (c : k) (ψ : V), ψ ∈ C → K (c • ψ) fa = c • K ψ fa)
    (hKaddR : ∀ ψ₁ ψ₂, ψ₁ ∈ C → ψ₂ ∈ C → K fa (ψ₁ + ψ₂) = K fa ψ₁ + K fa ψ₂)
    (hKsmulR : ∀ (c : k) (ψ : V), ψ ∈ C → K fa (c • ψ) = c • K fa ψ) : Submodule k V where
  carrier := {ψ | ψ ∈ C ∧ K fa ψ = K ψ fa}
  add_mem' := by
    rintro ψ₁ ψ₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    exact ⟨C.add_mem h₁ h₂, by rw [hKaddR _ _ h₁ h₂, hKaddL _ _ h₁ h₂, h₁', h₂']⟩
  zero_mem' := ⟨C.zero_mem, by
    have h1 := hKsmulR 0 0 C.zero_mem
    have h2 := hKsmulL 0 0 C.zero_mem
    rw [zero_smul] at h1 h2
    rw [h1, h2, zero_smul, zero_smul]⟩
  smul_mem' := by
    rintro c ψ ⟨h, h'⟩
    exact ⟨C.smul_mem c h, by rw [hKsmulR c _ h, hKsmulL c _ h, h']⟩

variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ w, Group (H w)]
variable {Wt : ι → Type*} [∀ w, AddCommGroup (Wt w)] [∀ w, Module k (Wt w)]
  [∀ w, FiniteDimensional k (Wt w)]
  (τ : ∀ w, Representation k (H w) (Wt w)) [∀ w, (τ w).IsIrreducible]
  (Lf Rf : ∀ w, Representation k (H w) V)

noncomputable def typesSubmodule (C : Submodule k V) : Submodule k V :=
  C ⊓ ⨅ w, (typeSpan (Lf w) (τ w) ⊓ typeSpan (Rf w) (τ w).dual)

omit [IsAlgClosed k] [Fintype ι] [∀ w, FiniteDimensional k (Wt w)] [∀ w, (τ w).IsIrreducible] in
theorem mem_typesSubmodule_iff (C : Submodule k V) (ψ : V) :
    ψ ∈ typesSubmodule τ Lf Rf C ↔
      ψ ∈ C ∧ ∀ w, ψ ∈ typeSpan (Lf w) (τ w) ∧ ψ ∈ typeSpan (Rf w) (τ w).dual := by
  unfold typesSubmodule
  simp only [Submodule.mem_inf, Submodule.mem_iInf]

omit [IsAlgClosed k] [Fintype ι] [∀ w, FiniteDimensional k (Wt w)] [∀ w, (τ w).IsIrreducible] in
theorem apply_mem_typesSubmodule_left
    (hLR : ∀ (w w' : ι) (a : H w) (b : H w'), Lf w a ∘ₗ Rf w' b = Rf w' b ∘ₗ Lf w a)
    (hLL : ∀ (w w' : ι), w ≠ w' → ∀ (a : H w) (b : H w'),
      Lf w a ∘ₗ Lf w' b = Lf w' b ∘ₗ Lf w a)
    (C : Submodule k V) (hCL : ∀ (w : ι) (a : H w) (ψ : V), ψ ∈ C → Lf w a ψ ∈ C)
    (w : ι) (a : H w) (ψ : V) (hψ : ψ ∈ typesSubmodule τ Lf Rf C) :
    Lf w a ψ ∈ typesSubmodule τ Lf Rf C := by
  classical
  rw [mem_typesSubmodule_iff] at hψ ⊢
  refine ⟨hCL w a ψ hψ.1, fun w' => ⟨?_, ?_⟩⟩
  · by_cases hww : w = w'
    · subst hww
      exact apply_mem_typeSpan (Lf w) (τ w) a (hψ.2 w).1
    · exact map_mem_typeSpan (Lf w') (τ w') (Lf w a) (fun g => hLL w w' hww a g) (hψ.2 w').1
  · exact map_mem_typeSpan (Rf w') (τ w').dual (Lf w a) (fun g => hLR w w' a g) (hψ.2 w').2

omit [IsAlgClosed k] [Fintype ι] [∀ w, FiniteDimensional k (Wt w)] [∀ w, (τ w).IsIrreducible] in
theorem apply_mem_typesSubmodule_right
    (hLR : ∀ (w w' : ι) (a : H w) (b : H w'), Lf w a ∘ₗ Rf w' b = Rf w' b ∘ₗ Lf w a)
    (hRR : ∀ (w w' : ι), w ≠ w' → ∀ (a : H w) (b : H w'),
      Rf w a ∘ₗ Rf w' b = Rf w' b ∘ₗ Rf w a)
    (C : Submodule k V) (hCR : ∀ (w : ι) (b : H w) (ψ : V), ψ ∈ C → Rf w b ψ ∈ C)
    (w : ι) (b : H w) (ψ : V) (hψ : ψ ∈ typesSubmodule τ Lf Rf C) :
    Rf w b ψ ∈ typesSubmodule τ Lf Rf C := by
  classical
  rw [mem_typesSubmodule_iff] at hψ ⊢
  refine ⟨hCR w b ψ hψ.1, fun w' => ⟨?_, ?_⟩⟩
  · exact map_mem_typeSpan (Lf w') (τ w') (Rf w b) (fun g => (hLR w' w g b).symm) (hψ.2 w').1
  · by_cases hww : w = w'
    · subst hww
      exact apply_mem_typeSpan (Rf w) (τ w).dual b (hψ.2 w).2
    · exact map_mem_typeSpan (Rf w') (τ w').dual (Rf w b) (fun g => hRR w w' hww b g) (hψ.2 w').2

theorem pairing_symm_of_mem_typeSpan
    (hLR : ∀ (w w' : ι) (a : H w) (b : H w'), Lf w a ∘ₗ Rf w' b = Rf w' b ∘ₗ Lf w a)
    (hLL : ∀ (w w' : ι), w ≠ w' → ∀ (a : H w) (b : H w'),
      Lf w a ∘ₗ Lf w' b = Lf w' b ∘ₗ Lf w a)
    (hRR : ∀ (w w' : ι), w ≠ w' → ∀ (a : H w) (b : H w'),
      Rf w a ∘ₗ Rf w' b = Rf w' b ∘ₗ Rf w a)
    (C : Submodule k V) (hCL : ∀ (w : ι) (a : H w) (ψ : V), ψ ∈ C → Lf w a ψ ∈ C)
    (hCR : ∀ (w : ι) (b : H w) (ψ : V), ψ ∈ C → Rf w b ψ ∈ C)
    (K : V → V → V) (fa : V)
    (hKaddL : ∀ ψ₁ ψ₂, ψ₁ ∈ C → ψ₂ ∈ C → K (ψ₁ + ψ₂) fa = K ψ₁ fa + K ψ₂ fa)
    (hKsmulL : ∀ (c : k) (ψ : V), ψ ∈ C → K (c • ψ) fa = c • K ψ fa)
    (hKaddR : ∀ ψ₁ ψ₂, ψ₁ ∈ C → ψ₂ ∈ C → K fa (ψ₁ + ψ₂) = K fa ψ₁ + K fa ψ₂)
    (hKsmulR : ∀ (c : k) (ψ : V), ψ ∈ C → K fa (c • ψ) = c • K fa ψ)
    (hKL : ∀ (w : ι) (a : H w) (ψ : V), ψ ∈ C → K (Lf w a ψ) fa = Lf w a (K ψ fa))
    (hKR : ∀ (w : ι) (a : H w) (ψ : V), ψ ∈ C → K fa (Lf w a ψ) = Lf w a (K fa ψ))
    (hB : ∀ ψ₀ : V, ψ₀ ∈ C → (∀ (w : ι) (h : H w), Lf w h (Rf w h ψ₀) = ψ₀) → K fa ψ₀ = K ψ₀ fa)
    (ψ : V) (hψ : ψ ∈ C) (hψL : ∀ w, ψ ∈ typeSpan (Lf w) (τ w))
    (hψR : ∀ w, ψ ∈ typeSpan (Rf w) (τ w).dual) :
    K fa ψ = K ψ fa := by
  have key := le_of_invariants_mem τ Lf Rf hLR hLL hRR (typesSubmodule τ Lf Rf C)
    (apply_mem_typesSubmodule_left τ Lf Rf hLR hLL C hCL)
    (apply_mem_typesSubmodule_right τ Lf Rf hLR hRR C hCR)
    (fun w x hx => ((mem_typesSubmodule_iff τ Lf Rf C x).mp hx |>.2 w).1)
    (fun w x hx => ((mem_typesSubmodule_iff τ Lf Rf C x).mp hx |>.2 w).2)
    (identitySubmodule C K fa hKaddL hKsmulL hKaddR hKsmulR)
    (fun w a x hx => ⟨hCL w a x hx.1, by rw [hKR w a x hx.1, hKL w a x hx.1, hx.2]⟩)
    (fun n hn hinv => ⟨((mem_typesSubmodule_iff τ Lf Rf C n).mp hn).1,
      hB n ((mem_typesSubmodule_iff τ Lf Rf C n).mp hn).1 hinv⟩)
  have hψ𝓥 : ψ ∈ typesSubmodule τ Lf Rf C :=
    (mem_typesSubmodule_iff τ Lf Rf C ψ).mpr ⟨hψ, fun w => ⟨hψL w, hψR w⟩⟩
  exact (key hψ𝓥).2

end Pairing

section Translation

variable {A : Type*} [Group A]

def leftRep {H : Type*} [Group H] (e : H →* A) : Representation k H (A → k) where
  toFun h :=
    { toFun := fun ψ y => ψ ((e h)⁻¹ * y)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext ψ y; simp
  map_mul' a b := by ext ψ y; simp [mul_assoc]

def rightRep {H : Type*} [Group H] (e : H →* A) : Representation k H (A → k) where
  toFun h :=
    { toFun := fun ψ y => ψ (y * e h)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext ψ y; simp
  map_mul' a b := by ext ψ y; simp [mul_assoc]

@[scoped simp] theorem leftRep_apply {H : Type*} [Group H] (e : H →* A) (h : H) (ψ : A → k) (y : A) :
    leftRep (k := k) e h ψ y = ψ ((e h)⁻¹ * y) := rfl

@[scoped simp] theorem rightRep_apply {H : Type*} [Group H] (e : H →* A) (h : H) (ψ : A → k) (y : A) :
    rightRep (k := k) e h ψ y = ψ (y * e h) := rfl

def invMap : (A → k) →ₗ[k] (A → k) where
  toFun ψ y := ψ y⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem invMap_apply (ψ : A → k) (y : A) : invMap (k := k) ψ y = ψ y⁻¹ := rfl

attribute [irreducible] leftRep rightRep invMap

theorem leftRep_comp_rightRep {H H' : Type*} [Group H] [Group H'] (e : H →* A) (e' : H' →* A)
    (a : H) (b : H') :
    leftRep (k := k) e a ∘ₗ rightRep e' b = rightRep e' b ∘ₗ leftRep e a := by
  apply LinearMap.ext
  intro φ'
  funext y
  simp only [LinearMap.comp_apply, leftRep_apply, rightRep_apply, mul_assoc]

theorem leftRep_comp_leftRep {H H' : Type*} [Group H] [Group H'] (e : H →* A) (e' : H' →* A)
    (a : H) (b : H') (h : Commute (e a) (e' b)) :
    leftRep (k := k) e a ∘ₗ leftRep e' b = leftRep e' b ∘ₗ leftRep e a := by
  apply LinearMap.ext
  intro φ'
  funext y
  simp only [LinearMap.comp_apply, leftRep_apply, ← mul_assoc]
  rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, h.eq]

theorem rightRep_comp_rightRep {H H' : Type*} [Group H] [Group H'] (e : H →* A) (e' : H' →* A)
    (a : H) (b : H') (h : Commute (e a) (e' b)) :
    rightRep (k := k) e a ∘ₗ rightRep e' b = rightRep e' b ∘ₗ rightRep e a := by
  apply LinearMap.ext
  intro φ'
  funext y
  simp only [LinearMap.comp_apply, rightRep_apply, mul_assoc]
  rw [h.eq]

theorem conj_invariant_of_invariant {H : Type*} [Group H] (e : H →* A) (ψ : A → k)
    (hψ : ∀ h : H, leftRep (k := k) e h (rightRep e h ψ) = ψ) (h : H) (y : A) :
    ψ (e h * y * (e h)⁻¹) = ψ y := by
  have := congrFun (hψ h) (e h * y * (e h)⁻¹)
  simp only [leftRep_apply, rightRep_apply] at this
  rw [← this]
  congr 1
  group

theorem mem_typeSpan_leftRep_of_inv_mem {H U : Type*} [Group H] [AddCommGroup U] [Module k U]
    (e : H →* A) (σ : Representation k H U) {ψ : A → k}
    (hψ : (fun a => ψ a⁻¹) ∈ typeSpan (rightRep e) σ) : ψ ∈ typeSpan (leftRep e) σ := by
  suffices key : ∀ F ∈ typeSpan (rightRep (k := k) e) σ,
      (fun a => F a⁻¹) ∈ typeSpan (leftRep e) σ by
    have h := key _ hψ
    simp only [inv_inv] at h
    exact h
  intro F hF
  unfold typeSpan at hF ⊢
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨T, hT, u, rfl⟩ := hF
    refine Submodule.subset_span ⟨invMap ∘ₗ T, fun g v => ?_, u, ?_⟩
    · funext y
      rw [LinearMap.comp_apply, invMap_apply, hT, rightRep_apply, leftRep_apply,
        LinearMap.comp_apply, invMap_apply, _root_.mul_inv_rev, inv_inv]
    · rw [LinearMap.comp_apply]
      funext y
      rw [invMap_apply]
  | zero => exact Submodule.zero_mem _
  | add F G _ _ hF hG => exact Submodule.add_mem _ hF hG
  | smul c F _ hF => exact Submodule.smul_mem _ c hF

end Translation

end BiIsotypic

end
