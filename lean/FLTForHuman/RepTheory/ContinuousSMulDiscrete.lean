/-
  `SMul` by a topological group on a *discrete* type.

  A group action `G` on `M` is *discrete* when every stabilizer is open, equivalently
  (for discrete `M`) when the action map is continuous. This is the class that makes
  smooth vectors automatic: a locally constant function with compact support is a
  smooth vector (§ `Def_RepTheory_SmoothVectors`).

  Transcribed verbatim from
  `Definitions/Def_Deformations_ContinuousSMulDiscrete.lean` (pinned `aa2d8b3`). The
  pin's `import Mathlib` is replaced by the specific modules the file uses; the pin's
  declarations are top-level (no namespace) and stay so.
-/
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order

set_option autoImplicit false

section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }

lemma continuousSMulDiscrete_iff [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMulDiscrete G M ↔ ContinuousSMul G M := by
  refine ⟨fun H ↦ ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  · convert_to IsOpen (⋃ x, { g : G | g • x = y } ×ˢ {x})
    · ext; simp
    · exact isOpen_iUnion fun _ ↦
        .prod (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _) (isOpen_discrete _)
  · exact ((isOpen_discrete {y}).preimage continuous_smul).preimage (Continuous.prodMk_left x)

instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]

lemma ContinuousSMulDiscrete.of_continuousSMul [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul G M] : ContinuousSMulDiscrete G M := by
  rwa [continuousSMulDiscrete_iff]

lemma continuousSMulDiscrete_iff_isOpen_stabilizer {G M : Type*} [TopologicalSpace G]
    [Group G] [ContinuousMul G] [MulAction G M] :
    ContinuousSMulDiscrete G M ↔ ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun H x ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ _ _, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain h | ⟨g, rfl⟩ := Set.eq_empty_or_nonempty {g : G | g • x = y}
  · exact h ▸ isOpen_empty
  · convert (H x).preimage (Homeomorph.mulLeft g⁻¹).continuous using 1
    ext g'
    simp [mul_smul, inv_smul_eq_iff]

lemma ContinuousSMulDiscrete.isOpen_stabilizer (G : Type*) {M : Type*} [TopologicalSpace G]
    [Group G] [MulAction G M] [ContinuousSMulDiscrete G M] (x : M) :
      IsOpen (MulAction.stabilizer G x : Set G) := ContinuousSMulDiscrete.isOpen_smul_eq _ _ _

end
