/-
  SET-AF20B consumer: the two closedness rows of `Adelic/RationalUnipotentClosed.lean`
  composed with a membership, in one chain.

  The module proves, for a number field `K`, that `Z(𝔸_K) · Kˣ · U(𝔸_K)`
  (`rationalCentreUnipotent`) and `Z(𝔸_K) · T(K) · U(𝔸_K)` (`rationalTorusUnipotent`) are closed
  in `GL₂(𝔸_K)`, each by identifying the subgroup with an entry-defined set
  (`coe_rationalCentreUnipotent_eq`, `coe_rationalTorusUnipotent_eq`) and closing that set.

  **This zone.** One chain. The ambient `rationalTorusUnipotent K` is closed, and since the
  centre-unipotent subgroup sits inside it, the closure of the centre-unipotent subgroup is
  contained in it as well — so it is a closed ambient set for both rows. Then a concrete element
  `g = globalPoints (scalar a) * unipotentGL2 x` of the rational centre-unipotent subgroup is read
  through the whole chain: `g` is in `rationalCentreUnipotent K` by `Subgroup.mem_sup`, hence in
  the entry set `scalarUnipotentSet K` by the centre-unipotent identification; the entry
  conditions of `scalarUnipotentSet` (`1 0`-entry zero, rational diagonal entry, equal diagonal
  entries) imply those of `torusUnipotentSet` (`1 0`-entry zero, both diagonal entries rational),
  and the torus identification turns that last membership back into `g ∈ rationalTorusUnipotent K`
  — i.e. membership in the closed set of the first conjunct.
-/
import FLTForHuman.AutomorphicForm.Adelic.RationalUnipotentClosed

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace AutomorphicForm
namespace SetAF20B

/-- **The zone.** The torus-unipotent subgroup is closed and, being an ambient set for the
centre-unipotent subgroup, contains the closure of the latter; and every element
`globalPoints (scalar a) * unipotentGL2 x` of the centre-unipotent subgroup is read through the
entry sets of both rows into membership in the closed torus-unipotent subgroup. -/
theorem consumer_zone_centre_le_torus_closed (K : Type) [Field K] [NumberField K] :
    IsClosed (rationalTorusUnipotent K : Set (AdelicGL2 (𝓞 K) K)) ∧
      closure (rationalCentreUnipotent K : Set (AdelicGL2 (𝓞 K) K)) ⊆
        (rationalTorusUnipotent K : Set (AdelicGL2 (𝓞 K) K)) ∧
      ∀ (a : Kˣ) (x : AdeleRing (𝓞 K) K),
        (globalPoints (𝓞 K) K
              (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
            * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ scalarUnipotentSet K ∧
          (globalPoints (𝓞 K) K
                (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
              * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ torusUnipotentSet K ∧
            (globalPoints (𝓞 K) K
                  (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
                * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ rationalCentreUnipotent K ∧
              (globalPoints (𝓞 K) K
                    (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
                  * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ rationalTorusUnipotent K := by
  have hclosed := isClosed_rationalTorusUnipotent K
  -- the centre-unipotent subgroup sits inside the torus-unipotent one
  have hsub : (rationalCentreUnipotent K : Set (AdelicGL2 (𝓞 K) K)) ⊆
      (rationalTorusUnipotent K : Set (AdelicGL2 (𝓞 K) K)) := by
    rw [rationalCentreUnipotent, rationalTorusUnipotent, rationalTorus]
    exact sup_le_sup (le_sup_left : rationalCentre K ≤ rationalCentre K ⊔ rationalDiagOne K)
      (le_refl (adelicUnipotent K))
  refine ⟨hclosed, hclosed.closure_subset_iff.mpr hsub, ?_⟩
  intro a x
  -- the element is in the subgroup by `mem_sup`
  have hZ : (globalPoints (𝓞 K) K
        (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
      * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ rationalCentreUnipotent K :=
    Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨Multiplicative.ofAdd x, rfl⟩
  -- row centre-unipotent: the subgroup is its entry set
  have hscalar : (globalPoints (𝓞 K) K
        (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
      * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ scalarUnipotentSet K := by
    rw [← coe_rationalCentreUnipotent_eq]
    exact hZ
  -- the centre-unipotent entry conditions imply the torus-unipotent ones
  have h10 := hscalar.1
  have hdiag := hscalar.2.1
  have hrat := hscalar.2.2
  have htorus : (globalPoints (𝓞 K) K
        (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
      * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ torusUnipotentSet K :=
    ⟨h10, hrat, hdiag ▸ hrat⟩
  exact ⟨hscalar, htorus, hZ, by
    show (globalPoints (𝓞 K) K
          (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
        * unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈
        (rationalTorusUnipotent K : Set (AdelicGL2 (𝓞 K) K))
    rw [coe_rationalTorusUnipotent_eq]
    exact htorus⟩

end SetAF20B
end AutomorphicForm
