/-
  The generator type of the `CohCarrier` Hecke algebra and its operators on
  `H1 M H 𝒪`: the `T` (prime to the level), `U` (prime dividing the level) and
  `dia` (diamond, a unit of `ZMod M`) generators, the `T_ℓ` operator `heckeTL`
  built from the transfer along `Γ_HUpper(M,ℓ) → Γ_H(M)` (with
  `heckeTL_apply` identifying it with `heckeT`), the diamond operator `diamondL`
  obtained by choosing a lift in `Γ₀(M)`, the independence of that choice
  (`diamondL_eq_diamondRaw`), and the evaluation `opFamily` of a generator.

  FLT provenance, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Inst.lean`
  * `:13–16` — `Gen`.
  * `:23–34` — `heckeTL`; `:36–37` — `heckeTL_apply`.
  * `:55–58` — `diamondL`; `:60–89` — `diamondL_eq_diamondRaw`.
  * `:91–94` — `opFamily`.

  Deliberately not transcribed, and why:
  * `gamma0Units_surjective` (`:39–53`) — already ported in
    `ModularForms/Defs/GammaH.lean` (this module reaches it through
    `Defs/CohCarrierLevel.lean` and does use it, in `diamondL` and
    `diamondL_eq_diamondRaw`, but does not restate it).
  * `hdata` (`:96–103`) and `MLAt` (`:105–109`) — both are stated over
    `CohCarrier.HeckeData`, the pin's `Definitions/Def_CohCarrier_HeckeData.lean`,
    which is not in the port; deferred until that module is ported.
  * the pin's trailing `example` (`:111–112`) — an `inferInstance` probe on
    `MLAt`, i.e. on a deferral, so there is nothing to restate yet.

  Statements are transcribed verbatim (same names, binders and spelling); the
  proofs are the pin's, adapted only where mathlib `v4.34.0` moved an API.
  The pin imports `Definitions.Def_CohCarrier_HeckeData` as well; the port's
  single import covers everything the transcribed declarations use.

  spec-pin: Definitions/Def_CohCarrier_Inst.lean
-/
import FLTForHuman.ModularForms.Defs.CohCarrierLevel

set_option autoImplicit false

noncomputable section

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups

/-- The generators of the cohomological Hecke algebra at level `Γ_H(M)`: a prime
`ℓ` away from `S` and not dividing `M`, a prime `q` dividing `M`, and a diamond
generator `dia d` for a unit `d` of `ZMod M`. -/
inductive Gen (M : ℕ) (S : Set ℕ) : Type
  | T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M)
  | U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M)
  | dia (d : (ZMod M)ˣ)

section Inst

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]

/-- The `T_ℓ` operator on `H1 M H 𝒪`, `𝒪`-linearly: the transfer along the
upper-triangular inclusion `Γ_HUpper(M,ℓ) → Γ_H(M)` of the pullback along the
conjugation by `diag(ℓ,1)`. -/
def heckeTL (ℓ : ℕ) [NeZero ℓ] : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M H ℓ)))
  map_add' φ ψ := by
    have : (φ + ψ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) + ψ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : (r • φ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        r • φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

theorem heckeTL_apply (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H 𝒪) :
    heckeTL M H 𝒪 ℓ φ = heckeT M H ℓ 𝒪 φ := rfl

/-- The diamond operator at the unit `d`, `𝒪`-linearly: the raw diamond action
of any lift of `d` in `Γ₀(M)`. -/
def diamondL [NeZero M] (d : (ZMod M)ˣ) : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := diamondRaw M H 𝒪 (Classical.choose (gamma0Units_surjective M d)) φ
  map_add' φ ψ := map_add _ φ ψ
  map_smul' r φ := by ext; rfl

/-- The diamond operator does not depend on the chosen lift `σ` of `d`: two
lifts differ by an element `κ` of `Γ_H(M)`, and the `κ`-terms cancel because the
target `𝒪` is additive-commutative. -/
theorem diamondL_eq_diamondRaw [NeZero M] (d : (ZMod M)ˣ) (σ : Gamma0 M)
    (hσ : gamma0Units M σ = d) (φ : H1 M H 𝒪) :
    diamondL M H 𝒪 d φ = diamondRaw M H 𝒪 σ φ := by
  have hσ₀ : gamma0Units M (Classical.choose (gamma0Units_surjective M d)) = d :=
    Classical.choose_spec (gamma0Units_surjective M d)
  set σ₀ := Classical.choose (gamma0Units_surjective M d)

  have hκu : gamma0Units M (σ₀ * σ⁻¹) = 1 := by
    rw [map_mul, map_inv, hσ₀, hσ, mul_inv_cancel]
  have hκH : ((σ₀ * σ⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ GammaH M H := by
    rw [mem_GammaH_iff]
    exact ⟨(σ₀ * σ⁻¹).2, hκu ▸ one_mem H⟩
  set κ : ↥(GammaH M H) := ⟨((σ₀ * σ⁻¹ : Gamma0 M) : SL(2, ℤ)), hκH⟩ with hκdef

  have hconj : ∀ γ : ↥(GammaH M H),
      conjHom M H σ₀ γ = κ * conjHom M H σ γ * κ⁻¹ := by
    intro γ
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, hκdef, Subgroup.coe_mul,
      InvMemClass.coe_inv, Subgroup.coe_mul]
    group

  ext γ
  show φ (Additive.ofMul (conjHom M H σ₀ (Additive.toMul γ))) = φ (Additive.ofMul (conjHom M H σ (Additive.toMul γ)))
  rw [hconj (Additive.toMul γ)]
  have hsplit : Additive.ofMul (κ * conjHom M H σ (Additive.toMul γ) * κ⁻¹) =
      Additive.ofMul κ + Additive.ofMul (conjHom M H σ (Additive.toMul γ)) + (-(Additive.ofMul κ)) := by
    rw [ofMul_mul, ofMul_mul, ofMul_inv]
  rw [hsplit, map_add, map_add, map_neg]
  abel

/-- The Hecke operator attached to a generator: `T_ℓ` and `U_q` are both the
transfer operator `heckeTL`, and `dia d` is the diamond operator `diamondL`. -/
def opFamily [NeZero M] : Gen M S → Module.End 𝒪 (H1 M H 𝒪)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M H 𝒪 ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeTL M H 𝒪 q
  | .dia d => diamondL M H 𝒪 d

end Inst

end CohCarrier

end
