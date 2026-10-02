/-
  Consumer / wire test for the **Deligne–Serre weight-one unconditional port**
  (the 54-node slice, sets S1–S8).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of every half of the slice: each zone states a small
  `example` whose proof term genuinely *applies* the ported headlines, under
  their hypotheses, and concludes something. It is a deliverable measure — the
  error count is the metric — not a proof obligation, and it deliberately lives
  outside every library (`spec/` is not globbed by the lakefile), so it can never
  break the verified port's green build. Run it by hand:

      cd lean
      flock /tmp/flt_for_human.lock timeout 180 lake env lean \
        -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean

  There are no `#check`s and no `sorry`s: every zone is an elaborated proof term,
  so deleting any one of the imported modules makes the corresponding zone fail
  with an `unknown constant` / `unknown identifier` error. Where an unconditional
  instantiation would need mathematics that is deliberately *not* ported (the
  ray-class analysis behind S8's `hfam`, the Hecke-congruence congruence data of
  S3/S4), the zone is stated in **hypothesis form** and the reason is recorded in
  its comment; no zone is silently dropped.

  HOW TO READ IT
  --------------
  One `/-! ## Zone ... -/` per set of the slice, S1 through S8, in port order.
-/

-- S1 — the weight-one Eisenstein construction.
import FLTForHuman.ModularForms.Eisenstein.WeightOneMultiplier
import FLTForHuman.ModularForms.Eisenstein.WeierstrassZetaQuasiPeriod
-- S2 — the Γ₁ Hecke vanishing chain and the nebentypus/oddness derivation.
import FLTForHuman.ModularForms.Gamma1Vanishing
import FLTForHuman.ModularForms.HeckeEigenNebentypus
-- S3 — the relèvement and the weight-one → weight-two lifting.
import FLTForHuman.DeligneSerre.Relevement
import FLTForHuman.DeligneSerre.Lifting
-- S4/S5 — the coefficient ring and the semisimple descent.
import FLTForHuman.DeligneSerre.CoefficientRing
import FLTForHuman.GaloisRep.SemisimpleDescent
-- S6 — representation conjugacy and its Frobenius form.
import FLTForHuman.GaloisRep.RepConj
import FLTForHuman.GaloisRep.ConjFromFrobenius
-- S7 — the Frobenius-density statement and the degree-one-primes tail.
import FLTForHuman.NumberTheory.FrobeniusDensity.Statement
import FLTForHuman.NumberTheory.FrobeniusDensity.DegreeOnePrimesInfinite
-- S8 — the complex-trace assembly (the capstone).
import FLTForHuman.DeligneSerre.Assembly
-- S9 — the promoted rank-two charpoly conversion the weight-one → weight-two
-- → Frobenius-charpoly route consumes (studies/frobenius-charpoly-scout.md §4).
import FLTForHuman.Algebra.CharpolyOfQuadratic

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane ModularFormClass
open Polynomial
open scoped MatrixGroups ModularForm

/-- The pin's `Γℚ` (`ConjFromFrobenius.lean`, `Assembly.lean`), restated here
because those are file-local notations. -/
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/-- The port's `Γ₁(N)` carrier, matching the headlines' own spelling. -/
local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-- The port's `Γ₀(N)` carrier. -/
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

namespace DeligneSerreConsumer

/-! ## Zone S1 — the weight-one Eisenstein construction

`WeightOneMultiplier.lean` constructs, for a primitive odd Dirichlet character
`χ` of level `L`, a weight-one Eisenstein form on `Γ₁(L)` and reads off its
constant `q`-coefficient. `WeierstrassZetaQuasiPeriod.lean` provides the
quasi-period law of the underlying `EisensteinSeries.weierstrassZeta`
construction. The zone consumes both. -/

/-- The headline: extracting the constant-coefficient law from the existential
forces the whole five-module Eisenstein construction (`E1MF`, the `hasSum`
chain, the `q`-expansion). -/
example (L : ℕ) [NeZero L] (χ : DirichletCharacter ℂ L) (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    ∃ E : ModularForm (Γ₁(L)) 1,
      ModularFormClass.qCoeff E 0 =
        -(∑ a ∈ Finset.range L, (a : ℂ) * χ (a : ZMod L)) / (2 * L) := by
  obtain ⟨E, -, h0, -⟩ :=
    ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd L χ hχ hodd
  exact ⟨E, h0⟩

/-- An `EisensteinSeries` construction target: the first conjunct of the
quasi-period package, i.e. the `+1`-period of `weierstrassZeta`. -/
example (τ : UpperHalfPlane) :
    ∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * (τ : ℂ) + v 1) →
      EisensteinSeries.weierstrassZeta τ (z + 1) =
        EisensteinSeries.weierstrassZeta τ z + EisensteinSeries.G2 τ :=
  (EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul τ).1

/-! ## Zone S2 — the Hecke vanishing chain

Two halves of the S2 story are composed here: the Γ₁ vanishing theorem
(`Gamma1Vanishing.lean`) and the oddness derivation
(`HeckeEigenNebentypus.lean`). Both are stated in hypothesis form: the concrete
instances would require an eigenform with the Hecke-eigenvalue data, which is
exactly what S3/S4 construct. -/

/-- A `Γ₁(M)`-cusp form whose `T_p`-translate is `Γ₁(M)`-invariant is zero. -/
example {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : ¬ p ∣ M) (k : ℤ)
    (y : CuspForm (Γ₁(M)) k)
    (hy : ∀ γ ∈ Γ₁(M),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    y = 0 :=
  CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 hp hpM k y hy

/-- The oddness derivation: the Hecke-eigenvalue `q`-coefficient relation forces
the nebentypus slash law. Hypothesis form (`heig` is the residual Hecke data). -/
example {M : ℕ} [NeZero M] (k : ℤ) (g : CuspForm (Γ₁(M)) k) (χ : DirichletCharacter ℂ M)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ) :=
  CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen k g χ heig γ hγ

/-! ## Zone S3 — relèvement and lifting

The weight-generic relèvement (`Relevement.lean`) and the weight-one → weight-two
lifting (`Lifting.lean`). Both are stated in hypothesis form: the `hT` binder is
the Hecke-congruence congruence datum, and the weight-two form additionally needs
the weight-one eigenform it lifts. -/

/-- The weight-generic relèvement, consumed by extracting the nonzero lifted
eigenform. -/
example (N : ℕ) [NeZero N] (w : ℕ) (ε : DirichletCharacter ℂ N)
    (h : CuspForm (Γ₁(N)) w) (hεh : CuspForm.HasNebentypus ε h)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff h n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ)
    (hne : ∃ n : ℕ, φ ⟨ModularFormClass.qCoeff h n, hR n⟩ ≠ 0)
    (α : ℕ → R)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : κ) ≠ 0 → ∀ n : ℕ, ∃ r : R,
        (r : ℂ) = ModularFormClass.qCoeff h (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (w - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) ∧
        φ r = φ (α p) * φ ⟨ModularFormClass.qCoeff h n, hR n⟩) :
    ∃ (g : CuspForm (Γ₁(N)) w) (_b : ℕ → ℂ), g ≠ 0 := by
  obtain ⟨g, b, hg0, -⟩ :=
    DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr
      N w ε h hεh R hR hε κ φ hne α hT
  exact ⟨g, b, hg0⟩

/-- The weight-one → weight-two lifting, consumed by extracting the level
description `p ∣ M ↔ p ∣ N ∨ p = 0` in the residual field. -/
example (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Γ₁(N)) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ (M : ℕ) (_ : NeZero M),
      ∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∣ N ∨ (p : κ) = 0) := by
  obtain ⟨M, hM, hdiv, -⟩ :=
    DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
      N ε f hf₁ hT R hR hε κ φ
  exact ⟨M, hM, hdiv⟩

/-! ## Zone S4/S5 — the coefficient ring and the semisimple descent

S4 (`CoefficientRing.lean`) produces the finite `ℤ`-subalgebra of `ℂ` generated by
the Hecke eigenvalues of a weight-one eigenform and the Galois-conjugate family;
S5 (`SemisimpleDescent.lean`) recovers a semisimple mod-`ℓ` representation from
additive and multiplicative `ι.range` conditions on two characters. Both zones
are hypothesis form (the Hecke-congruence data / the character conditions). -/

/-- S4: the coefficient ring is a finite `ℤ`-algebra. -/
example (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Γ₁(N)) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R := by
  obtain ⟨R, hRfin, -⟩ :=
    DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
      N ε f hf₁ hT
  exact ⟨R, hRfin⟩

/-- S5: the additive/multiplicative `ι.range` conditions produce a representation
whose Frobenius characteristic polynomial is `(X - χ₁)(X - χ₂)`. -/
example {G : Type} [Group G] {κ : Type} [Field κ] [Finite κ] {Ω : Type} [Field Ω]
    (ι : κ →+* Ω) (χ₁ χ₂ : G →* Ωˣ)
    (hadd : ∀ g : G, (χ₁ g : Ω) + χ₂ g ∈ ι.range)
    (hmul : ∀ g : G, (χ₁ g : Ω) * χ₂ g ∈ ι.range) :
    ∃ ρ : G →* GL (Fin 2) κ,
      ∀ g : G, (((ρ g : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        (X - C (χ₁ g : Ω)) * (X - C (χ₂ g : Ω)) := by
  obtain ⟨ρ, -, -, hchar⟩ :=
    DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
      ι χ₁ χ₂ hadd hmul
  exact ⟨ρ, hchar⟩

/-! ## Zone S6 — representation conjugacy

The finite-image conjugacy criterion (`RepConj.lean`) and its Frobenius form
(`ConjFromFrobenius.lean`), which composes it with the finite-level reduction. -/

/-- Two finite-image complex `GL₂` representations with equal characteristic
polynomials are conjugate. -/
example {G : Type*} [Group G] (ρ ρ' : G →* GL (Fin 2) ℂ)
    (hρ : Finite (MonoidHom.range ρ)) (hρ' : Finite (MonoidHom.range ρ'))
    (h : ∀ g : G, ((ρ g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      ((ρ' g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ g : G, ρ' g = P * ρ g * P⁻¹ :=
  Representation.exists_conj_eq_of_charpoly_eq_of_finite_range ρ ρ' hρ hρ' h

/-- The Frobenius form: agreement of the Frobenius characteristic polynomials
outside a finite set, for two finite-level representations, gives global
conjugacy. -/
example (ρ ρ' : Γℚ →* GL (Fin 2) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
            ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ σ : Γℚ, ρ' σ = P * ρ σ * P⁻¹ :=
  GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
    ρ ρ' hρ hρ' S h

/-! ## Zone S7 — Frobenius density and the degree-one-primes tail

`FrobeniusDensity.statement` (`Statement.lean`, from the S7-II asymptotic chain)
and the unconditional infinitude of primes with a `ZMod ℓ`-point of a finite
`ℤ`-algebra (`DegreeOnePrimesInfinite.lean`, the S7-I tail). -/

/-- The density statement at `L = ℚ`: every conjugacy class of `Gal(ℚ/ℚ)` is
realised by a prime outside any finite set `S`. -/
example (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ ∉ S ∧ FrobeniusDensity.RealizesCyclicAt ℚ (1 : ℚ ≃ₐ[ℚ] ℚ) ℓ :=
  FrobeniusDensity.statement ℚ 1 S

/-- The tail, composed with `Set.Infinite.mono`: infinitely many primes admit a
ring homomorphism `ℤ →+* ZMod ℓ`. -/
example : {ℓ : ℕ | ℓ.Prime}.Infinite :=
  Set.Infinite.mono (fun _ hℓ => hℓ.1)
    (CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int ℤ)

/-! ## Zone S8 — the complex-trace assembly (the capstone)

The capstone is conditional by design: `hfam` is the ray-class compatible family
of residual representations, whose discharge is deliberately out of scope
(`PORTING-DeligneSerre.md` §0.3). The zone is therefore stated in hypothesis form
and consumes the headline by extracting the resulting complex representation. -/

/-- The assembly applied to a compatible residual family. -/
example (N : ℕ) (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R]
    (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζR : ζ ∈ R)
    (t d : ℕ → ℂ) (ht : ∀ p : ℕ, p.Prime → ¬ p ∣ N → t p ∈ R)
    (hd : ∀ p : ℕ, p.Prime → ¬ p ∣ N → d p ∈ R)
    (hfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (φ : R →+* ZMod ℓ),
      ∃ ρ : Γℚ →* GL (Fin 2) (ZMod ℓ), GaloisFactorsThroughFiniteLevel ρ ∧
        Nat.card (MonoidHom.range ρ) ∣ m ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
                X ^ 2 - C (φ ⟨t p, ht p hp hpN⟩) * X + C (φ ⟨d p, hd p hp hpN⟩)) :
    ∃ ρ : Γℚ →* GL (Fin 2) ℂ, GaloisFactorsThroughFiniteLevel ρ := by
  obtain ⟨ρ, hρfl, -⟩ :=
    DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
      N R m hm ζ hζ hζR t d ht hd hfam
  exact ⟨ρ, hρfl⟩

/-! ## Zone S9 — the promoted rank-two charpoly conversion

`LinearMap.charpoly_eq_of_quadratic_of_det` is the port's promotion of the pin's
generated-namespace helper `E1G1ES.charpoly_eq_of_quadratic_of_det` — the
"quadratic relation + determinant ⟹ characteristic polynomial" step that the
weight-one → weight-two → Frobenius-charpoly route needs (the pin re-proves it in
eight `S_` files; studies/frobenius-charpoly-scout.md §4). The pin's own
statement is the source of truth here, so the checker diffs it rather than
exempting it.

Non-vacuous instantiation: the identity of `ℚ²`, written as
`algebraMap ℚ (Module.End ℚ (Fin 2 → ℚ)) 1`, satisfies
`f * f - 2 • f + 1 = 0` with `det f = 1`, so its characteristic polynomial is
`X² - 2X + 1`. -/

example :
    LinearMap.charpoly (algebraMap ℚ (Module.End ℚ (Fin 2 → ℚ)) 1)
      = X ^ 2 - C 2 * X + C 1 :=
  LinearMap.charpoly_eq_of_quadratic_of_det (by simp)
    (algebraMap ℚ (Module.End ℚ (Fin 2 → ℚ)) 1)
    (by rw [map_one]; exact isUnit_one)
    2 1
    (by norm_num [Algebra.smul_def, map_ofNat])
    (by rw [map_one]; simp)

end DeligneSerreConsumer
