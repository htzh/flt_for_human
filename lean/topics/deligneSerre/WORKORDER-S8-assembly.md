# Work order — S8: the complex-trace assembly (1 node)

**Status: ready to dispatch — the final theorem set; H and S1–S7 are closed and green
(checker 2551/0/0).** Method handbook:
`lean/porting-playbook.md` (§2.3 conditional capstone, §3.1–§3.5, §4).
Mathematics: `math/019` §4.

## 0. Scope

Glue a compatible family of residual representations into a complex representation
with the prescribed traces and determinants. This is the set the deferred statement
replaces: S8 takes the residual family as a **hypothesis** (`hfam`), so it lands
without `M4aTorus.completedRayL_fe` and without the density-dependent Group B
lemmas. 463 pin lines.

**Prerequisites, all on disk:** S4's `DeligneSerre/CoefficientRing.lean`; S5's
`GaloisRep/SemisimpleDescent.lean`; S6's `GaloisRep/{RepConj,RepLift,ConjFromFrobenius}.lean`;
S7's `NumberTheory/FrobeniusDensity/{Statement,DegreeOnePrimesInfinite}.lean`
(`FrobeniusDensity.statement`, `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`);
H1's `GaloisRep/Prelude.lean` (`finite_range_of_factorsThroughFiniteLevel`); and the
D0 `GaloisRep/Defs/{MatrixRepresentation,Residual,Ramification}.lean`. `#check` each
before writing.

**Explicitly not this set:** the Group B lemmas (`isIrreducible_…_of_odd`,
`exists_natCard_range_le`) which reach the ray-class node.

## 1. The public target — statement verbatim

```lean
theorem DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
    (N : ℕ) (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R]
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
    ∃ ρ : Γℚ →* GL (Fin 2) ℂ, GaloisFactorsThroughFiniteLevel ρ ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = t p ∧
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = d p
```

(`Γℚ` is the pin's local notation for
`AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`; restate at the port's spelling.)

## 2. Home

New module `FLTForHuman/DeligneSerre/Assembly.lean`, namespace `DeligneSerre`.

**Conditional shape is intended.** The `hfam` hypothesis is genuine mathematics, not
debt: build the file unconditionally, with `hfam` as a hypothesis. Do **not** try to
discharge it from ray-class analysis (out of scope, §0.3 of `PORTING-DeligneSerre.md`).

## 3. Route and risk

- Two ingredients: a nonzero element of the finite `ℤ`-algebra `R` is detected by
  infinitely many primes (S7's `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`),
  and the trace of a finite-order `2×2` matrix is a sum of two roots of unity (S6).
- `#check` the ported `ValuationSubring.{LiesOverPrime,IsFrobeniusAt,inertiaSubgroupIn}`
  and `GaloisFactorsThroughFiniteLevel` before writing.
- Keep helpers `private`; record a negative for any mathlib search that finds nothing.
- Writing this file is the effort's **final wire test**: a wrong binder or a missing
  upstream lemma surfaces here. That is the point.

## 4. Verification, build discipline, closing

As `WORKORDER-S1-eisenstein.md` §4: checker wiring appended last; edit loop
`timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
file-done `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.DeligneSerre.Assembly`;
no bare whole-tree `lake build`; no `sorry`/`admit`/`axiom`; no `import Mathlib`;
`#print axioms` clean; friction log appended; no writing git commands.

---

## Appendix — pin declaration inventory

#### S8 — pin `P2M/Sol/S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual.lean` (463 lines, 13 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `finite_range_of_factorsThroughFiniteLevel` | theorem | 21 | 28 |  |
| `exists_int_ne_zero_mem_span` | theorem | 49 | 28 |  |
| `finite_setOf_prime_exists_apply_eq_zero` | theorem | 77 | 16 |  |
| `eq_of_infinite_setOf_apply_eq` | theorem | 93 | 8 |  |
| `root_of_unity_of_charpoly` | theorem | 101 | 11 |  |
| `exists_trace_eq_add_of_pow_eq_one` | theorem | 112 | 16 |  |
| `coeff_quadratic` | theorem | 128 | 6 |  |
| `exists_lift_at` | theorem | 134 | 76 |  |
| `infinite_setOf_prime_nonempty` | theorem | 210 | 4 |  |
| `exists_eq_add_eq_mul` | theorem | 214 | 74 |  |
| `exists_good_lift` | theorem | 288 | 53 |  |
| `finite_setOf_prime_exists_apply_eq` | theorem | 341 | 14 |  |
| `solution` | theorem | 355 | 109 |  |
