# Work order — S6: representation conjugacy and lifting (3 nodes)

**Status: ready to dispatch — H, S1–S5 and S7 are closed and green (checker 2548/0/0);
S6c's S7 dependency is now available.** Method handbook:
`lean/porting-playbook.md` (§3.1–§3.5, §4). Mathematics: `math/019` §4.

## 0. Scope

Character determines a finite-group representation up to conjugacy; a mod-`ℓ`
representation of an `ℓ'`-group lifts to characteristic zero with matching
characteristic polynomials; the Galois form converts "equal charpolys at almost all
Frobenius elements" into global conjugacy. Three nodes, 1,036 pin lines.

**Explicitly not this set:** S7's density theorem (imported), S5, S8.

## 1. The three public targets — statements verbatim

```lean
theorem Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
    (G : Type) [Group G] [Finite G]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Nat.card G)
    (k : Type) [Field k] [Finite k] [CharP k ℓ]
    (n m : ℕ) (hm : 0 < m) (hℓm : ¬ ℓ ∣ m) (hGm : ∀ g : G, g ^ m = 1)
    (S : Subalgebra ℤ ℂ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζS : ζ ∈ S) (φ : S →+* k)
    (ρbar : G →* GL (Fin n) k) :
    ∃ ρ : G →* GL (Fin n) ℂ, ∀ g : G, ∃ P : Polynomial S,
      P.map (algebraMap S ℂ) = ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly ∧
      P.map φ = ((ρbar g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly
```

```lean
theorem Representation.exists_conj_eq_of_charpoly_eq_of_finite_range
    {G : Type*} [Group G] (ρ ρ' : G →* GL (Fin 2) ℂ)
    (hρ : Finite (MonoidHom.range ρ)) (hρ' : Finite (MonoidHom.range ρ'))
    (h : ∀ g : G, ((ρ g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      ((ρ' g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ g : G, ρ' g = P * ρ g * P⁻¹
```

```lean
theorem GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
    (ρ ρ' : Γℚ →* GL (Fin 2) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
            ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ σ : Γℚ, ρ' σ = P * ρ σ * P⁻¹
```

(`Γℚ` is the pin's local notation for
`AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`; restate it at the port's spelling.)

## 2. Homes and order

All three keep the pin's `Representation.*` / `GaloisRep.*` names.

| order | node | new module | prerequisites |
|---:|---|---|---|
| 1 | `Representation.exists_conj_eq_of_charpoly_eq_of_finite_range` | `GaloisRep/RepConj.lean` | mathlib finite-group representation theory |
| 2 | `Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard` | `GaloisRep/RepLift.lean` | mathlib `CharP`, `IsPrimitiveRoot`, Brauer–Nesbitt/Brauer character theory |
| 3 | `GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel` | `GaloisRep/ConjFromFrobenius.lean` | H1 `GaloisRep/Prelude.lean` (`finite_range_of_factorsThroughFiniteLevel`); S7's `FrobeniusDensity.statement`, `statement_of_degOneAsymptotic`, `frobeniusPowerDense_of_le_ker` and `Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`; the ported `ValuationSubring.{LiesOverPrime,IsFrobeniusAt}` vocabulary |

The H1 Prelude also carries `isOpen_ker` in its pin source; port it into
`ConjFromFrobenius.lean` (or extend the prelude in the refactor round) if node 3 needs
it. `#check` the `ValuationSubring` API in
`NumberTheory/{ValuationAtPlace,FrobeniusAtPlace}.lean` before writing.

**Node 2's own def layer is already on disk:** phase D's
`FLTForHuman/Algebra/BrauerNesbitt.lean` (`Def_RepTheory_BrauerNesbitt_TraceCharZero`)
provides the Brauer–Nesbitt trace/character-zero vocabulary — `#check` it before
writing node 2. The pin's node-2 file also carries a Witt-vector lifting block
(`exists_unit_lift`, `exists_lift'`, `BrauerLiftComplete.*`, `charZero_witt`,
`teichmuller_injective`, `mk_witt`); treat those as the private closure.

Route: node 2 is the risk (685 lines; Brauer–Nesbitt trace and the `m`-th root of
unity reduction, plus the Witt lifting). If mathlib lacks a needed Brauer-character result, record the
negative and stop rather than weaken the statement. Node 3 is glue over node 1,
H1's finiteness and S7's density/dichotomy.

## 3. Verification, build discipline, closing

As `WORKORDER-S1-eisenstein.md` §4: checker wiring appended last; edit loop
`timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
file-done `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.<Dotted.Path>`;
no bare whole-tree `lake build`; no `sorry`/`admit`/`axiom`; no `import Mathlib`;
`#print axioms` clean; friction log appended; no writing git commands.

---

## Appendix — pin declaration inventory

#### S6a — pin `P2M/Sol/S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.lean` (685 lines, 31 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `oneAdd` | def | 13 | 14 |  |
| `exists_unit_lift` | theorem | 27 | 34 |  |
| `_root_.BrauerLiftSqZero.exists_lift` | theorem | 61 | 127 | yes |
| `exists_lift'` | theorem | 188 | 19 |  |
| `le_pow_succ` | theorem | 207 | 2 |  |
| `_root_.BrauerLiftComplete.trans` | def | 209 | 3 | yes |
| `trans_mk` | theorem | 212 | 2 |  |
| `trans_surjective` | theorem | 214 | 3 |  |
| `trans_eq_zero_iff` | theorem | 217 | 4 |  |
| `mul_eq_zero_of_trans` | theorem | 221 | 10 |  |
| `Trans` | def | 231 | 3 |  |
| `Trans_surjective` | theorem | 234 | 6 |  |
| `Trans_sqzero` | theorem | 240 | 10 |  |
| `step` | theorem | 250 | 9 |  |
| `seq` | def | 259 | 5 |  |
| `seq_zero` | theorem | 264 | 3 |  |
| `seq_succ` | theorem | 267 | 5 |  |
| `seq_succ_apply` | theorem | 272 | 8 |  |
| `smodEq_pow_iff` | theorem | 280 | 6 |  |
| `eq_zero_of_forall_mem` | theorem | 286 | 7 |  |
| `exists_limit` | theorem | 293 | 33 |  |
| `exists_lift` | theorem | 326 | 76 |  |
| `exists_ringHom_comp_algebraMap` | theorem | 402 | 32 |  |
| `charZero_witt` | theorem | 434 | 31 |  |
| `teichmuller_injective` | theorem | 465 | 6 |  |
| `mk_witt` | theorem | 471 | 11 |  |
| `exists_embedding` | theorem | 482 | 56 |  |
| `map_prod_X_sub_C_pow` | theorem | 538 | 8 |  |
| `pow_eq_one_of_mem_roots_charpoly` | theorem | 546 | 15 |  |
| `main` | theorem | 561 | 114 |  |
| `solution` | theorem | 675 | 11 |  |

#### S6b — pin `P2M/Sol/S_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean` (180 lines, 10 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `repOfGL` | def | 22 | 12 |  |
| `trace_repOfGL` | theorem | 34 | 4 |  |
| `actionEndo_of_eq_conj` | theorem | 38 | 10 |  |
| `trace_actionEndo_of` | theorem | 48 | 7 |  |
| `exists_linearEquiv_of_asModule_equiv` | theorem | 55 | 11 |  |
| `exists_conj_eq_of_linearEquiv` | theorem | 66 | 28 |  |
| `exists_conj_eq_of_trace_eq` | theorem | 94 | 36 |  |
| `trace_eq_of_charpoly_eq` | theorem | 130 | 8 |  |
| `exists_conj_eq_of_charpoly_eq_of_finite_range` | theorem | 138 | 36 |  |
| `solution` | theorem | 174 | 7 |  |

#### S6c — pin `P2M/Sol/S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean` (171 lines, 7 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `finite_range_of_factorsThroughFiniteLevel` | theorem | 18 | 28 |  |
| `isOpen_ker` | theorem | 46 | 14 |  |
| `sq_eq_trace_smul_sub` | theorem | 60 | 10 |  |
| `trace_pow_eq_of_trace_eq_of_det_eq` | theorem | 70 | 19 |  |
| `charpoly_pow_eq_of_charpoly_eq` | theorem | 89 | 20 |  |
| `charpoly_eq_of_frobenius` | theorem | 109 | 49 |  |
| `solution` | theorem | 158 | 14 |  |
