# Topic: the weight-one lifting and assembly (54 nodes)

**Status: work order, not started (2026-09-29).** The first set of the
Deligne–Serre weight-one port — the unconditional slice. It is the whole
`DeligneSerre.*` content that does not depend on the shared ray-class
$`L`$-function: the weight-one Eisenstein multiplier, the Hecke/$`\Gamma_1`$
vanishing lemmas, the relèvement and the lifting, the coefficient ring and Galois
conjugation, the semisimple descent, the representation conjugacy, the Frobenius
density input, and the complex-trace assembly.

**Read, in order.** [porting-playbook.md](../../porting-playbook.md) (all of it;
§2.4 for the dedup discipline, §3.1–§3.3 for module-as-role and one-topic-at-a-time,
§4 for faithfulness); [../../../math/019-deligne-serre-weight-one.md](../../../math/019-deligne-serre-weight-one.md)
§3–§4 (the mathematics this set implements); [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md)
§1–§4 (the overall plan and the port-advice reading); and
[../../../studies/deligne-serre-weight-one-scout.md](../../../studies/deligne-serre-weight-one-scout.md)
§2–§3.1 (why this slice is unconditional).

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 120 lake build <module>`. A multi-minute build is never acceptable.
- **Never raise `maxHeartbeats` / `maxRecDepth`.** On a non-return, comment the
  declaration out and bisect, or reproduce in the gitignored `Scratch.lean` with a
  low cap. The usual causes are a `FunLike`-quantified lemma at a bare function
  type and concrete intermediate-field defeqs (playbook §6).
- Tell a blow-up from contention by CPU time: high user CPU + timeout is a real
  blow-up; ~0 CPU wall time is lock contention with another agent.

## 0. The cone

54 theorem nodes / 13,226 raw `S_` lines / 20 pin definition modules (2,752
lines), measured against `aa2d8b3`. Eight sets, each a mathematical subject:

| set | subject | nodes | `S_` lines | depends on |
|---|---|---:|---:|---|
| **S1** | weight-one Eisenstein series | 5 | 2,270 | mathlib, the `EisensteinSeries`/`WeierstrassZeta` definitions |
| **S2** | Hecke / $`\Gamma_1`$ vanishing and nebentypus | 9 | 2,286 | the ported Hecke/`Γ` vocabulary |
| **S3** | relèvement and weight-one $`\to`$ weight-two lifting | 2 | 1,918 | S1, S2 |
| **S4** | coefficient ring and Galois conjugation | 6 | 1,349 | generic algebra |
| **S5** | semisimple descent of a reducible residual representation | 1 | 675 | finite-field algebra |
| **S6** | representation conjugacy and lifting | 3 | 1,036 | finite-group representation theory |
| **S7** | Frobenius density and Frobenius elements | 27 | 3,229 | number fields, prime ideals |
| **S8** | complex-trace assembly from the residual family | 1 | 463 | S4, S5, S6, S7 |

The set contents are listed in the appendix. S1–S3 are the *lifting* half
(weight one in, weight two out); S4–S8 are the *assembly* half (residual family in,
complex representation out); S4–S8 do not depend on S1–S3.

## 1. Set-by-set work order

Each set closes with its own review gate (statements checked, `#print axioms`,
build green) before the next starts.

### S1 — the weight-one Eisenstein series (5 nodes)

| node | `S_` |
|---|---:|
| `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd` | 703 |
| `EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2` | 539 |
| `EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1` | 532 |
| `EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul` | 284 |
| `EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add` | 212 |

The mathematics is `math/019` §3 (the multiplier): $`E_1(1,\chi)`$ for a primitive
odd $`\chi`$, built from the cotangent expansion of the Weierstrass
$`\zeta`$-function and its quasi-periods; the $`q`$-expansion has constant term
$`-B_{1,\chi}/2`$ and coefficients $`\sigma_\chi(n)`$. **Home:** extend
`ModularForms/EisensteinSeries.lean`, or a new `ModularForms/Eisenstein/`; the
quotient $`\mathrm{WeierstrassZeta}`$ definitions live in the pin's
`EisensteinSeries_WeierstrassZeta`.

**Dedup.** This set has the largest shared-prelude saving: `norm_pi_cot_add_le`
(44 lines × 3), `pi_cot_add_eq` (24 × 3), `norm_pi_cot_sub_le` (18 × 3) and the
`cot`/`Gammaℝ` factor lemmas are proved in several of the five files. Give the
cotangent/factor calculus one home in the S1 module; do not copy it per target.

### S2 — Hecke / $`\Gamma_1`$ vanishing and nebentypus (9 nodes)

| node | `S_` |
|---|---:|
| `Ihara.amalgamToGamma0Away_surjective` | 612 |
| `CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen` | 436 |
| `CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` | 381 |
| `ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` | 379 |
| `CuspForm.qCoeff_heckeTLinOne` | 178 |
| `CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant` | 173 |
| `CuspForm.eq_zero_of_forall_vadd_inv_pow_eq` | 76 |
| `CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul` | 29 |
| `CuspForm.heckeTLinOne_slashOfMemGamma0` | 22 |

The mathematically substantive pair is the *oddness derivation* (the Hecke
eigen-relation forces the nebentypus, `slash_eq_dirichlet_smul_…`) and the
*vanishing lemma* (a $`\Gamma_1`$-cusp form invariant under $`\mathrm{diag}(p,1)`$,
after the diamond correction, is zero), which is what makes the lifting's
congruence nonzero. The `qCoeff`/slash commutation lemmas are the plumbing that
feeds them.

**Home:** the Hecke and $`\Gamma_1`$ vocabulary already lives in
`ModularForms/` (`HeckeInvariance`, `HeckeQCoeff`, `HeckeLattice`, …) and
`ModularForms/WeightOne/`; the new statements go there, not into a new directory.
`Ihara.amalgamToGamma0Away_surjective` is a group-theoretic input with its own
definition layer (`IharaAmalgam`, `IharaAmalgamMap`, `Gamma0Away`, `IharaIota`);
home it with the modular-curve/Ihara material.

**Reuse.** This set is where the port is richest: `periodic_of_slash_T`
(22 × 3), `finite_range_of_factorsThroughFiniteLevel` (28 × 2) and several
`T_mem_Gamma1`/`heckeDiagMatrix_mul` lemmas already exist (28 substitutions, 22
name clashes). Read the substitution and clash lists before writing anything; a
`port_advise` clash that differs only in binders is resolved by taking the wrapper's
binders.

### S3 — the relèvement and the lifting (2 nodes)

| node | `S_` |
|---|---:|
| `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` | 1,242 |
| `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` | 676 |

The heart of the batch. The second is the weight-generic **relèvement** (`math/019`
§3): a residual eigenvector of the Hecke algebra on a finite-dimensional space of
cusp forms lifts to a genuine eigenform. The first is the FLT lifting: multiply
the weight-one form by the normalized Eisenstein series of S1 (the Teichmüller
character for odd $`\ell`$, the character mod $`4`$ for $`\ell = 2`$, with the
congruence $`\chi(p)p \equiv 1`$), then apply the relèvement. Home both in a new
`DeligneSerre/` directory; the relèvement is weight-generic, so keep it separate
from the weight-one instance.

**Dedup.** `DeligneSerre.exists_weightTwo_…` duplicates the Hecke/`Γ` prelude
(`locKer`, the `mdifferentiable_heckeU` copy, the `periodic_smul` family) that S2
homes; the port_advise substitution list flags 7 port-private statements to
promote here.

### S4 — coefficient ring and Galois conjugation (6 nodes)

| node | `S_` |
|---|---:|
| `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen` | 491 |
| `integralClosure.exists_complex_ringEquiv_apply_eq` | 277 |
| `Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top` | 163 |
| `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul` | 144 |
| `Module.Basis.repr_mem_range_ratCast_of_forall_dual` | 143 |
| `Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast` | 131 |

The finiteness of the coefficient ring and the Galois action on weight-one
newforms (`math/019` §3). The five non-`DeligneSerre` nodes are generic algebra:
integral eigenvalues of a lattice-preserving operator family, eigenvector extraction
from a minimal prime, and rational coordinates in a rational-operator basis. Home
them in `Algebra/` (`FaithfulLatticeEigenvector`, `IntegralExtensionCharacters`
already exist there) and keep only the weight-one statement in `DeligneSerre/`.

### S5 — semisimple descent (1 node)

`DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range`
(675 lines). If the trace and determinant of a residual representation are known
to lie in a subfield, the two characters descend and the representation is
semisimple over that subfield (`math/019` §4). The proof is a finite-field
Frobenius argument (`x \mapsto x^q`). Home in `Algebra/` or `GaloisRep/`.

### S6 — representation conjugacy and lifting (3 nodes)

| node | `S_` |
|---|---:|
| `Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard` | 685 |
| `Representation.exists_conj_eq_of_charpoly_eq_of_finite_range` | 180 |
| `GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel` | 171 |

Character determines a finite-group representation up to conjugacy, and a mod-$`\ell`$
representation of an $`\ell'`$-group lifts to characteristic zero with matching
characteristic polynomials (`math/019` §4). The Galois form converts "equal
charpolys at almost all Frobenius elements" into global conjugacy, using S7's
density theorem. Home in `GaloisRep/`.

### S7 — Frobenius density and Frobenius elements (27 nodes)

The qualitative Frobenius density theorem (Chebotarev) from the degree-one prime
asymptotic, plus the places/Frobenius vocabulary it is stated with. The 27 nodes
are listed in the appendix; the substantive targets are
`FrobeniusDensity.degOneAsymptotic`, `FrobeniusDensity.primeSum_toReal_add_log_isBigO`,
`FrobeniusDensity.statement_of_degOneAsymptotic`,
`NumberField.exists_isFrobenius_lift_arithFrobAt`, and
`CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int` (which
S8 also uses). Home in a new `NumberTheory/FrobeniusDensity/`, extending the
existing `NumberTheory/{FrobeniusAtPlace,ValuationAtPlace}.lean`.

**Dedup.** `sum_moebius_mem_zpowers` (39 × 2), `mem_zpowers_pow_div_iff`
(30 × 2), `tsum_normFiber` (22 × 2), `isBigO_sum_of_tendsto_div` (20 × 2) and the
`FrobeniusDensity` Möbius/fixed-coset lemmas repeat across the 17 `FrobeniusDensity`
files; one shared `Defs` module for the fixed-coset count is the saving.

### S8 — the assembly (1 node)

`DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual`
(463 lines). Glue a compatible family of residual representations into a complex
representation with the prescribed traces and determinants (`math/019` §4): a
nonzero element of the finite $`\mathbb{Z}`$-algebra is detected by infinitely many
primes, and the trace of a finite-order $`2 \times 2`$ matrix is a sum of two roots
of unity. Home in `DeligneSerre/Assembly.lean`.

**This is the set that the deferred statement replaces.** S8 takes the residual
family as a *hypothesis* (`hfam`), so it lands without `M4aTorus.completedRayL_fe`.
The Group B lemmas (`isIrreducible_…_of_odd`, `exists_natCard_range_le`), which
*do* reach the ray-class node, are outside this work order.

## 2. Reuse, dedup and generalisation — the pre-port actions

The `port_advise` reading (reproduce in [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md)
§3) gives four actions to take **before** writing:

1. **Substitutions (28; 21 importable, 7 port-private).** Import the 21; promote
   the 7 port-private copies (mostly in `Defs/HeckeRepresentatives.lean`,
   `Level/Diamond.lean`, `WeightOne/`) or lift them to a shared home.
2. **Port once (78 in-target helpers, 585 removable lines).** The S1 and S7
   preludes dominate; the per-set notes above name the blocks.
3. **Generalise or take the wrapper binders (237 near-duplicates; 120 binder-only).**
   A binder-only duplicate takes the pin wrapper's binders (playbook §7.4); a
   genuine duplicate is generalised into one lemma.
4. **Reconcile name clashes (22; 5 binder-only).** The port already defines these
   names with near-identical statements; the checker's name map must agree before
   the declaration is written.

## 3. Faithfulness and review gates

- Every public target keeps the pin's `DeligneSerre.*` / `FrobeniusDensity.*` /
  `Representation.*` name and statement; proofs may be reorganized.
- Per set: statement checker at 0 mismatched / 0 missing for the set's
  declarations; `lake build` green; `#print axioms` is
  `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`.
- Record the review in [../../logs/](../../logs/) (a
  `deligne-serre-port.md` record, as the other efforts keep).

## 4. Build ladder

S8 is the only set whose targets are stated late; everything else is a leaf or a
short chain, so there is no patching-style cascade. Build each module with
`lake build` and check with the statement checker before moving to the next set;
use a conditional skeleton (playbook §2.3) if S8 is written before S4–S7 land —
its `hfam` hypothesis makes that natural.

## Appendix: the 54 nodes

**S1 (5).** `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd`;
`EisensteinSeries.{hasSum_weierstrassZeta_sub_mul_G2,
isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1,
weierstrassZeta_add_one_and_add_tau_and_smul,
eisensteinG1_apply_smul_and_eisensteinG1_add}`.

**S2 (9).** `CuspForm.{slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen,
eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1,
vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant,
eq_zero_of_forall_vadd_inv_pow_eq, qCoeff_heckeTLinOne,
heckeTLinOne_slashOfMemGamma0, HasNebentypus.diamondLinOne_apply_eq_smul}`;
`ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`;
`Ihara.amalgamToGamma0Away_surjective`.

**S3 (2).** `DeligneSerre.{exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen,
exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr}`.

**S4 (6).** `DeligneSerre.{exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen,
exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul}`;
`integralClosure.exists_complex_ringEquiv_apply_eq`;
`Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top`;
`Module.Basis.{repr_mem_range_ratCast_of_forall_dual,
exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast}`.

**S5 (1).** `DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range`.

**S6 (3).** `Representation.{exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard,
exists_conj_eq_of_charpoly_eq_of_finite_range}`;
`GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`.

**S7 (27).** `FrobeniusDensity.{degOneAsymptotic, degOneSum_add_log_isBigO,
exists_frobenius_conj_pow_of_statement, frobeniusPowerDense_of_le_ker,
idealSum_ne_top, ncard_conj_gen_ne_zero_iff,
ncard_degreeOne_primesOver_eq_ncard_frobFixed, ncard_degreeOne_primesOver_under,
primeSum_eq_degOneSum_add, primeSum_toReal_add_log_isBigO,
stabilizer_eq_zpowers_arithFrobAt, statement,
statement_of_degOneAsymptotic, sum_moebius_mul_pos, summable_degOne_term,
tendsto_sub_one_mul_idealSum_test, weight_eq}`;
`ArithmeticFunction.sum_moebius_filter_dvd`;
`CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`;
`IsOpen.exists_numberField_ker_restrictNormalHom_le`;
`NumberField.{exists_isFrobenius_lift_arithFrobAt,
exists_valuationSubring_eq_localization}`;
`Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`;
`ValuationSubring.{exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat,
exists_liesOverPrime_algebraicClosure_rat,
exists_liesOverPrime_isFrobeniusAt_ratAlgClosure,
isFrobeniusAt_of_forall_smul_sub_pow_mem}`.

**S8 (1).** `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual`.
