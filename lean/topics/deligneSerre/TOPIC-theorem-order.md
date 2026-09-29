# Work order — phase T: the 54 theorem modules, importees first

**Status: work order, not started (2026-09-29).** Phase T of the 54-node slice:
the theorem modules, in the ten topological levels of the premise graph. Read
[TOPIC-port-order.md](TOPIC-port-order.md) first; phases D/H are in
[TOPIC-definitions-and-homes.md](TOPIC-definitions-and-homes.md); the mathematics
of these nodes is in
[TOPIC-weight-one-lifting-and-assembly.md](TOPIC-weight-one-lifting-and-assembly.md).

Method: restrict the citation graph to the 54 nodes and run Kahn's algorithm on
the premise relation (a node is ready when all its in-slice premises are placed).
The result is ten levels; **each level imports only levels below it**, so a
dispatch per level is a forward build. Levels 0–4 are mostly *generic home* nodes
(algebra, representation theory, Frobenius density, the Eisenstein construction);
the `DeligneSerre.*` nodes cluster in the later levels.

## The ten levels

| level | nodes | pin lines | what it is |
|---|---:|---:|---|
| **T0** | 25 | 5,121 | the leaves: the Eisenstein cotangent block, the Hecke/Γ₁ q-coefficient block, the generic algebra (lattice eigenvalues, minimal-prime eigenvector, rational coordinates), the representation conjugacy/lifting pair, the Frobenius-density zeta/coset block, the place/Frobenius vocabulary |
| **T1** | 11 | 2,206 | the relèvement (`exists_hecke_eigen_reduction`), the Eisenstein quasi-period step, the Möbius/fixed-coset and ideal-sum steps, the rational-coordinate conjugation step |
| **T2** | 4 | 1,111 | the Γ₁-invariance vanishing, the weight-one slash covariance, the degree-one count, the prime-ideal asymptotic |
| **T3** | 4 | 1,425 | the oddness derivation (`slash_eq_dirichlet_smul`), the Eisenstein boundedness, the degree-one asymptotic, the density-from-asymptotic step |
| **T4** | 4 | 1,400 | infinitely many primes for an order, the coefficient ring/Galois conjugation, the degree-one asymptotic statement, **the multiplier** (`exists_weightOne_eisenstein`) |
| **T5** | 2 | 1,254 | the weight-one → weight-two lifting, the qualitative Frobenius-density statement |
| **T6** | 1 | 47 | Frobenius-power density modulo a kernel |
| **T7** | 1 | 28 | Frobenius density modulo an open subgroup |
| **T8** | 1 | 171 | Galois conjugacy from equal Frobenius characteristic polynomials |
| **T9** | 1 | 463 | **the assembly** (`exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual`) |

Total 54 nodes / 13,226 pin lines.

## Per-level dispatch

**T0 (25 nodes) — the leaves, home them by subject.** This is the level with the
most reuse risk; port each node into its subject home (not a DeligneSerre file):

- Eisenstein: `EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2` →
  `ModularForms/Eisenstein/`.
- Hecke/Γ₁: `CuspForm.{HasNebentypus.diamondLinOne_apply_eq_smul, qCoeff_heckeTLinOne,
  heckeTLinOne_slashOfMemGamma0, eq_zero_of_forall_vadd_inv_pow_eq}`,
  `ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` →
  `ModularForms/`; `Ihara.amalgamToGamma0Away_surjective` → `ModularCurve/`.
- Algebra: `Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top`,
  `Module.Basis.repr_mem_range_ratCast_of_forall_dual`,
  `integralClosure.exists_complex_ringEquiv_apply_eq` → `Algebra/`;
  `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul` →
  `Algebra/` (it is generic algebra despite the namespace).
- Representation: `Representation.{exists_conj_eq_of_charpoly_eq_of_finite_range,
  exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard}`,
  `DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range`
  → `GaloisRep/` or `Algebra/`.
- Frobenius density / places: the `FrobeniusDensity.*` leaves,
  `ArithmeticFunction.sum_moebius_filter_dvd`,
  `NumberField.{exists_isFrobenius_lift_arithFrobAt, exists_valuationSubring_eq_localization}`,
  the `ValuationSubring.*` family, `IsOpen.exists_numberField_ker_restrictNormalHom_le`
  → `NumberTheory/FrobeniusDensity/` and `NumberTheory/`.

**T1–T4 — the two chains.** The *lifting* chain builds the Eisenstein series and
the Hecke vanishing (T1–T3) toward the multiplier at T4; the *density* chain
builds the Möbius/coset counts toward the density statement. The generic algebra
conjugation step is T1. Port each node into its home.

**T5–T9 — the DS-specific nodes.** `exists_weightTwo_hecke_eigen_reduction` (T5)
and the assembly (T9) are `DeligneSerre/`; T6–T8 are the density and conjugacy
steps that feed the assembly. T9 imports T8, T7, T6, T5 and the T4 coefficient-ring
node.

## Closing each level

- `timeout 120 lake build <module>` green, no `sorry`/`admit`;
- statement checker 0 mismatched / 0 missing for the level's files;
- `#print axioms` clean on the level's headlines;
- any local copy of a closed file's lemma is recorded in
  `lean/logs/deligne-serre-friction.md`;
- once green, the level's files are **closed**.

Do not start a level whose in-slice premises are not closed. If a level needs a
change in an earlier file, resolve it locally and log it — the refactor round owns
the promotion.
