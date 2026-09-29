# The Deligne–Serre weight-one port — status and subject plan

**Status: SCOPED, port not started (2026-09-29).** Measured against the pin
`aa2d8b3` with `tools/deps`; the port's mathlib is `v4.34.0`. This note is the
overall status and subject plan. The first work order — the 54-node unconditional
"lifting and assembly" slice — is
[deligneSerre/TOPIC-weight-one-lifting-and-assembly.md](deligneSerre/TOPIC-weight-one-lifting-and-assembly.md).

Companions:

- [../../math/019-deligne-serre-weight-one.md](../../math/019-deligne-serre-weight-one.md)
  — the mathematics: the theorem, the lifting, the assembly from residual data.
- [../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
  — the effort measurement, the subject clusters, and the deferral of the shared
  ray-class input (§2–§3.1 there).
- [porting-playbook.md](../porting-playbook.md) — the rules; §2.4 (dedup before
  coding), §3.2 (one directory per theory), §3.3 (a topic at a time, with a work
  order), §4 (faithfulness).
- Adjacent efforts this cone is stated against: [PORTING-Hecke.md](PORTING-Hecke.md)
  (the Hecke operators, eigenform dictionary, integral lattice), and
  [PORTING-Level.md](PORTING-Level.md) (the `Γ_H` / `Γ₁` / diamond vocabulary).

## 0. What this effort is, and is not

**Is.** The weight-one `DeligneSerre.*` family in the three shapes FLT uses:

* **forward** — a normalized weight-one cuspidal newform produces an odd
  finite-image $`\rho_f : G_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{C})`$ with
  $`\mathrm{charpoly}(\rho_f(\mathrm{Frob}_p)) = X^2 - a_p X + \varepsilon(p)`$
  at good $`p`$;
* **lifting** — the reduction of a weight-one mod-$`\ell`$ eigenform is a weight-two
  mod-$`\ell`$ eigenform (multiplication by a weight-one Eisenstein series, then the
  *relèvement*);
* **assembly** — the semisimple descent, characteristic-polynomial conjugacy, and
  complex-trace gluing that turn a compatible family of residual representations
  into the complex one.

**Is not** (and is deferred behind interfaces, §6): the two analytic gates (the
Rankin-type second-moment bound and the coefficient-ring upper-density argument),
the automorphic/adèlic layer those gates rest on, the ray-class
$`L`$-function's functional equation, the Frobenius-density/Chebotarev analytic
block, and the converse cone's Artin-$`L`$ functional equation.

## 1. The cone

| target | cone | already ported (in cone) | new nodes / raw `S_` lines |
|---|---:|---:|---:|
| `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | 2,308 | 309 | 1,988 / 995,359 |
| `DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | 1,528 | 307 | 1,210 / 622,105 |
| `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | 439 | 18 | 421 / 196,678 |
| `FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd` (endgame consumer) | 7,222 | 331 | 6,713 / 4,325,955 |

The cone splits three ways, and the split is the plan:

| slice | nodes | raw `S_` lines | status |
|---|---:|---:|---|
| **unconditional** — lifting + assembly (the first batch) | 54 | 13,226 | this effort's first target |
| density-dependent — `isIrreducible_…_of_odd`, `exists_natCard_range_le` | 22 | 20,391 | behind the ray-class-continuation interface |
| analytic gates — `exists_tsum_norm`, `exists_finset_qCoeff_mem` | ~775 each | (automorphic cone) | the automorphic subject |
| converse cone — local factors + Artin conductor | 421 | 196,678 | a separate subject |

Deferring the single statement `M4aTorus.completedRayL_fe` (the batch's only route
into the ray-class $`L`$-function, and only through its *analytic-continuation*
conjunct) takes the 54-node batch with the two density lemmas from 70 nodes /
32,804 lines to 69 / 20,678; adding the density block as a second interface leaves
59 / 15,654. The measurement and the interface argument are
[../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
§3.1.

## 2. What ships first — the 54-node group

Eight sets, ordered so each can be reviewed before the next. The subject of each
set is the mathematics, not the pin file.

| set | subject | nodes | `S_` lines | math |
|---|---|---:|---:|---|
| **S1** | weight-one Eisenstein series | 5 | 2,270 | `math/019` §3 (the multiplier): $`E_1(1,\chi)`$, cotangent expansion, divisor sums |
| **S2** | Hecke / $`\Gamma_1`$ vanishing and nebentypus | 9 | 2,286 | the eigenvalue relation forces $`\varepsilon`$; a $`\Gamma_1`$-form invariant under $`\mathrm{diag}(p,1)`$ vanishes |
| **S3** | relèvement and weight-one $`\to`$ weight-two lifting | 2 | 1,918 | `math/019` §3 (the relèvement) |
| **S4** | coefficient ring and Galois conjugation | 6 | 1,349 | `math/019` §3 (the coefficient ring) |
| **S5** | semisimple descent of a reducible residual representation | 1 | 675 | `math/019` §4 |
| **S6** | representation conjugacy and lifting | 3 | 1,036 | `math/019` §4 |
| **S7** | Frobenius density and Frobenius elements | 27 | 3,229 | `math/019` §4 (the density input) |
| **S8** | complex-trace assembly from the residual family | 1 | 463 | `math/019` §4 (the gluing) |
| | **total** | **54** | **13,226** | |

Dependency order: S1 and S2 feed S3; S4 and S5 are independent of S1–S3; S6 and
S7 feed the assembly; S1, S4, S6 and S7 are the prerequisites of S8. The topic
note gives the per-set module plan.

## 3. What the pins already give us (`port_advise`)

`port_advise.py` was run on the 54 nodes; the JSON is
[`tools/deps/build/groupA_advise.json`](../../tools/deps/build/groupA_advise.json)
(54 qualified names, 108 target files — each node's `Thm_` and `S_` — and 963
declarations). Reproduce:

```bash
cd tools/deps
python3 port_advise.py --nodes "$(paste -sd, build/groupA_nodes.txt)" --json build/groupA_advise.json
```

The pre-port reading:

| finding | count | action |
|---|---:|---|
| **substitutions** — a byte-identical statement already in the port | 28 (21 importable, 7 port-private) | import; if private, promote or lift to a shared home |
| **port-once** — a helper proved in ≥2 target files | 78 in-target, **585 removable lines** | one shared home, not per consumer |
| **near-duplicates** — same name, different statement | 237 (120 binder-only, 117 genuine) | take the pin wrapper's binders, or generalise |
| **port name clashes** — the port already has this name, different statement | 22 (5 binder-only) | reconcile before writing; the checker's name map must agree |
| **new private helpers** — same-file closure of the public targets | 98 helpers / 1,296 lines, 16 files | the actual new low-level work |

The largest dedup targets are in S1/S2 and are all `EisensteinSeries`/`CuspForm`
preludes: `norm_pi_cot_add_le` (44 lines, 3 copies), `sum_moebius_mem_zpowers`
(39, 2), `mem_zpowers_pow_div_iff` (30, 2),
`finite_range_of_factorsThroughFiniteLevel` (28, 2), `pi_cot_add_eq` (24, 3),
`periodic_of_slash_T` (22, 3), `tsum_normFiber` (22, 2). The 28 substitutions are
concentrated in the already-ported Hecke/`Γ` vocabulary
(`Defs/HeckeRepresentatives.lean`, `Level/Diamond.lean`, `WeightOne/`).

**The definition layer** is 20 pin definition modules / 2,752 raw lines. Ported
already: `ModularForm_HeckeOperator`, the eigenform half of
`FLTPrelim_Modularity`, `GaloisRep_Residual`, `EllipticCurve_FrobeniusTrace`,
`FLTPrelim_Ramification` (via `GaloisRep/Defs/{Residual,FrobeniusTrace,Ramification}.lean`).
New, and the natural homes: `EisensteinSeries_WeierstrassZeta`,
`CuspForm_Gamma1HeckeOperators`, `CuspForm_PrimitiveFormGamma1`,
`RepTheory_BrauerNesbitt_TraceCharZero`, `FrobeniusDensity_{PrimeSums,
DegOneAsymptotic,BadPrimes}`, `GaloisRep_FrobeniusPowerDense`, `TaylorWiles_Primes`,
`FieldTheory_RatAlgClosureGalois`, the Ihara trio (`IharaIota`, `IharaAmalgam`,
`IharaAmalgamMap`, `Gamma0Away`), `Deformations_MatrixRepresentation`.

## 4. Module layout

One directory per theory (playbook §3.2). The DS statements are their own theory,
but most of the shared mathematics belongs in existing homes:

| set | proposed home | why |
|---|---|---|
| S1 | `ModularForms/EisensteinSeries.lean` (extend) or `ModularForms/Eisenstein/` | weight-one Eisenstein series are ordinary modular forms; `EisensteinSeries.lean` exists |
| S2 | `ModularForms/` (`Hecke*`) and `ModularForms/WeightOne/` | the Hecke and $`\Gamma_1`$ vocabulary already lives here |
| S3 | `DeligneSerre/Lifting.lean` (new top-level dir) | the relèvement is weight-generic, the lifting is DS-specific |
| S4 | `Algebra/` (`FaithfulLatticeEigenvector`, `IntegralExtensionCharacters`) + `DeligneSerre/` | the trace/lattice and minimal-prime arguments are generic algebra |
| S5 | `Algebra/` or `GaloisRep/` | a finite-field representation-theory statement |
| S6 | `GaloisRep/` | finite-image representation conjugacy |
| S7 | `NumberTheory/FrobeniusDensity/` (new) | extends the existing `NumberTheory/{FrobeniusAtPlace,ValuationAtPlace}.lean` |
| assembly | `DeligneSerre/Assembly.lean` | the gluing statement |

`DeligneSerre/` is proposed as a top-level directory, matching `HeckeGalois/`.
Public names keep the pin's `DeligneSerre.*` namespace so the statement checker's
name map stays mechanical.

## 5. Build discipline and faithfulness

The rules of [porting-playbook.md](../porting-playbook.md) apply in full. The two
that matter most here:

- **Deduplicate before writing.** §3 lists 585 removable lines inside this slice
  and 28 statements already paid for. The WeightOne rectification (7,242 removable
  lines) is the cost of ignoring this; this cone overlaps the same material
  (`CuspForm`, `ModularForm`, `EisensteinSeries`).
- **Statements verbatim from the pin.** Every public target has a `Theorems/Thm_`
  wrapper; the port's declaration keeps the pin's name and statement and the
  checker verifies it. Proofs may be reorganized freely, but a name that appears
  in `port_name_clashes` must be reconciled first.
- **No `sorry`, `#print axioms` clean, bounded builds.** The port's convention is
  `[propext, Classical.choice, Quot.sound]` on every headline; a build past ~60 s
  is a blow-up to bisect, not wait on.

## 6. The deferred half

Everything outside the 54 nodes is deliberately behind an interface:

- **Group B (22 nodes)**, the irreducibility criterion and the image-order bound,
  behind the *ray-class analytic continuation* — the classical Hecke continuation
  of the nontrivial narrow ray-class $`L`$-function, without the functional
  equation (scout §3.1).
- **The density block** (the four `FrobeniusDensity.*`, the `NumberField.sub_mul_log_*`
  and `GaloisRep.sub_mul_log_*` lemmas), as a second classical interface.
- **The two gates** (`exists_tsum_norm`, `exists_finset_qCoeff_mem`) and the
  automorphic/adèlic subject beneath them — the next subject after this batch.
- **The converse cone** (local factors, Artin conductor, the Artin-$`L`$
  functional equation), which needs the full `M4aTorus.completedRayL_fe`.
