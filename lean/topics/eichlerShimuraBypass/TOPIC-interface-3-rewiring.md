# Topic: de-E-S-ifying interface 3 — verification plan

**Status: reconnaissance plan (2026-09-26). Phases 0–2 complete (2026-09-25);
Phases 3–6 not started.** This is a scouting / feasibility plan, not a port order.
It exists to decide — with pinned measurements — whether the single
analytic-Eichler–Shimura premise of FLT's interface 3 can be replaced by E-S-free
machinery, how much that saves, and whether the replacement is type-compatible
with the existing proof. If the verdict is positive, this file becomes the parent
of a Lean work order (see §7).

**Phase 0 result:** the plan is coherent and its Phase 0 gate **passes**. All
figures in §1/§2 reproduced against the pin (§3 closure 25 nodes / 21 `HeckeEis`,
interface 3 `HeckeEis` footprint 36 nodes / 13,293 `S_` lines); the analytic cone
is 12 nodes / 2,301 lines, all only reachable through the target lemma, and no
tail node depends on it. The contract and the partition tables are in
[../../../studies/eichler-shimura-bypass-scout.md](../../../studies/eichler-shimura-bypass-scout.md).

**Phase 1–2 result (scout §3, §5):** the degree-0 contract is E-S-free reachable
today — route B's `ModularCurve.Period.exists_parabolicRealization` composed with
`CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul` yields exactly
`IsEigensystemH1 N (1) (fun _ => LinearMap.id) S₀ lam` with **0 analytic nodes**
in their cones; interface 3's steps 2 and 3 are E-S-free, so the swap is a
justified local refactor rather than a one-token replacement. The blocker is
degree: the composition is weight-2 only. Expanding the blocker (scout §4)
shows the general mod-p weight reduction is E-S-free **modulo C′** — its 10
analytic nodes all enter through route A's proof of
`hasIntegralStructure_of_two_le`, which C′ replaces — and interfaces 5 and 6 are
C′-dissolved; the weight-$`(p+1)`$ → 2 descent already exists (interface 6's
θ-cycle, interface 5's maximal-ideal form). What is missing is only a form-side
$`[2, p+1] \to 2`$ descent, or a reduction landing at $`p+1`$. The
architecture-B stop condition is triggered but localized to that one brick.

**Thesis (scout note, header).** The endgame takes analytic-Eichler–Shimura
content through exactly two doors — Hecke-algebra finiteness/integrality, and the
mod-$`p`$ Hecke eigenvector / Galois attachment. Route C′ covers the first; the
$`k = 2`$ period map (Route B) plus the geometric E-S congruence and
$`S_2 \cong \Omega^1`$ already in the pin covers the second. This topic is the
feasibility test of that claim.

Provenance (read all three before acting):

- [../../../studies/flt-non-frey-segments.md](../../../studies/flt-non-frey-segments.md)
  §8 and §8.1 — the measured interface map: which E-S nodes the endgame actually
  consumes, the maximal interface family (four on the `HeckeEis` side, ten once
  the `ModPForms`/`PeriodPair` consumers are included), and the correction that C′
  alone saves
  only 4 nodes / 800 lines.
- [../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md)
  §4 (addendum) — the closure-accurate C′/route-A accounting.
- [../../../math/015-weight-two-hecke-periods.md](../../../math/015-weight-two-hecke-periods.md)
  — the weight-2 period/cocycle argument (route B), the mathematical picture of
  what the E-S map is and is not.

FLT is read at the pin `aa2d8b3`; measurements are from `tools/deps` (the
docs-site graph) plus source greps of the pin's `S_`/`Thm_` files. The port's
mathlib is `v4.34.0`.

## 1. Why this topic

The finding that motivates it (measured, `aa2d8b3`):

- Interface 3 is
  `GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le`.
  It attaches a 2-dimensional mod-$`p`$ Galois representation to a nonzero
  weight-$`k`$ Hecke eigenform $`f`$ with eigencharacter $`\chi`$: traces
  $`\mathrm{trace}\,\rho(\mathrm{Frob}_\ell) = \varphi(\chi(T_\ell))`$, determinant
  $`\ell^{k-1}`$, unramified outside $`Np`$. Its single endgame consumer is
  `GaloisRep.exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal`, and
  the chain runs through `GaloisRep.exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow`
  → the Katz/weight-raising step
  `WeierstrassCurve.exists_ideal_heckeAlgebra_two_or_succ_…_of_katz_…` →
  `WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNewform_…` → modularity
  lifting.
- Interface 3's analytic-E-S footprint is 46 E-S-ish nodes / 23,363 raw `S_`
  lines (36 `HeckeEis` / 13,293 if `PeriodPair` is excluded), but it is
  concentrated in **one lemma**, see §2. Everything downstream — the weight
  reduction $`n \to 0`$ and the construction of the Galois representation from a
  weight-2 eigensystem — is E-S-free (4 and 1 bookkeeping `HeckeEis` nodes
  respectively; see §3).

**Two different "600-node" numbers, which must not be conflated.** Route A's
`hasIntegralStructure_of_two_le` cone is **657 nodes / 263,720 lines**, but it is
mostly *geometry*, not E-S:

| namespace in route A's cone | nodes | lines |
|---|---:|---:|
| `ModularCurve` | 266 | 67,287 |
| `AlgebraicCurve` | 162 | 69,010 |
| `WeierstrassCurve` | 100 | 91,063 |
| `HeckeEis` | 54 | 12,683 |
| `PeriodPair` | 9 | 9,836 |
| `CuspForm` | 8 | 1,745 |
| `ModularForm` | 11 | 1,034 |
| other | 47 | ~11,062 |

The ~528 modular-curve/elliptic nodes are needed by the endgame regardless (the
`JZero`/Tate Galois route, Riemann–Roch, differentials, patching), which is why
replacing route A's *proof* by C′ removes only **4 nodes / 800 lines**. The
E-S-ish package in the endgame is the union of three namespaces:

| namespace | endgame nodes | lines |
|---|---:|---:|
| `HeckeEis` | 130 | 44,516 |
| `ModPForms` | 65 | 15,084 |
| `PeriodPair` | 18 | 12,265 |
| **E-S-ish total** | **213** | **71,865** |

**The surface is ten interfaces, not four.** Maximally-consumed exits of the
E-S-ish package into the rest of the endgame (per-interface counts overlap; the
union is 207 of the 213 nodes / 70,558 of 71,865 lines):

| # | interface | E-S-ish nodes | lines |
|---|---|---:|---:|
| 1 | `WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ` | 65 | 21,872 |
| 2 | `WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_…` | 39 | 21,157 |
| 3 | `GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le` | 46 | 23,363 |
| 4 | `WeierstrassCurve.exists_ideal_heckeAlgebra_three_weight_le_four_pow_mul_apOfModel_…` | 89 | 34,062 |
| 5 | `CuspForm.heckeAlgebra.exists_isMaximal_two_ringHom_of_succ_…` | 107 | 31,660 |
| 6 | `CuspForm.heckeAlgebra.thetaCycle_exists_ringHom_mul_two_apply_eq_…` | 93 | 28,401 |
| 7 | `CuspForm.exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two` | 16 | 10,768 |
| 8 | `LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime` | 22 | 12,609 |
| 9 | `ModularCurve.exists_eq_smul_of_diffQExpBar_eq_…_of_kaehlerH0_…` | 1 | 26 |
| 10 | `WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul` | 6 | 4,265 |

**Consequence to be tested.** If all ten interfaces are re-proved E-S-free, the
E-S-ish package leaves the endgame — a target of **213 nodes / 71,865 lines**.
The fallback is the retain-interface-3-only variant: drop E-S for the other nine,
keeping interface 3's 46 / 23,363, which saves **161 nodes / 47,195 lines**.
Either way the prize is far smaller than route A's 657-node cone, because ~528 of
those nodes are geometry that the endgame needs anyway. The full ten-interface
figure is also the correct answer to "is it more than just the interface?": yes —
four times the four-interface estimate, but still not the 657-node cone. The scout
note [§6](../../studies/eichler-shimura-bypass-scout.md) records the full payout:
the 213 / 71,865 package measured against the 29,488-node / 11,926,355-line FLT
proof cone, the three nested targets, the replacement ingredients already inside
the endgame, the two conditions on "all interfaces" (higher weight / Katz forms,
and the twelve further direct citers beyond the ten), and a reproduction script.

**The weight-2 E-S is already in the pin.** `Definitions/Def_ModularCurve_PeriodMap.lean`
defines `ModularCurve.Period.IsEquivariantPrimitive` / `period` / `periodHom` /
`parabolicHoms` (and interface 3's tail already imports it), and route B's blob
supplies the substantive weight-2 theory — primitive existence, period
injectivity, Hecke equivariance, the integral cocycle lattice `addChars ℤ Γ₀ ℤ`,
its spanning and the Hecke triple algebra — self-contained at graph closure 1.
So the $`n = 0`$ (trivial-coefficient) instance of interface 3's analytic step can
come from what is already written, not from the `HeckeEis` package. §3 Candidate 0
is this bridge and is the first thing Phase 1 tests; the open question it leaves
is the form-side reduction from weight $`k`$ to weight 2.

## 2. The contract: exactly what must be replaced

The analytic content of interface 3 is the single lemma

```lean
HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ) (n : ℕ) (k : ℤ)
    (hk : (n : ℤ) + 2 = k)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0)
    (a : ℕ → integralClosure ℤ ℂ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      ModularForm.heckeTLin k hℓ hℓN f = ((a ℓ : integralClosure ℤ ℂ) : ℂ) • f)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) :
    HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S (fun ℓ => φ (a ℓ))
```

(`S_` file 523 lines; closure 25 nodes, 21 of them `HeckeEis`). Its mathematical
content: realize the mod-$`p`$ reduction of the eigenform as a **nonzero Hecke
eigenvector in the group cohomology**
$`H^1(\Gamma_0(N), \mathrm{Sym}^n)`$ (`HeckeEis.coeffH1 (binaryFormRepSL κ n)`),
with the Hecke action `binaryFormAlphaAdj`. The analytic Eichler integral is the
*only* reason the proof needs the period map; the Hecke-eigenvector property is
what the downstream steps consume.

**Deliverable of Phase 0:** a partition of interface 3's 36 `HeckeEis` nodes into
"reachable only through this lemma" and "shared with the E-S-free tail", and a
table of the 21 nodes in the lemma's own cone with the analytic fact each uses.

## 3. The crux: a carrier bridge

The replacement must produce a term of type `HeckeEis.IsEigensystemH1 N
((binaryFormRepSL κ n).comp Γ₀.subtype) (binaryFormAlphaAdj κ n) S lam` — i.e. a
nonzero element of `HeckeEis.coeffH1` for the **binary-form coefficient system**.
The E-S-free candidates land in *different* carriers:

| candidate | carrier it produces | closure | `HeckeEis` nodes |
|---|---|---|---|
| `CohCarrier.*` eigensystem lemmas | `CohCarrier.H1` (Γ_H carrier) | 2–594 | 0–2 |
| `ModularCurve.frobeniusQuadratic_JZero` / `W54.jZeroPPowTorsion_frobeniusQuadratic` | JZero p-power torsion / Tate module | 995 / 1,035 | 1 / 1 |
| `ModularCurve.exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq` | regular differentials, weight 2 | 882 | 0 |

So the plan must answer: *can a nonzero Hecke eigenvector in
$`H^1(\Gamma_0, \mathrm{Sym}^n)`$ be produced without the Eichler integral?* Two
architectures:

- **Architecture A — replace the lemma at degree $`n`$.** Needs a geometric model
  of $`H^1`$ with $`\mathrm{Sym}^n`$ coefficients (Kuga–Sato / de Rham comparison).
  Heaviest; likely requires theory not currently in the pin/port.
- **Architecture B — move the weight reduction before the lemma.** Reduce the
  mod-$`p`$ eigenform from weight $`k`$ to weight 2 on the *form* side (Katz forms
  / the existing twist machinery), then produce only the $`n = 0`$ eigensystem
  geometrically from the JZero/Frobenius route plus the
  `intLattice ≅ regularDifferentials` comparison. Interface 3's E-S-free tail then
  applies unchanged. **This is the leading hypothesis.**

**Carrier constraint (the main thing; added after the Phase 0 review).** The
replacement must not carry a cohomology argument beyond the *tame implicit type*
of route B's blob — `addChars`, i.e. `Hom` at trivial coefficients, with every
1-coboundary zero and no quotient
([../../studies/eichler-shimura-bypass-scout.md](../../studies/eichler-shimura-bypass-scout.md)
§0, [../../../math/015-weight-two-hecke-periods.md](../../../math/015-weight-two-hecke-periods.md)
§3). Concretely, a candidate whose cone builds a genuine
$`H^1(\Gamma_0, \mathrm{Sym}^n)`$ — Kuga–Sato, de Rham comparison, or an
identification of `CohCarrier.H1` with `coeffH1 (binaryFormRepSL κ n)` at
$`n > 0`$ — is outside the constraint and needs a separate justification before
it counts. Architecture B / Candidate 0 is compatible by construction: at
$`n = 0`$ the coefficients are trivial, so `coeffCoboundaries 1 = ⊥` and
`coeffH1 1` *is* route B's type; the bridge is thin and adds no cohomology. This
is a Phase 1 filter and a §5 stop condition.

**Candidate 0 — the route B bridge (leading).** The weight-2
(trivial-coefficient) E-S is already in the pin, twice:

- **definitions**: `ModularCurve.Period.IsEquivariantPrimitive`, `period`,
  `periodHom`, `IsParabolicHom`, `parabolicHoms` live in
  `Definitions/Def_ModularCurve_PeriodMap.lean`, which interface 3's own tail
  (step 3, `exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom`) already
  imports;
- **substance**: primitive existence, period injectivity, Hecke equivariance, the
  integral cocycle lattice `addChars ℤ Γ₀ ℤ`, its spanning
  (`span_range_ofIntChars`) and the Hecke triple algebra are proved
  self-contained in route B's blob
  (`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`, 4,308 lines, graph closure 1).

At degree $`n = 0`$ the target of step 1 degenerates to a nonzero Hecke
eigenvector in `coeffH1 (1 : Representation κ Γ₀ κ)`. Since
`coeffH1 1 = coeffCocycles 1 ⧸ 0 = Hom(Γ₀, κ) = addChars κ Γ₀ κ`, that is exactly
the shape route B produces, so the $`n = 0`$ instance of step 1 should come from
route B plus a **thin carrier bridge**
`addChars κ Γ₀ κ ≃ coeffH1 (1 : Representation κ Γ₀ κ)` (a quotient by the zero
coboundary submodule) — not from the `HeckeEis` package.

What route B does **not** give is degree $`n \gt 0`$: its primitive exists only for
weight 2. So the bridge closes interface 3 iff the transfer from weight $`k`$ to
weight 2 can be made *before* step 1 — a **form-side weight reduction** (Katz
forms / the θ-cycle machinery). The pin's step 2
(`exists_isEigensystemH1_one_dvd_mul_sq_…`) is E-S-free but consumes step 1's
degree-$`n`$ output; the question is whether an E-S-free form-side analogue
exists.

**Obligations for Candidate 0.** (a) the carrier bridge above, or a direct
`IsEigensystemH1` construction; (b) the form-side weight reduction $`k \to 2`$,
E-S-free; (c) the mod-$`p`$ eigenvector from route B's ℂ periods plus the integral
cocycle lattice — the integrality step step 1 performs. Route B's
`span_range_ofIntChars` says the integral cocycles ℂ-span, not that a specific
period class is integral; that gap is the same subtlety as §2.

**Reframing.** If Candidate 0 works, the topic is really
**de-`HeckeEis`-ification**: the analytic E-S is not removed, it is replaced by
route B's weight-2 instance, which is already written and dependency-free. That is
a much better outcome than a new general-weight construction, and it is the first
thing Phase 1 should test.

Architecture B is only viable if the form-side weight reduction is itself
E-S-free. The pin's step 2
(`HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL`)
does the reduction on the *cohomology* side (level $`M \mid Np^2`$, trivial
coefficients, eigenvalues twisted by $`\ell^{n/2}`$). The question is whether the
same reduction exists on the form side in the `KatzModularForm.*` cluster
(19 nodes) — Phase 1.

## 4. Phase plan

Each phase states tasks, artifact, and a gate. Phases 0–4 are scouting (no Lean
build); Phase 5 is the optional spike.

### Phase 0 — Freeze the contract and the E-S partition (½–1 round)

1. Read the pin's
   `P2M/Sol/S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.lean`
   (523 lines) whole; list every analytic input (Eichler-integral existence,
   chain rule/boundedness, binary-form Hecke correspondence, cocycle identities)
   and mark which are only needed to build the *period* class.
2. Pin the exact types: `HeckeEis.IsEigensystemH1`, `IsCoeffHeckeOnH1`,
   `binaryFormRepSL`, `binaryFormAlphaAdj`, `coeffH1`, `coeffCocycles`.
3. Produce the 36-node partition of §2 and the 21-node fact table.

Artifact: §"Contract" table in the scout note
([../../../studies/eichler-shimura-bypass-scout.md](../../../studies/eichler-shimura-bypass-scout.md)
§1–§2).
Gate: if more than this one lemma is analytic, re-scope the topic before Phase 1.

**Done 2026-09-25 — gate passes.** The 36-node partition is 14 reachable only
through the lemma / 22 reachable without it; the 21-node cone splits into 9
analytic nodes (2,137 lines), 3 E-S-packaging nodes (164 lines), 8 E-S-free
algebra nodes (2,281 lines), plus the 523-line lemma. No tail node's closure
meets the analytic set, so the analytic construction is confined to the target
lemma. Refinement: two of the 14 only-through nodes
(`span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top`,
`exists_injective_baseChange_coeffH1_binaryFormRepSL`, 781 lines) are E-S-free
algebra, so Phase 2's circularity set is the 12-node / 2,301-line analytic cone,
not all 14.

### Phase 1 — Candidate constructions, stated as theorems (2–3 rounds)

For each candidate, write the Lean-style signature it can supply, grep its cone
for `HeckeEis`, and check the carrier match:

1. **Route B bridge (Candidate 0, leading).** `ModularCurve.Period.periodHom`
   (`Definitions/Def_ModularCurve_PeriodMap.lean`) plus route B's
   `exists_equivariantPrimitive_gamma0`, `periodHom_injective`,
   `periodHom_hecke`, `addChars ℤ Γ₀ ℤ`, `span_range_ofIntChars` and the triple
   algebra. Produce the $`n = 0`$ `IsEigensystemH1` directly, via the carrier
   bridge `addChars κ Γ₀ κ ≃ coeffH1 (1 : Representation κ Γ₀ κ)`. This is the
   candidate that uses what the pin already has.
2. **CohCarrier route.** `CohCarrier.heckeT_top_apply_eq_heckeOperatorHom`,
   `CohCarrier.exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int`,
   `CohCarrier.mem_span_int_of_forall_isOfFinOrder_apply_eq_zero`,
   `CohCarrier.exists_ringHom_heckeAlgebra_apply_smul_eq_heckeT_of_mem_parabolicHoms`.
   Does it give a nonzero Hecke eigenvector from an eigenform/eigencharacter
   without the Eichler integral? Is `CohCarrier.H1` identifiable with
   `coeffH1 (binaryFormRepSL κ n)`?
3. **JZero/Frobenius route (architecture B, $`n = 0`$).**
   `ModularCurve.frobeniusQuadratic_JZero`, `W54.jZeroPPowTorsion_frobeniusQuadratic`,
   `CuspForm.IsNewform.exists_eigenPlane_tateModule_jZero`, composed with
   `ModularCurve.exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq`.
4. **Katz-forms route (architecture B, form side).** `KatzModularForm.*`,
   `ModularCurve.KatzGamma0Form`/`KatzLevelPForm`. Locate the weight-reduction
   statement on forms (the analogue of step 2) and check it is E-S-free. This is
   the gate for Candidate 0 at degree $`n \gt 0`$.
5. **Abstract route.** Can `ModularCurve.EichlerShimuraData` /
   `FrobeniusQuadratic` / `SpecialFibreRelation` be instantiated E-S-free and fed
   to `IsEigensystemH1`?

Artifact: candidate matrix (theorem, hypotheses, carrier, `HeckeEis` count,
contract compatibility).
Gate: at least one candidate must plausibly produce the *exact* `coeffH1`
eigensystem (or a refactor of interface 3 must be justified).

**Done 2026-09-25 — gate passes conditionally; scout §3.** Candidates 0 and 1
*compose* to the exact degree-0 contract E-S-free: route B's
`ModularCurve.Period.exists_parabolicRealization` (31 nodes / 7,166 lines, 0
`HeckeEis`, 0 analytic) gives a nonzero parabolic Hecke eigenvector in
`parabolicHoms k Γ₀ k`, and `CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul`
(3 / 307 lines, 0 analytic) turns it into exactly
`IsEigensystemH1 N (1 : Representation κ Γ₀ κ) (fun _ => LinearMap.id) S₀ lam`.
The carrier/Hecke match is already formalized for the harder projLine analogue
(`HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` and
`HeckeEis.coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom`).
Candidates 2 (JZero/Frobenius) and 4 (abstract `EichlerShimuraData`) are E-S-free
but have no glue to `coeffH1` — and the abstract datum is a dead interface with
zero consumers. Candidate 3 (Katz / mod-p form side) is the blocker, but the
expanded analysis (scout §4) splits it: the general reduction
(`exists_weight_le_succ_…`) and interfaces 5/6 are E-S-free modulo C′, while the
intrinsic core `ModPForms.exists_isEigensystemH1_…_of_isModPEigen` (the
general-weight $`\mathrm{Sym}^{k-2}`$ period map, 12/12 analytic) is not. So the
gate passes with the refactor, and the open obligation narrows to a form-side
$`[2, p+1] \to 2`$ descent.

### Phase 2 — Statement compatibility and circularity (1–2 rounds)

- State the replacement with the same conclusion as the analytic lemma so
  interface 3's proof is a one-token swap; if that fails, plan the minimal
  refactor (interface 3 already factors as transfer → weight reduction →
  construction).
- Check hypotheses are derivable from interface 3's inputs (a weight-$`k`$
  eigenform/eigencharacter plus $`\varphi`$).
- Circularity: does the candidate cite any node in the 36-node interface-3 E-S
  cone, or `hasIntegralStructure`/`moduleFinite_heckeAlgebra` (acceptable — C′
  supplies those)? The candidate cones in §3 have 0–2 `HeckeEis` nodes, none
  analytic.

**Done 2026-09-25 — one-token swap fails; minimal refactor is at step 1+2; scout §5.** Interface 3 concludes the degree-$`n`$ eigensystem; the 0∘1 composition is
degree-0. Steps 2 and 3 are E-S-free (cones 18 / 9,854 and 1,350 / 566,832, 0
analytic nodes), so the refactor is: drop step 1 and step 2, insert [form-side
$`k \to 2`$ reduction] then route B then
`CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul` (degree-0 at level `N`), keep
`GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom` and the
existing cyclotomic twist. Hypotheses: derivable for $`k = 2`$ (outside interface
3's stated range); for $`k \ge 3`$ the reduction is the gap. Circularity:
candidates 0/1/2/4 have 0 analytic nodes in cone; candidate 3 has 10–12 and is
circular as written.

### Phase 3 — Measured gain (½ round)

Recompute with `tools/deps` (the metric is the sum of `S_`-file lines over the
closure):

- interface-3 cone with and without the 21-node analytic cone;
- the retain-interface-3-only saving (161 E-S-ish nodes / 47,195 lines) and the
  all-ten target (213 E-S-ish nodes / 71,865 lines);
- the replacement's own marginal cone (is it already inside the endgame's
  required cone, i.e. zero marginal lines as with C′?).

Reproduction skeleton:

```bash
cd tools/deps && python3 - <<'PY'
import sys, os; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); I = d.index
def cl(i):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j); st.extend(d.cites(j))
    return seen
def he(C): return {i for i in C if d.qual(i).startswith('HeckeEis.')}
def lines(S):
    root = os.path.expanduser('~/proj/fermats-last-theorem')
    def lc(i):
        stem = d.stem_of.get(i, '')
        for sub in ('P2M/Sol', 'Theorems'):
            for pre in ('S_', 'Thm_'):
                p = os.path.join(root, sub, f'{pre}{stem}.lean')
                if os.path.exists(p):
                    return sum(1 for _ in open(p, encoding='utf-8', errors='replace'))
        return 0
    return sum(lc(i) for i in S)
lem = cl(I['HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul'])
print('lemma cone:', len(he(lem)), 'HeckeEis nodes /', lines(he(lem)), 'lines')
PY
```

### Phase 4 — Novelty and literature (1 round)

- Search the formalization literature (mathlib modular forms / Hecke / Galois
  representations; other FLT formalizations) and the classical literature
  (Deligne, Katz, Hida, Gross) for whether "attach the mod-$`p`$ Galois
  representation from the $`q`$-expansion lattice plus the geometric E-S
  congruence, without the analytic period map" is known mathematics or only a
  new *formalization* strategy.
- Write the novelty claim precisely. If the replacement is standard mathematics,
  the contribution is architectural (a formalization shortcut); say so.

### Phase 5 — Feasibility spike (2–5 rounds, conditional)

In the port's `FLTForHuman/ModularForms/WeightOne/` (where builds are feasible),
attempt the smallest instance: architecture B at $`n = 0`$, i.e. construct a
nonzero `IsEigensystemH1` on the trivial-coefficient carrier from the geometric
route, using the ported C′ lattice (`intLattice`, `HasIntegralStructure`) and
mathlib. If the full target is too heavy, do a paper proof plus a `sorry`-free
statement skeleton and a compile check of interface 3 with the replacement
assumed.

Gate: does the candidate carrier's Hecke action match `IsCoeffHeckeOnH1`? If not,
the carrier bridge is the whole problem and architecture A may be unavoidable.

Build discipline (port side, from
[../../porting-playbook.md](../../porting-playbook.md) §3–§5 and
[../hecke/TOPIC-route-c-prime-integral-structure.md](../hecke/TOPIC-route-c-prime-integral-structure.md)
header): bound every build (`timeout 60 lake env lean <file>`,
`timeout 180 lake build <module>`), quarantine a blow-up immediately, never raise
`maxHeartbeats`.

### Phase 6 — Verdict and record

- Decision matrix: **feasible / conditionally feasible (state X) / blocked (state
  the concrete blocker)**.
- Write `studies/eichler-shimura-bypass-scout.md` (pinned, measured) and cross-link
  it from [../../../studies/flt-non-frey-segments.md](../../../studies/flt-non-frey-segments.md)
  §8.1.
- If positive, draft the Lean work order as
  `TOPIC-interface-3-rewiring-port.md` in this directory: module split, tier
  order, obligations, checker/consumer plan, stop conditions.

## 5. Budget, stop conditions

**Budget: 4–6 rounds** for Phases 0–4 (scouting only), plus **2–5 rounds** for
Phase 5 if the gate is passed.

**Stop and report on:**

- more than the one analytic lemma in interface 3's E-S cone (Phase 0 gate);
- the carrier bridge requiring the E-S comparison itself (architecture A), which
  needs unported general-weight theory;
- a candidate that must formalize a genuine $`H^1(\Gamma_0, \mathrm{Sym}^n)`$
  (Kuga–Sato, de Rham comparison, or a `CohCarrier.H1` identification at
  $`n > 0`$) — i.e. cohomology beyond route B's `addChars`/`Hom` type (§3);
- no form-side, E-S-free weight reduction existing (architecture B fails) —
  **TRIGGERED, LOCALIZED (Phase 1 + expansion, scout §4):** the general mod-p
  reduction (`ModPForms.exists_weight_le_succ_…`) is E-S-free modulo C′ (its 10
  analytic nodes all enter via `hasIntegralStructure_of_two_le`), interfaces 5/6
  are C′-dissolved, and the weight-$`(p+1)`$ → 2 descent exists; the missing
  brick is a form-side $`[2, p+1] \to 2`$ descent (or a reduction landing at
  $`p+1`$). The intrinsic core
  `ModPForms.exists_isEigensystemH1_…_of_isModPEigen` remains analytic;
- a candidate citing any node of the 21-node analytic cone (circularity) —
  **observed for candidate 3** (Katz / mod-p reduction, 10–12 nodes); candidates
  0/1/2/4 are clean;
- a measured saving materially below the 161-node / 47,195-line figure (or, for
  the full ten-interface target, the 213-node / 71,865-line figure).

## 6. Reporting back

1. the 36-node partition and the 21-node analytic fact table (Phase 0);
2. the candidate matrix with carriers and `HeckeEis` counts (Phase 1);
3. the replacement signature(s) and the compatibility verdict (Phase 2);
4. the measured saving with the reproduction command (Phase 3);
5. the novelty assessment, separating known mathematics from formalization
   novelty (Phase 4);
6. the spike outcome and the carrier-action match (Phase 5);
7. the decision matrix and the concrete blocker, if any (Phase 6).

## 7. Definition of done (for the scouting topic)

- [x] contract frozen (§2) and the two-partition table produced (scout §1–§2);
- [x] candidate matrix with `HeckeEis` counts for every candidate (scout §3);
- [x] at least one replacement signature type-compatible with interface 3, or a
      justified refactor (0∘1 gives the exact degree-0 contract; refactor in
      scout §5.1);
- [x] circularity check done against the 36-node cone (scout §5.3);
- [ ] measured saving reproduced with the command above;
- [ ] novelty/literature assessment written;
- [x] `studies/eichler-shimura-bypass-scout.md` written and cross-linked (Phase 0);
- [ ] verdict recorded; if positive, the port work order drafted as
      `TOPIC-interface-3-rewiring-port.md`.

## 8. Pointers

- Phase 0 contract and E-S partition:
  [../../../studies/eichler-shimura-bypass-scout.md](../../../studies/eichler-shimura-bypass-scout.md)
  §1–§2 and reproduction §7.
- Interface map and corrections:
  [../../../studies/flt-non-frey-segments.md](../../../studies/flt-non-frey-segments.md)
  §8, §8.1.
- C′/route-A closure-accurate accounting:
  [../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md)
  §4 addendum; [../../../studies/hecke-finiteness-coverage.md](../../../studies/hecke-finiteness-coverage.md)
  §7.3.
- Weight-2 period/cocycle mathematics (route B):
  [../../../math/015-weight-two-hecke-periods.md](../../../math/015-weight-two-hecke-periods.md).
- Prior finiteness scoping:
  [../hecke/TOPIC-t10-finite-algebra.md](../hecke/TOPIC-t10-finite-algebra.md) §7.
- Port method: [../../porting-playbook.md](../../porting-playbook.md).
- The lemma to replace:
  [`S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.lean).
- Interface 3:
  [`Thm_GaloisRep_exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_GaloisRep_exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le.lean).
