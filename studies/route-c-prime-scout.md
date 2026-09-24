# Route C′ scouted — the integral-basis shortcut for `HasIntegralStructure`

**Status: HOLDS** (mathematically; the trace lemma is not yet formalized). The
shortcut is real, and its measured cone is a subset of an endgame branch FLT needs
anyway. Route A's Eichler–Shimura tower is avoidable for
`hasIntegralStructure_of_two_le`.

Measured 2026-09-24 against the pin `aa2d8b3` with `tools/deps` (graph closure)
and the `S_`-file line metric (the same metric that reproduces route A's
263,720). Companion: [hecke-finiteness-coverage.md](hecke-finiteness-coverage.md)
§4–§5, §7.3, §9 Q1; the brief it corrects is
[../lean/topics/hecke/TOPIC-t10-finite-algebra.md](../lean/topics/hecke/TOPIC-t10-finite-algebra.md)
§7.

## 1. The brief's ingredient does not exist under that name

The T10 brief and the coverage study both write
`exists_basis_gamma1_qCoeff_mem_range_intCast`. There is no such declaration in
the pin. The name conflates two real ones:

| real declaration | statement |
|---|---|
| `CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast` (`S_` 19 lines) | a `ℂ`-basis of $`S_2(\Gamma_1(M))`$ whose elements have integral $`q`$-coefficients |
| `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` (`S_` 183 lines) | a `ℂ`-basis of $`S_k(\Gamma_1(N))`$ whose **every $`\Gamma_0(N)`$-slash** has integral $`q`$-coefficients, for arbitrary $`k`$ |

The second is the working ingredient; it is the first's general-weight,
slash-closed parent (the first is its weight-2, $`\gamma = 1`$ specialisation).
The slash condition is not decoration — it is exactly what makes the missing step
work, and the general-$`k`$ form means there is no weight-raising problem either.

## 2. The missing step is one trace lemma — and Sturm is not needed

Let $`\Gamma_1(N) \trianglelefteq \Gamma_0(N)`$ (mathlib:
`Gamma1' N = (Gamma0Map N).ker`), and suppose
$`b_1, \dots, b_n`$ is a $`\mathbb{C}`$-basis of $`S_k(\Gamma_1(N))`$ such that
every $`q`$-coefficient of every $`b_i \mid_k \gamma`$ ($`\gamma \in \Gamma_0(N)`$)
is an integer. Choose coset representatives $`\gamma_1, \dots, \gamma_r`$ and set

```text
P_i = Σ_j  b_i ∣[k] γ_j          (i = 1, …, n).
```

- **Bundled form.** Each $`b_i \mid_k \gamma_j`$ is a cusp form for
  $`\Gamma_1(N)`$ (normality of $`\Gamma_1`$), and $`P_i`$ is fixed by every
  $`\gamma \in \Gamma_0(N)`$ (right action permutes the cosets), so
  $`P_i \in S_k(\Gamma_0(N))`$.
- **Integral.** $`P_i`$ is a finite sum of functions with integral
  $`q`$-coefficients, so $`q`$-coefficients of $`P_i`$ are integers; hence
  $`P_i \in \mathtt{intLattice}\ N\ k`$.
- **Spanning.** The trace $`T(v) = \sum_j v \mid_k \gamma_j`$ is $`\mathbb{C}`$-linear
  and maps $`S_k(\Gamma_1(N))`$ into $`S_k(\Gamma_0(N))`$; for
  $`w \in S_k(\Gamma_0(N))`$ one has $`T(w) = r \cdot w`$ with
  $`r = [\Gamma_0(N) : \Gamma_1(N)] \neq 0`$. So $`T`$ is onto and
  $`\{P_i\} = \{T(b_i)\}`$ spans $`S_k(\Gamma_0(N))`$.

Therefore $`\mathrm{span}_{\mathbb{C}}(\mathtt{intLattice}\ N\ k) = \top`$,
i.e. `CuspForm.HasIntegralStructure N k` — for **all** $`k`$, not only
$`k \ge 2`$. The Sturm bound never appears: the trace argument certifies spanning
directly, so the "`+` small Sturm bound" in the brief is unnecessary (and the
`~287`-node figure attached to it is not a measurement of anything).

FLT does not contain this step. `CuspForm.hasIntegralStructure_of_two_le` is
proved by route A and does not mention `exists_basis_gamma1*`,
`HasIntegralBasis`, `qIntegral` or `sturm_bound` (grep counts 0); the
`exists_basis_gamma1*` family feeds the mod-3/weight-one branch instead.

## 3. Measurements

Node count = graph closure; lines = sum of the `S_` files of the closure nodes
(the metric of [hecke-finiteness-coverage.md](hecke-finiteness-coverage.md) §1;
it reproduces route A's 263,720 exactly).

| declaration | nodes | raw `S_` lines |
|---|---|---|
| `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` | **53** | **33,719** |
| `CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast` | 54 | 33,738 |
| `CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` | 42 | 24,371 |
| `CuspForm.hasIntegralStructure_of_two_le` (route A) | **657** | **263,720** |
| `CuspForm.hasIntegralStructure_two` (route A, `k = 2`) | 593 | 247,788 |

Standalone, C′ is $`\approx 7.8\times`$ cheaper in raw lines and
$`12\times`$ cheaper in nodes than route A.

The cone is dominated by the weight-one/fricke package, not by Hecke theory:
`EisensteinWeightOne.e1Chi3IsModular` (3,816 lines), the nine `WLight.*`
frickeFunction/`levelN` nodes (≈9k lines together),
`CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top` (1,390),
`ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`
(1,362). Of the 53 nodes only five are already in the port:
`eq_zero_of_lt_order_qExpansion_of_isArithmetic`,
`exists_nat_mem_strictPeriods_conj`,
`levelOne_eq_zero_of_lt_order_qExpansion`,
`qExpansion_prod`,
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`.

## 4. The decisive overlap: the cone is already inside an endgame branch

`FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd` has closure **7,222**
and is itself inside `fermatLastTheorem`'s closure. Every one of the 53 C′ nodes
lies in that branch's closure:

```text
C′ cone ∩ closure(No2BridgeWiring) = 53 / 53
C′ cone \ closure(No2BridgeWiring) = 0
```

So if the port does the weight-one/`No2BridgeWiring` branch — which the endgame
requires — the C′ cone is ported as part of that work, and the route-specific
addition is only the trace lemma. **The lemma is additive: it replaces none of the
53 declarations**, all of which are load-bearing in the branch.

`CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` is a direct premise
of that branch (via `CuspForm.IsPrimitiveForm.*` and `DeligneSerre.*`), not a
coincidence of closure. Route A behaves differently: of its 657 nodes,
584 / 246,483 lines are also in the `No2BridgeWiring` closure, and only
73 / 17,237 lines are its own — the `HeckeEis.*` Eichler–Shimura comparison
(`eichlerShimuraMap_heckeTLin`, `range_eichlerShimuraMap_inf_range_conj_eq_bot`,
…) plus the generic criterion
`hasIntegralStructure_of_moduleFinite_of_linearIndependent`. So:

| scenario | route A marginal | C′ marginal (cone + lemma) |
|---|---|---|
| weight-one branch ported | 73 nodes / 17,237 lines | **trace lemma** (cone already ported) |
| weight-one branch not ported | 657 nodes / 263,720 lines | 53 nodes / 33,719 lines **+ lemma** |

C′ is cheaper in both, by construction in the first and $`\approx 8\times`$ in the
second. The trace lemma never substitutes for the cone.

## 4b. The path is in the endgame, and the cone is not throwaway

Unlike route B — a parallel duplicate of a statement route A already implies,
written and then deleted — the C′ declarations sit on the critical path to
`FLT.fermatLastTheorem`, through the No. 2 bridge and weight-one branch. BFS over
the premise graph gives a shortest chain of 15 steps:

```text
FLT.fermatLastTheorem
→ FreyPackage.fermatLastTheoremFor_of_five_le
→ FreyPackage.no_frey_package
→ FreyPackage.frey_isModular
→ WeierstrassCurve.modularity_of_semistableModel
→ WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
→ FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd
→ LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_not_nine_dvd_not_cube_dvd_of_natCard_inertia_eq_two_of_coprime
→ … (LanglandsTunnell cusp-pair chain) …
→ DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
→ DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
→ DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
→ CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast
```

The basis theorem feeds `frey_isModular` through the Deligne–Serre primitive-form
rationality used by the weight-one newform existence, independently of the
integral-structure goal. Its other consumers (`CuspForm.IsPrimitiveForm.*`,
`ModularCurve.XOneP.*`, `CuspForm.IsEigenformWith.fg_adjoin_qCoeff`) are likewise
on the modularity side; one of them,
`CuspForm.IsPrimitiveForm.ringHom_rationalHeckeOne_mul_eq_of_dvd_of_not_sq_dvd_of_dvd_conductor_of_dvd_level`,
is a *second*, independent endgame path (19 premise steps from
`fermatLastTheorem`, through the Taylor–Wiles/`HeckeRing` branch). The cone is
therefore not merely "in the closure": it is a multi-path prerequisite of the
endgame:

- the cone is **in the endgame** (closure of `fermatLastTheorem`; shortest chain
  15, `explore`-reported depth 16, 52 theorems below, cited by 8);
- the cone is **not a duplicate** of anything route A proves — it is shared with
  the endgame's weight-one modularity work, so it survives whatever integral-
  structure route is chosen;
- the **trace lemma is the only route-specific addition**, and the only piece that
  would be superseded if route A were *also* ported (which is exactly what C′
  avoids paying for).

## 5. Verdict and consequences

1. **C′ holds.** `CuspForm.HasIntegralStructure N k` follows from
   `exists_basis_gamma1_qCoeff_slash_mem_range_intCast` + the trace lemma, with no
   Eichler–Shimura, no `ModPForms`, no `HeckeEis`, and no Sturm bound. Route A is
   not needed for this target.
2. **The missing artifact is small and ours.** The trace lemma is the only piece
   not already in FLT; it is subgroup-quotient and `SlashAction` bookkeeping
   (`Gamma1_in_Gamma0`, `Gamma1' = ker Gamma0Map` for normality, finite-index
   coset sums, and the `CuspForm`/`intLattice` membership).
3. **T10's "χ₋₃ route was wrong" needs a qualifier.** The χ₋₃/weight-one
   machinery (`EisensteinWeightOne.e1Chi3IsModular`, the `WLight` fricke
   package) is *not* on FLT's route A, but it **is** the analytic content of the
   C′ ingredient. The ported `Defs/EisensteinChiNegThree.lean` and
   `Defs/IntegralLattice.lean` are therefore prerequisites of C′, not of the
   mod-3 machinery alone.
4. **The study's C′ line should read 53 nodes, not ~287.** The `~287` figure is
   unsupported; the "`+` `sturm_bound_of_isArithmetic`" is a red herring.
5. **Caveat on the line metric.** The `S_`-file sum over-counts: a closure node's
   file may contain other declarations, and 33,719 is not 33,719 lines of new
   proof. The node counts and the overlap are the robust measurements; the raw
   line number is comparable only against route A's identically-computed 263,720.
6. **The cone is endgame and not throwaway.** It is in `fermatLastTheorem`'s
   closure (shortest premise chain 15; §4b) and shared with the endgame's
   weight-one modularity work, so no future integral-structure choice deletes it.
   The trace lemma is the route-specific addition, not a replacement for any C′
   declaration. This is the difference from route B, whose 4,308-line standalone
   proof *is* a duplicate of a specialisation and is written only to be deleted
   once the general statement lands.
