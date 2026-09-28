# A driver for the T side

**Status: recommendation, measured 2026-09-28** against the pin `aa2d8b3` with
`tools/deps`, after T11 landed the T-side definition layer
([../lean/topics/hecke/TOPIC-t11-t-side-definitions.md](../lean/topics/hecke/TOPIC-t11-t-side-definitions.md),
[../lean/logs/t-side-port.md](../lean/logs/t-side-port.md)). It answers: *which
T-side target should the next port push on?* The recommended driver is the
**$`R \cong T`$ assembly**,
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`, ported as a
**conditional capstone** (§4).

Companions: [r-equals-t-in-the-proof-base.md](r-equals-t-in-the-proof-base.md)
(the graph route, consumers, and the T-side port-scope reading §6),
[../math/018-t-side-definitions.md](../math/018-t-side-definitions.md) (the
definitions), [hecke-finiteness-coverage.md](hecke-finiteness-coverage.md) §3,
§6 (the endgame verdict and the T side), and
[../lean/porting-playbook.md](../lean/porting-playbook.md) §7.3 (the conditional
capstone).

## 0. Method, and the C′ caveat

The estimate is `frontier.py`'s: for a target $`t`$,

$$\mathrm{needed}(t) \;=\; \bigl\{\, v \text{ reachable from } t
  \text{ avoiding } R \,\bigr\} \setminus F,$$

with $`F`$ the ported frontier (the checker's `SOURCES` wrappers plus the
declarations found in `lean/FLTForHuman/`) and no removal set $`R`$. "Lines" is
the `S_`-file metric, so it is the *pin*'s written volume for the still-unported
theorem nodes; T11's definition modules are already ported and are not in the
theorem cones.

**The C′ caveat, quantified.** The FLT citation graph prices the T side through
route A: `hasIntegralStructure_of_two_le` (657 nodes / 263,720 raw `S_` lines) and
route B's standalone `moduleFinite_heckeAlgebra_two` (4,308 lines). The port
obtained integrality and finiteness instead through the **C′ shortcut**
(`ModularForms/WeightOne/*` + the trace lemma) and T10
(`HeckeFiniteAlgebra.lean`), and `frontier.py` already treats those nodes as
ported — they are in $`F`$ in **both** reading tiers (`sources` and `names`). The
estimate below therefore does **not** charge route A or route B. Concretely,
removing the 13 C′-and-T10 nodes from $`F`$ and recomputing:

| target | frontier, as measured | if C′/T10 were undone | C′ residual |
|---|---:|---:|---:|
| the $`R \cong T`$ assembly | 26 / 7,287 | 31 / 7,522 | **5 / 235** |
| p=3 modularity lifting | 22,583 / 7,734,215 | 22,595 / 7,739,810 | **12 / 5,595** |

The twelve for the lifting theorem are headed by `moduleFinite_heckeAlgebra_two`
(4,308) and `hasIntegralStructure_of_two_le` (515) — precisely the route-A/B work
the shortcut removed. **Any estimate for a T-side target that reads the FLT map
without this substitution overcounts by those amounts**, and the deep patching
targets are the ones where the substitution matters (§3). The assembly's own
reliance is only 235 lines, because it takes `HasIntegralStructure` as a
*hypothesis* and uses the ported `HasIntegralStructure.moduleFinite_heckeAlgebra`
at line 108 of its proof.

## 1. The recommended driver

`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`
(pin `P2M/Sol/S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`,
145 lines) is the assembly that concludes **$`W`$ is modular of level
$`N \prod_{q \in S, q \nmid N} q`$** from a patching datum plus the two halves of
$`R \cong T`$. Its proof is where the equality actually happens:
`AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩` at line 69.

It satisfies the three criteria:

- **Real mathematics.** The proof does the patching-side injectivity (a free
  nontrivial patched module forces $`\varphi`$ injective), then the
  Eichler–Shimura comparison: it applies $`R`$'s universal property a second time
  at $`A = \mathcal{O}`$, transports the point across the isomorphism, compares
  Frobenius characteristic polynomials (`GaloisRepAdic.charpoly_baseChangeAlong`,
  `charpoly_eq_of_isEquiv`) to read off $`\psi_W(\pi(T_\ell)) = a_\ell(W)`$, and
  converts the resulting Hecke character into a normalised eigenform via
  `Ideal.exists_ringHom_integralClosure_ker_eq`. Not plumbing.
- **On the critical path.** Depth 7 from `fermatLastTheorem`, on the shortest
  chain
  `fermatLastTheorem → … → frey_isModular → modularity_of_semistableModel → (p=3 lifting) → this node`.
- **Significant ported base.** 39 of its 65-node cone are already in $`F`$ (60%):
  the whole Hecke operator/`q`-coefficient/Sturm/`intLattice` layer and the
  C′/T10 integrality and finiteness.

## 2. The estimate

| reading | frontier | `S_` lines |
|---|---:|---:|
| full assembly (unconditional) | 26 nodes | 7,287 |
| **conditional capstone** (§4) | **16 nodes** | **1,663** |
| deferred patching cluster | 10 nodes | 5,624 |

The full frontier is dominated by one node: `Algebra.PatchingDatum.nonempty_patchingLevel_bot`,
the Taylor–Wiles patching construction, whose `S_` file is **3,789 lines** and
whose imports are 46 mathlib modules of topology, profinite groups, filtrations
and adic completion. It is the single largest risk in the T side, and it is
separable (§4).

The 16 conditional nodes, by cost:

| `S_` lines | node |
|---:|---|
| 314 | `ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime` |
| 246 | `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom` |
| 184 | `ValuationSubring.exists_integral_mul_eq_of_liesOverPrime` |
| 147 | `CuspForm.exists_isNormalizedEigenform_level_mul` |
| 145 | the assembly itself |
| 144 | `CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` |
| 115 | `CuspForm.exists_degeneracy_Gamma0` |
| 95 | `CuspForm.linearIndependent_of_mem_intLattice` |
| 76 | `Ideal.exists_ringHom_integralClosure_ker_eq` |
| 51 | `CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong` |
| 39 | `CuspForm.exists_isNormalizedEigenform_of_dvd` |
| 30 | `ValuationSubring.exists_isFrobeniusAt_rat` |
| 30 | `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` |
| 25 | `CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul` |
| 13 | `GaloisRepAdic.charpoly_eq_of_isEquiv` |
| 9 | `GaloisRepAdic.charpoly_baseChangeAlong` |

`frontier.py --target … --top` gives the fewest-new-nodes-first order:
`CuspForm.linearIndependent_of_mem_intLattice` (1 needed), then
`CuspForm.exists_isNormalizedEigenform_level_mul` (2), then
`CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul` (3), then
`CuspForm.exists_isNormalizedEigenform_of_dvd` (3, two hops), then
`CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` (5).

## 3. The survey behind the choice

All T-side nodes in the endgame (the 266 of
[r-equals-t-in-the-proof-base.md](r-equals-t-in-the-proof-base.md) §6), ranked by
**ported-base fraction** (cone $`\ge 8`$, so leaves are excluded). "need / lines"
is the C′-adjusted frontier.

| ratio | need | lines | depth | target |
|---:|---:|---:|---:|---|
| 0.75 | 3 | 2,555 | — | `CuspForm.HeckeGaloisRepDatum.exists_points_jointly_injective` |
| 0.60 | **26** | **7,287** | **7** | **`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`** |
| 0.56 | 8 | 4,689 | — | `CuspForm.heckeLocal.finrank_le_of_forall_point_exists_extension` |
| 0.52 | 47 | 20,329 | 15 | `CuspForm.heckeLocal.pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd` |
| 0.39 | 159 | 93,041 | 16 | `CuspForm.TWLevel.HeckeRing.exists_isEigenformWith_or_eisenstein_of_algHom` |

Against the alternatives:

- **The two modularity lifting theorems** (depth 6, the true endgame drivers)
  cost 22,583 and 22,262 nodes — the Selmer-side cotangent criterion and the
  Taylor–Wiles module ladder. Out of reach as a next step; they are what the
  driver is *toward*.
- **The abstract patching exit** `Algebra.PatchingDatum.bijective_and_free_of_surjective`
  (depth 10, 13 nodes) is the $`R \cong T`$ statement in isolation, but its
  frontier is 5,690 lines, 5,624 of them the same patching cluster. It is a
  component of the driver, not a cheaper substitute.
- **The surjection half** `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`
  (depth 7, 7 nodes / 610 lines) is the cheapest genuinely mathematical T-side
  target, but it is one half of one step, with no ported base of its own.
- **`CuspForm.heckeLocal.pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd`** (52% ported,
  47 nodes) is the best non-assembly candidate — real arithmetic (the vanishing
  of $`U_q`$ when $`q^2 \parallel N`$) — but it is depth 15 and its 20,329-line
  frontier sits below the patching ladder rather than leading it.

The assembly wins because it is the shallowest T-side node that is both
*theorem-shaped* and *mostly ported*: it is the first place the T side becomes
mathematics the endgame can consume.

## 4. The conditional-capstone split

Playbook §7.3: when a proof is an assembly over largely independent inputs, state
the capstone with the heavy input as a named field first. Here the heavy input is
the patching level. Take as hypotheses the *output* of
`Algebra.PatchingLevel.free_and_ker_eq_span` — a level `L`, `Module.Free R M`,
`Module.annihilator R M = ⊥` and the kernel description — instead of calling
`P.nonempty_patchingLevel_bot` and `L.free_and_ker_eq_span` inside. Then:

- **the capstone port costs 16 nodes / 1,663 lines** (the surjection half, the
  Frobenius/charpoly lemmas, the eigenform-extraction chain, and the 145-line
  assembly) and its `#print axioms` is clean, because every field is a
  hypothesis;
- **the deferred field is the patching cluster**: `nonempty_patchingLevel_bot`
  (3,789 lines), `free_and_ker_eq_span` (310), six `MvPowerSeries` lemmas
  (~1,300), `Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal`,
  `IsAdicComplete.map_of_surjective` — 10 nodes / 5,624 lines, discharging
  `Algebra.PatchingDatum.bijective_and_free_of_surjective` (the abstract
  patching exit) on the way.

The split is honest about the C′ caveat: neither half is gated on route A or B.
The C′-provided finiteness is *inside* the capstone's ported base
(`HasIntegralStructure.moduleFinite_heckeAlgebra`, used at the assembly's line
108 to feed `Ideal.exists_ringHom_integralClosure_ker_eq`), so the capstone cannot
be ported without it — and it is already there.

Proposed work-order decomposition:

- **SET 1 — the surjection half.** `CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong`
  + `GaloisRepAdic.charpoly_baseChangeAlong`/`charpoly_eq_of_isEquiv` +
  `ValuationSubring.exists_isFrobeniusAt_rat`/`_of_liesOverPrime` +
  `exists_integral_mul_eq_of_liesOverPrime`; then
  `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`.
  Small, and it delivers the $`R \twoheadrightarrow T`$ half.
- **SET 2 — the eigenform-extraction chain.** The `CuspForm.HasIntegralStructure.exists_*`
  and `CuspForm.exists_isNormalizedEigenform_*` family, plus
  `linearIndependent_of_mem_intLattice`, `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom`,
  `Ideal.exists_ringHom_integralClosure_ker_eq` and
  `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed`. Pure
  Hecke-side mathematics, reusing T8's eigenform dictionary.
- **SET 3 — the conditional capstone.** State and prove the assembly with the
  patching facts as hypotheses; its own `AlgEquiv.ofBijective φ ⟨hinj,hsurj⟩`.
- **SET 4 (deferred) — the patching cluster.** `Algebra.PatchingLevel.free_and_ker_eq_span`,
  `Algebra.PatchingDatum.nonempty_patchingLevel_bot` and the `MvPowerSeries`
  lemmas; then discharge SET 3's hypotheses and recover the unconditional
  assembly.

## 5. Risks

- **The patching monolith.** `nonempty_patchingLevel_bot` is 3,789 `S_` lines
  importing profinite/compact/topological-ring machinery; it is the one place on
  the T side where the playbook's "cost tracks distance from mathlib" bites
  hardest. Keep it in SET 4, port it in bounded pieces, and expect the
  `MvPowerSeries`/`AdicCompletion` API to be the friction.
- **The eigenform-extraction chain is shared with the endgame.** These nodes are
  also wanted by the weight-one/modularity branch, so porting them for the driver
  is not throwaway — but it means the frontier can move under the estimate if
  another effort lands them first. Re-measure before starting.
- **Do not price route A/B.** Any work order written for this driver must state
  the C′ substitution explicitly (§0), or it will look like a 263k-line job.
- **T11 is the base.** The driver's statements are parameterised by T11's
  structures (`GaloisRep.DeformationRingData`, `CuspForm.HeckeGaloisRepDatum`);
  do not port the theorem layer against pin copies of those.

## 6. Reproduction

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
from frontier import Frontier
d = FltData(); F = Frontier(); fu = F.frontier('union')
def cl(i):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j); st.extend(d.cites(j))
    return seen
i = d.index['WeierstrassCurve.isModularModelOfLevel_of_patchingDatum']
need = cl(i) - fu
print('full assembly frontier:', len(need), F.total_lines(need))
patch = (cl(d.index['Algebra.PatchingDatum.nonempty_patchingLevel_bot'])
         | cl(d.index['Algebra.PatchingLevel.free_and_ker_eq_span']))
cond = need - patch
print('patching cluster:', len(need & patch), F.total_lines(need & patch))
print('conditional capstone:', len(cond), F.total_lines(cond))
# C-prime residual
cp = [d.index[n] for n in [
 'CuspForm.hasIntegralStructure_of_two_le','CuspForm.hasIntegralStructure_two',
 'CuspForm.moduleFinite_heckeAlgebra','CuspForm.moduleFinite_heckeAlgebra_two',
 'CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra',
 'CuspForm.HasIntegralStructure.moduleFree_heckeAlgebra',
 'CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice',
 'CuspForm.intLattice_fg','CuspForm.fg_toSubmodule_heckeAlgebra',
 'CuspForm.finrank_span_heckeAlgebra_eq_finrank','ModularForm.sturm_bound_Gamma0',
 'ModularForm.sturm_bound_of_isArithmetic','CuspForm.finiteDimensional_Gamma0']
 if n in d.index]
F1 = fu - set(cp)
for t in [i, d.index['WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd']]:
    c = cl(t); print(d.qual(t), 'C-prime residual:', len((c-F1)-(c-fu)), F.total_lines((c-F1)-(c-fu)))
PY
```

Frontier and order:

```bash
cd tools/deps
python3 frontier.py --target WeierstrassCurve.isModularModelOfLevel_of_patchingDatum --top 12
```

## 7. Pointers

- [r-equals-t-in-the-proof-base.md](r-equals-t-in-the-proof-base.md) §6–§7 —
  the T-side node set, the port-scope reading, and the R=T route.
- [hecke-finiteness-coverage.md](hecke-finiteness-coverage.md) §3, §6 — why the
  general finiteness is unavoidable for the endgame, and what the T side adds.
- [route-c-prime-scout.md](route-c-prime-scout.md) — the C′ shortcut and the
  trace lemma, the reason §0's substitution is legitimate.
- [../lean/topics/hecke/TOPIC-t11-t-side-definitions.md](../lean/topics/hecke/TOPIC-t11-t-side-definitions.md),
  [../lean/logs/t-side-port.md](../lean/logs/t-side-port.md) — the definition
  layer this driver builds on.
- [../lean/porting-playbook.md](../lean/porting-playbook.md) §3.11 (build
  discipline), §5 (checklist), §7.3 (the conditional capstone).
