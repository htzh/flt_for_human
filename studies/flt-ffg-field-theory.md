# Survey: field theory in the `functionFieldGeneration` segment

How much field theory FLT develops inside the `functionFieldGeneration` cone, how
much of it is generic rather than modular, and whether any of it is worth building
bottom up. Everything is read from the pinned clone
`anthropics/fermats-last-theorem@aa2d8b3` (mathlib `v4.34.0` in the port; FLT
itself pins `v4.33.0`).

This is the *segment-scoped* companion to
[flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md),
which surveys the whole repository's curve layer (places, divisors, Riemann–Roch,
Weil pairing). That note answers "does FLT develop function-field theory?" with
"almost all of it". This note asks the narrower question: **inside
`functionFieldGeneration`, what field theory is there, and is it a library or
just a proof?** The plan this feeds is [../lean/PORTING-FFG.md](../lean/PORTING-FFG.md).

Terminology. "Function-field theory" here means the field-theoretic machinery the
segment uses; the segment contains no `Place`, `Divisor`, `genus` or valuation —
those live in the separate `AlgebraicCurve` layer and are outside this cone. What
is actually present is *field-extension theory* (`adjoin`, relative degree,
`minpoly`, splitting, irreducibility) together with the q-expansion layer that
makes the extension concrete.

## 0. The question and the short answer

Question: how much field theory does FLT develop inside the FFG segment, and is
it something to build bottom up?

Answer: **the segment is field theory end to end, but of two different kinds.**

- A **small generic core** — about 180 lines, three lemmas about a polynomial
  over a field extension — that is the mathematical engine of the whole proof and
  is **absent from mathlib**. It is the natural bottom-up target.
- A **large instantiated theory** of the one specific extension
  $`\mathbb{Q}(j(q)) \subseteq \mathbb{Q}(j(q^N))`$ — the relative-degree steps,
  the non-membership lemmas, the slot description. This is modular-specific: it
  cannot be stated generically, and it *is* the theorem, not a library.

The first is insight-dense and cheap; the second is the deferred 24-node
remainder. Building bottom up makes sense for the first, and would sit *under*
the second without discharging it.

The rest of the note measures both, then separates them. One placement fact is
worth stating up front, because it conditions everything else.

### 0.1 The cone is the floor of FLT, and what follows

The measurements in §1 and §8 give a placement that deserves to be read first:

- its **transitive premise closure is 70 theorem nodes** — 67 `ModularCurve.*`
  plus the three generic `Polynomial.*` lemmas — and **26 of the 70 cite no FLT
  theorem at all**, resting directly on four definition modules and mathlib;
- **5,804 theorem nodes depend on it**, every one of them on the path to
  `fermat_last_theorem`, which is **19.9%** of FLT's 29,489-node critical path;
- it is **0.24%** of the theorem nodes and **0.18%** of the lines (144 files,
  24,402 lines, against 60,474 files and 13.5M lines repo-wide).

So the cone is a *source* of the citation DAG: nothing in the Frey, modularity,
Galois-representation or curve layers feeds it, while a fifth of the proof rests
on it. Six consequences.

1. **Verification leverage.** At the floor, a wrong *statement* is maximally
   expensive and a wrong *proof* is maximally cheap to replace. That is why the
   port's `spec/check_flt_statements.py` (137 statements identical to the pin) is
   the right investment, and why `#print axioms` on the cone matters more than
   anywhere else in the tree.
2. **The interface is the deliverable.** The 5,804 nodes reach the cone through a
   handful of channel declarations — `coeffMap_qExpand` (indeg 194),
   `dedekindPsi_prime` (72), `coeffEmb_qExpand` and
   `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (66 each),
   `transcendental_jq` (56), … . Layer 0's real product *is* that interface, and
   it answers "will 0a be used?" far more strongly than the original pitch: it is
   used by the whole tower, not just by math/010.
3. **A bottom-up rebuild is risk-bounded.** Downstream nodes cite statements, not
   proofs, so replacing the cone's generic core (Tier 0–1 of §2) with a
   bottom-up route perturbs nothing above it; the blast radius is the cone
   itself. Rebuilding a *high* node has the opposite risk profile.
4. **Discharging the 10 `Inputs` has outsized payoff.** In the port they are the
   only assumed premises under that fifth of the proof — the 44-node slot input
   is *proved* in FLT. Each field discharged therefore removes a hypothesis from
   under a large region rather than closing one theorem, which is a stronger case
   for the topic-by-topic route than for stop-and-harvest (§4).
5. **"Floor" is not "primitive".** The closure contains the 44-node,
   11,034-line $`\Phi_p`$ slot subtree — the modular-form/Hecke/q-expansion input
   — and the cone uses four definition modules (`ModularCurve_X0`,
   `LaurentCoeff`, `PhiGen`, `ModularForm_HeckeOperator`) that are themselves
   shared by 326–599 nodes each. The genuine primitives are mathlib plus those
   definitions; the cone is the floor of the *arithmetic* tower.
6. **It is a self-contained story.** Being closed under premises and only 70
   nodes, it can be read start to finish without the rest of FLT. That is why
   math/010 can be read linearly, and why it was the right second port.

One caveat on wording: any transitive closure is closed under premises by
construction, so "no inbound dependencies" should be read as "the closure is
small — 70 nodes — and contains no Frey, modularity or `AlgebraicCurve`
theorem", not as "it assumes nothing". What it assumes is the four definition
modules and mathlib.

## 1. The segment and its shape

Boundary: the closure of the capstone in FLT's own doc-site graph, re-derived
with [../tools/deps](../tools/deps).

| quantity | value |
|---|---|
| theorem nodes in the capstone closure | **69** below the capstone |
| files in the cone | 144 |
| lines in the cone | 24,402 |
| definition modules | 4 (1,005 lines) |
| proof layer (`P2M/Sol`) | 71 files, 22,892 lines |
| `Theorems/` wrappers | ~96, 505 lines |
| Φ_p subtree (`PhiGen.splits_prime_at_slot`) | 44 nodes, 94 files, 11,034 lines |
| **remainder below both** | **24 nodes** |

The 24-node remainder is the field-theory half: 13 big `S_ModularCurve_*.lean`
proof files plus three `S_Polynomial_*` files, the small `dedekindPsi_*` files and
`relfinrank_*`. Its per-node file-size sum, as recorded in
[PORTING-FFG §7.3](../lean/PORTING-FFG.md), is **12,420 lines** — and §8.1 of the
port record already flags that this is a file-size sum, not a work estimate. §5
below shows it is a loose upper bound by a wider margin than recorded.

Where the mathematics actually lives:

- the port's **Layer 0** already transcribes the definitions (the q-substitution,
  the twist, the `j`-series, the two fields, `TS`) — 9 modules, 137 declarations;
- the port's **`Spine.lean`** already proves the strong induction `hall_all` and
  the conditional capstone `functionFieldGeneration_of (h : Inputs)`;
- the **10 `Inputs` fields** are exactly the significant modular statements still
  assumed;
- the generic field-theoretic principles FLT uses *inside* those fields' proofs
  are **not in the port at all**.

## 2. The field-theoretic content, as a dependency stack

Read bottom-up, the segment's field theory is six tiers. "Generic" means the
statement makes sense for an arbitrary field extension; "instantiated" means it
mentions `jq`, `jqN` or `LaurentSeries`.

### Tier 0 — polynomial roots over a field extension (generic, mathlib-absent)

The three lemmas, in `P2M/Sol/S_Polynomial_*.lean` (182 lines each, but see §5:
the three files are the *same* file):

| principle | declaration | content |
|---|---|---|
| unique common root | `Polynomial.mem_range_of_unique_common_root` | $`F \subseteq L`$, $`A`$ split with distinct roots; if $`x`$ is the **only** common root of $`A`$ and $`B`$ then $`x \in F`$ |
| constant on enough points | `Polynomial.mem_range_of_eval_eq_const` | $`\deg g \lt \mathrm{card}(s)`$ and $`g`$ constant on $`s`$ $`\Rightarrow`$ the constant lies in $`F`$ |
| transitive automorphism | `Polynomial.irreducible_of_transitive_ringAut` | monic $`P`$ split with distinct roots, one root outside $`F`$, the rest cycled by an $`F`$-fixing ring automorphism $`\Rightarrow`$ $`P`$ irreducible |

These are the engine. §4 of [math/010](../math/010-function-field-generation.md)
(descent by one prime) *is* principle 1; §6's non-membership lemmas *are*
principle 2; §6's prime-power degrees $`p+1`$ and $`p`$ *are* principle 3. The
modular equation supplies the roots; these three supply everything else.

### Tier 1 — `IntermediateField` degree and transport (mostly mathlib, restated)

FLT restates the primitives it needs in the ambient `LaurentSeries ℚ`:

| declaration | location | mathlib source |
|---|---|---|
| `IntermediateField.relfinrank_insert` (`w1_relfinrank_insert`, two versions) | `S_..._relfinrank_full_eq_mul`, `S_..._relfinrank_full_of_squarefree` | `IntermediateField.relfinrank_eq_finrank_of_le` + `IntermediateField.extendScalars_adjoin` |
| `relfinrank_modularFunctionField` | `S_..._relfinrank_modularFunctionField` (31 lines) | the same two |
| `relfinrank_adjoin_primes` | `S_..._relfinrank_full_of_squarefree` | `relfinrank_mul_relfinrank` (tower law) |
| `aeval_intermediateField_eq_zero` | copied into several files | `IntermediateField.aeval_coe` (`FieldTheory/IntermediateField/Basic.lean:596`) |
| `minpoly` degree = adjoin degree (`toAdjoin_eq_minpoly`) | `S_..._finrank_adjoin_jqN_eq_of_squarefree` | `IntermediateField.adjoin.finrank` (`Adjoin/Basic.lean:489`) |

This tier is the port's §1.3 "monomorphic helper" pattern avant la lettre: FLT
itself writes the monomorphic restatement it can rewrite with.

### Tier 2 — bivariate specialization `phiAtSeed` (generic construction, modular data)

`def phiAtSeed {R} [CommRing R] {n} [NeZero n] (data : ModularPolynomialData n)
(x : R) : Polynomial R` evaluates the bivariate $`\Phi`$ at $`X = x`$. The
construction and `phiAtSeed_map`, `_monic`, `_natDegree`, `phiAtSeed_eval_map`,
`phiAtSeed_eval_of_injective` are generic commutative algebra over any commutative
ring; only the `ModularPolynomialData` parameter ties them to the curve. These
lemmas are re-declared inside almost every big file.

### Tier 3 — cyclotomic roots (mathlib primitives, restated)

`exists_isPrimitiveRoot_cyclotomicField`, `cycUnit`, `cycUnit_spec`,
`isPrimitiveRoot_pow_div`. All four are direct consequences of mathlib's
`IsCyclotomicExtension.exists_isPrimitiveRoot` and `IsPrimitiveRoot.pow_of_dvd`;
the port already rebuilds them privately in `Spine.lean`.

### Tier 4 — the Laurent-series/q layer (instantiated, but already in the port)

`TS K e u` = $`j(u q^e)`$; its coefficient lemmas and injectivity, `qTwist_TS`,
`qExpand_TS`, `qTwistEquiv`, `phiProd_conj_eq`, `roots_phiProd_conj*`,
`roots_prime_at_slot*`, `qExpand_qTwist_TS`,
`qExpand_qTwist_notMem_range_qExpand`, `coeffMap_*`. This is modular-specific but
the *transport* part of it (`TS` and its lemmas) is Layer 0 of the port,
`FLTForHuman/ModularCurve/Defs/TS.lean`.

### Tier 5 — the field theory of $`\mathbb{Q}(j) \subseteq \mathbb{Q}(j_N)`$ (instantiated)

The 24-node remainder proper: `jqN_mem_of_div_primes`,
`jqN_div_mem_modularFunctionField`, `modularFunctionField_eq_full_of`,
`full_eq_adjoin_full_div_prime`, `full_eq_adjoin_primes`,
`jqN_prime_not_mem_adjoin`, `jqN_pow_not_mem_adjoin_full`,
`finrank_adjoin_jqN_*`, `relfinrank_full_*`, `minpoly_jqN_map_eq_prod_slots`,
`exists_monic_evalAtJ_jqN_eq_zero`, `exists_phiIrreducible_of_finrank_eq`. This is
where the bulk of the lines are, and every statement mentions `jq`/`jqN`; it is
field theory *of a particular function field*, not a general theory.

### Tier 6 — Dedekind $`\psi`$ arithmetic (number theory, mathlib-absent)

`dedekindPsi_mul_of_coprime`, `dedekindPsi_prime_pow`,
`dedekindPsi_of_squarefree`, and the slot-sum combinatorics
(`slotAt`, `slots`, `slots_eq_dedekindPsi`, `gcd_*` helpers). Mathlib has
`ArithmeticFunction` and `Nat.totient`, but no $`\psi`$ function. This is the
one part of the segment that is neither field theory nor modular curves.

**The answer to "how much".** Generic field theory (Tiers 0–1) is ~300 distinct
lines; Tier 2 is ~40; Tier 3 is ~40; the modular-specific field theory is the
remaining thousands (Tier 4–5), and the ψ arithmetic is ~400 spread across files.
So: a real generic kernel, wrapped in a large modular instantiation.

## 3. The mathlib interface, lemma by lemma

Checked against the port's mathlib `v4.34.0`.

**Present in mathlib, used by the port (no port-side lemma needed):**

| mathlib declaration | where |
|---|---|
| `IntermediateField.relfinrank`, `relfinrank_eq_finrank_of_le`, `relfinrank_mul_relfinrank`, `relfinrank_eq_one_iff` | `FieldTheory/Relrank.lean` (532 lines) |
| `IntermediateField.extendScalars_adjoin`, `adjoin.mono`, `adjoin_le_iff`, `subset_adjoin` | `FieldTheory/IntermediateField/Adjoin/Defs.lean` |
| `IntermediateField.aeval_coe`, `inclusion` | `FieldTheory/IntermediateField/Basic.lean:596` |
| `IntermediateField.adjoin.finrank` | `FieldTheory/IntermediateField/Adjoin/Basic.lean:489` |
| `minpoly`, `minpoly.monic`, `minpoly.dvd`, `minpoly.aeval`, `eq_of_monic_of_dvd_of_natDegree_le` | `FieldTheory/Minpoly/*` |
| `Polynomial.Splits`, `Splits.natDegree_eq_card_roots`, `Splits.mem_range_of_isRoot`, `roots.le_of_dvd`, `Monic.irreducible_iff_natDegree` | `Algebra/Polynomial/Splits.lean:368,547`, `Roots.lean:186`, `Monic.lean:335` |
| `IsPrimitiveRoot`, `CyclotomicField`, `IsCyclotomicExtension.exists_isPrimitiveRoot` | `RingTheory/RootsOfUnity/*`, `NumberTheory/Cyclotomic/Basic.lean` |

**Absent from mathlib, proved by FLT (the bottom-up candidate set):**

| FLT declaration | why mathlib does not have it |
|---|---|
| `Polynomial.mem_range_of_unique_common_root` | mathlib has `Splits.mem_range_of_isRoot` (one root, one splitting polynomial), not the two-polynomial common-root criterion |
| `Polynomial.mem_range_of_eval_eq_const` | mathlib has `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`, not the "value lies in the base" corollary |
| `Polynomial.irreducible_of_transitive_ringAut` | mathlib has irreducibility criteria via `natDegree` divisors and Galois/`Normal` API, but not this cyclic-automorphism criterion |
| `dedekindPsi` and its arithmetic | no $`\psi`$ function in mathlib (greps for `dedekindPsi` are empty) |
| the whole of Tier 5 | instantiated; nothing general to state |

The three polynomial lemmas are the only *substantive* generic mathematics the
segment adds to mathlib. A `grep` for their names over `Mathlib/` returns
nothing.

## 4. Is it worth building bottom up?

**The case for.**
The three lemmas are exactly the math insight this survey was asked to find: they
are the principles the whole induction turns on, they are 180 lines in total, and
they are stated with no modular content at all. Building them bottom-up means
proving, in a clean dependency order,

1. a split squarefree polynomial with a unique common root with another
   polynomial has that root in the base field (the rational-root principle
   behind descent);
2. a low-degree polynomial that is constant on enough points has its constant
   value in the base field (behind non-membership);
3. a split monic polynomial whose roots are cycled by a base-fixing automorphism,
   with one root outside the base, is irreducible (behind the $`p+1`$ / $`p`$
   degree steps),

plus the Tier 1 bridges that connect them to `IntermediateField.relfinrank`. That
is a self-contained module a reader can walk linearly, and it is the layer the
port's `Spine.lean` currently *assumes* through the 10 `Inputs`. Making the
assumption explicit as proved generic lemmas is a genuine gain in comprehension,
independent of the theorem.

**The case against (for the rest).**
Tier 5 is not a library: its statements are about `jq`/`jqN` in
`LaurentSeries ℚ`, and generalizing them *is* re-proving the modular-curve
theorem. Tier 4 (`TS`, `qTwist`, roots of `phiProd`) is already built in the port
as Layer 0. Tier 6 is number theory, orthogonal to function fields. So
"build the segment's function-field theory bottom up" reduces to "build Tier 0
(and its Tier 1 bridges), then continue Layer 0's style for Tier 5" — the second
being the deferred theorem.

**A concrete shape.** A module `FLTForHuman/FieldTheory/CommonRoot.lean` (name
suggestive, not prescribed) containing the three Tier-0 lemmas over an arbitrary
$`F \subseteq L`$, with the monomorphic Tier-1 bridges, docstrings naming the
transported principle, and — as the wire test — the derivation of one existing
`Inputs` field's *inner* step from them. It would be mathlib-only, `sorry`-free,
and would sit beside `FLTForHuman/ModularCurve/` without touching the 137-statement
correspondence.

**Recommendation.** Do Tier 0 + Tier 1 as a topic. Treat Tier 5 as the deferred
theorem it already is. The three polynomial lemmas are the highest
insight-per-line artifact available in this segment, and they are currently
neither in mathlib nor in the port.

## 5. Corrections to the manifest: file size is not node cost

The 12,420-line per-node sum in [PORTING-FFG §7.3](../lean/PORTING-FFG.md)
attributes whole `S_` files to single nodes. Measured against the files
themselves, that sum is a loose upper bound. Four effects:

1. **Exact duplication.** `S_ModularCurve_jqN_prime_not_mem_full.lean` and
   `S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` (2,002 lines each) are the
   *same file*: stripping namespaces and the one-line `solution`, `diff` is 62
   lines, all of them `p2m_*` namespace plumbing. The same holds for
   `S_ModularCurve_jqN_div_mem_modularFunctionField.lean` and
   `S_ModularCurve_modularFunctionField_eq_full_of.lean` (735 lines each; `diff`
   is 0 after stripping), and for the three `S_Polynomial_*` files (182 lines
   each, identical but for the `solution` line — already noted in
   [logs/ffg-port.md §8.1](../lean/logs/ffg-port.md)). Removing the repeats:
   −2,002, −735, −364.
2. **A node re-proved inside another node's file.** The 2,002-line file proves
   `jqN_prime_not_mem_adjoin`, `minpoly_jqN_map_eq_prod_slots` **and**
   `jqN_prime_not_mem_full`; `S_ModularCurve_jqN_prime_not_mem_adjoin.lean` (653
   lines) is a second proof of the first. At least one of the two is redundant.
3. **A shared 360-line prelude.** The `TS`–`qTwist`–cyclotomic–`phiProd`–
   `roots_prime_at_slot`–`phiAtSeed` block is copied verbatim into the front of
   each big file: 11 of the 13 remainder files before de-duplication, 9 distinct
   files after, one of them partial; and **38 `S_ModularCurve_*` files** in the
   cone's neighbourhood carry the full block (13,426 lines of the same
   declarations; `grep -l '^def TS ' S_ModularCurve_*.lean` finds 50). A bottom-up
   library writes it once.
4. **A node whose file proves something else.** `S_ModularCurve_dedekindPsi_mul_of_coprime.lean`
   is 471 lines, but `dedekindPsi_mul_of_coprime` is proved in roughly the first
   72 lines from `ArithmeticFunction` multiplicativity; the remaining ~399 lines
   are a resultant/elimination development for
   `nonempty_modularPolynomialData_mul_of_coprime`, which is **not a node in the
   doc-site graph at all** and is off the capstone path. The node's real cost is
   ~72 lines, not 471.

Structural estimate after these corrections, as an explicit ledger off the 12,420
headline:

| correction | lines removed |
|---|---|
| second copy of the `jqN_prime_not_mem_full` file | −2,002 |
| second copy of the `modularFunctionField_eq_full_of` file | −735 |
| two extra copies of the `S_Polynomial_*` file | −364 |
| `jqN_prime_not_mem_adjoin`, a second proof inside the 2,002-line file | −653 |
| resultant development off the capstone path, in the `dedekindPsi` file | −399 |
| duplicate standalone `S_ModularCurve_dedekindPsi_prime_pow.lean` | −38 |
| **de-duplicated remainder** | **≈8,229** |
| 8 of the 9 copies of the 360-line prelude (one is kept) | −2,880 |
| **prelude written once** | **≈5,349** |

This is a structural line count, not a proof budget: [porting-playbook.md](../lean/porting-playbook.md)
and [logs/ffg-port.md §6](../lean/logs/ffg-port.md) both record that proof cost in
this project tracks *shape risk*, not lines. It does say the deferred remainder is
smaller than the manifest's headline, and that a bottom-up library removes
duplication the per-node view hides.

## 6. Reproduction recipes

Closure, remainder and per-node file sizes (needs `tools/deps`):

```bash
cd tools/deps && python3 - <<'PY'
import sys; from pathlib import Path; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); FLT = Path.home() / 'proj' / 'fermats-last-theorem'
def closure(i):
    seen, stack = set(), [i]
    while stack:
        j = stack.pop()
        if j in seen: continue
        seen.add(j); stack.extend(d.cites(j))
    return seen
def lines(p): return sum(1 for _ in open(p, encoding='utf-8')) if p.exists() else 0
cap = d.index['ModularCurve.functionFieldGeneration']
slot = d.index['ModularCurve.PhiGen.splits_prime_at_slot']
for n in sorted((closure(cap) - closure(slot)) - {cap},
                key=lambda n: -lines(FLT / f"P2M/Sol/S_{d.stem_of[n]}.lean")):
    print(f"{lines(FLT / f'P2M/Sol/S_{d.stem_of[n]}.lean'):5d}  {d.qual(n)}")
PY
```

Duplication and the shared prelude:

```bash
cd ~/proj/fermats-last-theorem/P2M/Sol
diff <(grep -vE 'namespace P2MW|theorem solution|p2m_|^  ModularCurve\.' \
        S_ModularCurve_jqN_prime_not_mem_full.lean) \
     <(grep -vE 'namespace P2MW|theorem solution|p2m_|^  ModularCurve\.' \
        S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean) | wc -l   # 62, all plumbing
grep -l '^def TS ' S_ModularCurve_*.lean | wc -l                      # 50
grep -c 'dedekindPsi_mul_of_coprime' S_ModularCurve_dedekindPsi_mul_of_coprime.lean
```

Mathlib gaps:

```bash
cd lean/.lake/packages/mathlib/Mathlib
for t in unique_common_root irreducible_of_transitive_ringAut mem_range_of_eval_eq_const dedekindPsi; do
  printf '%-36s ' "$t"; grep -rl "$t" --include='*.lean' . | wc -l
done
```

## 7. Why the cone contains no `AlgebraicCurve` theory

Measured: the capstone closure has **0** `AlgebraicCurve` theorem nodes; none of
the 13 remainder `S_` files and none of the cone's definition modules mentions
`AlgebraicCurve`. The question "is that because they chose to coefficient-bash the
`jq` series?" has three answers, in increasing depth.

**(a) The object is presented by q-expansions.** `modularFunctionField N` and
`modularFunctionFieldFull N` are `IntermediateField ℚ (LaurentSeries ℚ)`
([Def_ModularCurve_X0.lean#L250-L305](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L250-L305)).
The target is an equality of two subfields of Laurent series, so both sides are
coefficient-level by construction. Every `CurveModel` for $`X_0(N)`$ is then built
*on* that presentation: `M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p)`
([Def_ModularCurve_DRModelPackage.lean#L51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DRModelPackage.lean#L51))
takes the intermediate field as the curve's function field. The curve is
downstream of the field, not the other way round.

But this is not a free choice. FLT has no Riemann existence theorem and no
complex-analytic construction of $`X_0(N)`$; it builds the curve by glueing charts
from a field presentation, and the only concrete presentation available without
analysis is the q-expansion field. Given that presentation, the modular equation
must be proved on q-expansions — which is exactly the 44-node slot subtree
(math/010 §3), not gratuitous bashing.

**(b) The available curve theory has no moduli content for $`X_0(N)`$.** FLT's
`AlgebraicCurve` layer is abstract: `Place`, `Divisor`, `Pic0`, and the
degree/fundamental-identity lemmas over an arbitrary `IsCurveOver K F`. It has
the classical principle "$`\deg`$ = fibre count"
(`Place.sum_ramificationIndex_mul_inertiaDeg`) and the bridge to field degrees
(`finrankAlong_eq_relfinrank_fieldRange`), but it knows nothing about cyclic
$`N`$-isogenies or the upper half plane. It therefore cannot supply the one hard
input — the description of the roots of $`\Phi_p`$. The modular-form/Hecke
q-expansion cluster is what supplies it instead.

**(c) The curve structure is proved *downstream* of FFG.** This is the decisive
point, and it is a dependency measurement from `tools/deps`:

| fact | its closure contains |
|---|---|
| `isCurveOver_modularFunctionFieldBar` | `functionFieldGeneration` (direct citer), `finrank_adjoin_jqN_eq_dedekindPsi`, `PhiGen.splits_prime_at_slot` |
| `isCurveOver_modularFunctionFieldFullC` | `finrank_adjoin_jqN_eq_dedekindPsi`, `PhiGen.splits_prime_at_slot` |
| `isCurveOver_modularFunctionFieldC_of_perfectField` | `finrank_adjoin_jqN_eq_dedekindPsi`, `exists_phiIrreducible`, `PhiGen.splits_prime_at_slot` |
| `qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull` | `finrank_adjoin_jqN_eq_dedekindPsi`, `exists_phiIrreducible`, `PhiGen.splits_prime_at_slot` |
| `stichtenothGenusExists_modularFunctionFieldBar`, `functionFieldRiemannRoch_modularFunctionFieldBar`, `exists_genus_riemannIndex_modularFunctionFieldBar` | `functionFieldGeneration` |

The three corollaries `finrank_adjoin_jqN_eq_dedekindPsi`,
`relfinrank_full_eq_dedekindPsi` and `exists_phiIrreducible` are *siblings* of the
capstone, not consequences of it: each has its own 70-node closure citing
`splits_prime_at_slot`, `minpoly_jqN_map_eq_prod_slots`,
`finrank_adjoin_jqN_pow_succ_of_not_mem` and `relfinrank_full_eq_mul` — the same
engine. So the curve layer consumes the modular equation's degree/splitting
facts; it cannot be used to prove them without circularity.

The only genuinely independent curve model is the automorphic one over $`\mathbb{C}`$:
`IsCurveOver ℂ (automorphicField Γ)` with a place dictionary from $`\mathbb{H}`$ to
`Place`. It is unbridged to the q-expansion side — **0 files mention both
`automorphicField` and `qExpFunctionFieldC`**. Crossing that bridge is the missing
analytic step.

**Would curve theory make the proof easier?** Not with the theory as it stands:
using `IsCurveOver`/places for FFG would be circular by (c). In principle a
moduli-first development is more *conceptual*: the classical proof reads
generation off the degree $`\psi(N)`$ of $`X_0(N) \to X(1)`$, computed from cyclic
isogenies or cusp widths, and the field-theoretic bookkeeping then collapses. But

- it still needs the hard degree input, which FLT obtains from the $`\Phi_p`$ root
  description (the 44-node, 11,034-line slot subtree) — a moduli route replaces an
  11k-line modular-forms argument with a moduli argument, not obviously smaller;
- it needs a Riemann-existence / analytic comparison to pass between the analytic
  model and the q-expansion field, which is precisely the unbridged step and
  plausibly harder than FFG itself;
- the field theory curve theory would tidy — the ~5,300-line remainder — is not the
  bottleneck; the slot subtree is.

So: more conceptual, not cheaper, and not available today.

One thing the curve layer does not hide is an analytic gap: its Riemann–Roch is
proved algebraically, from `IsCurveOver`, by the adic/Tate residue route (see
[flt-function-field-theory-and-mathlib.md §13](flt-function-field-theory-and-mathlib.md)).
So the analysis this segment lacks is exactly the analytic bridge above — Riemann
existence, a complex model of $`X_0(N)`$, and its comparison with the q-expansion
field — not the algebraic theory of curves.

## 8. Cross-pollination with the rest of FLT

The cone is not a leaf. Measured on the doc-site graph:

| direction | measurement |
|---|---|
| **outbound** (cone used elsewhere) | **500** direct citers; **5,804** transitive theorem nodes depend on the cone — ~20% of all 29,511 |
| **inbound** (cone uses other sectors' theorems) | **~0**: the closure is 70 nodes, all `ModularCurve`/`Polynomial`; the only outside nodes are the two `AlgebraicCurve` cites noted in §7 |
| **shared definition modules** | 4 — `ModularCurve_X0` (referenced by 516 repo nodes), `ModularCurve_LaurentCoeff` (599), `ModularForm_HeckeOperator` (336), `ModularCurve_PhiGen` (326) |

So the cross-pollination is almost entirely **outbound**, and it flows through
small interface declarations rather than the headline theorem. Cone nodes by
repo-wide indegree (number of theorem nodes citing them):

| declaration | indeg |
|---|---|
| `coeffMap_qExpand` | 194 |
| `dedekindPsi_prime` | 72 |
| `coeffEmb_qExpand` | 66 |
| `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` | 66 |
| `transcendental_jq` | 56 |
| `functionFieldGeneration` | 52 |
| `dedekindPsi_mul_of_coprime` | 46 |
| `PhiGen.splits_prime_at_slot` | 42 |

`coeffMap_qExpand` — "coefficient extension commutes with the q-substitution" — is
the single most-shared declaration in the cone. The outbound traffic lands in
these sub-sectors (transitive counts): `FullLevel` 1,119, `PlaceSpecialization`
507, `CuspForm` 280, `XOneP` 273, `XH` 237, `DRModel` 211, `CerednikDrinfeld`
117, `JZero` 97, `JHPlaceSpecialization` 90, `MultCovering` 90, `IgusaScheme` 89,
`WeierstrassCurve` 76, `JHNeronObjectAtP` 75, `CharPModel` 74, … `FreyPackage`
17, `GaloisRep` 15, `AlgebraicCurve` **6**. So the curve-theoretic citations are
real but tiny; the modular-curve side is where the reuse is.

### 8.1 The `jq` coefficient results are a separate hub

The low-coefficient computations are **not** in the cone. `coeff_jNum_le_six` and
`coeff_jNum_le_twelve` — the six/twelve coefficients FLT proves in the standalone
[`S_ModularCurve_coeff_jNum_le_six.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeff_jNum_le_six.lean),
the analogue of the port's `JqCoefficients.lean` — each have indeg **1**: they are
consumed by `ModularPolynomialData.phi_eq_phiTwo` and `phi_eq_phiThree`, the
explicit modular polynomials at levels 2 and 3. From there they fan out to
**2,688** and **651** transitive nodes.

The two hubs barely touch as dependencies: `coeff_jNum_le_six` is not in the
cone's closure, and `functionFieldGeneration` is not in the coefficient hub's
closure. Yet 2,687 of the 2,688 nodes below the coefficient hub also depend on the
cone — they meet in the *downstream*, through the shared interface lemmas
(`coeffMap_qExpand`, `coeffEmb_qExpand`, `transcendental_jq`,
`qExpansion_discriminant_…`), not through the coefficients.

The *architectural* coefficient facts are different: `coeff_jqModC_neg_one` (the
characteristic-$`p`$ pole coefficient) has indeg **120** and crosses into
`ModPForms`, `FullLevel` and the rest of the outbound list. So the pole is
load-bearing everywhere, while the 744/196884 computations feed the small-level
modular polynomials.

For the port this settles a classification: `JqCoefficients.lean` was right to be
a *topic* rather than part of Layer 0 — in FLT's graph it belongs to the
$`\Phi_2`$/$`\Phi_3`$ cluster, not to the FFG cone, even though the consumer's Zone C
sits in the FFG file.

Reproduce:

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0,'.')
from fltdata import FltData
d=FltData()
def up(i):
    seen,st=set(),[i]
    while st:
        j=st.pop()
        if j in seen: continue
        seen.add(j); st.extend(d.cites(j))
    return seen
cap=d.index['ModularCurve.functionFieldGeneration']; C=up(cap)
ext=set()
for n in C:
    ext.update(c for c in d.cited_by[n] if c not in C)
out=set(); st=list(ext)
while st:
    j=st.pop()
    if j in out or j in C: continue
    out.add(j); st.extend(d.cited_by[j])
print('direct citers:',len(ext),' transitive downstream:',len(out))
for n in sorted(C, key=lambda n:-d.indeg(n))[:8]:
    print(f'{d.indeg(n):5d}  {d.qual(n)}')
PY
```

## 9. Links

FLT at `aa2d8b3`:

- capstone: [Thm_ModularCurve_functionFieldGeneration.lean#L8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean#L8)
- the generic core: [S_Polynomial_mem_range_of_unique_common_root.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Polynomial_mem_range_of_unique_common_root.lean) — the other two `S_Polynomial_*` files are the same file
- descent: [S_ModularCurve_jqN_div_mem_modularFunctionField.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_jqN_div_mem_modularFunctionField.lean) — same file as `S_ModularCurve_modularFunctionField_eq_full_of.lean`
- the shared prelude: [S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean) — lines 35–404
- ψ arithmetic plus off-path resultants: [S_ModularCurve_dedekindPsi_mul_of_coprime.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_dedekindPsi_mul_of_coprime.lean) — ψ part at lines 24–72

Companion notes:

- [flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md) — the repository-wide curve-layer survey
- [../math/010-function-field-generation.md](../math/010-function-field-generation.md) — the mathematics of this segment
- [../lean/PORTING-FFG.md](../lean/PORTING-FFG.md) — the plan
- [../lean/logs/ffg-port.md](../lean/logs/ffg-port.md) — the port record and the duplication findings
- [../lean/porting-playbook.md](../lean/porting-playbook.md) — the cost model
