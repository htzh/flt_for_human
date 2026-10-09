# The qexp head's successors — scope of the nodes the landing unblocked

**Status: scoped 2026-10-08.** Pin `aa2d8b3`, port checker at **6904 identical
(313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6940 checked)**
after the head landed (see
[TOPIC-qexp-rationality-degree-head.md](TOPIC-qexp-rationality-degree-head.md)
§10). The head's landed record is
[SET-R-A](SET-R-A.md),
[SET-R-B](SET-R-B.md),
[SET-R-C](SET-R-C.md).

## 1. Which nodes the landing actually unblocked (correction to head §10)

The ready shelf of
`frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --rank-by silo --ready`
fell **89 → 86**: the five targets left the shelf and **exactly two** successors
entered it. Method: for every node of the target's unported demand whose own
demand is itself, intersect its premise closure with the five landed headlines.
Two nodes meet one, and both are on the shelf:

| successor | unblocked by | silo (`S_` lines) |
|---|---|---:|
| `ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even` | SET-R-A target 1 | 583 |
| `ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed` | SET-R-C target 5 | 326 |

**Correction.** The head's §10 originally named
`ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring` as a
second successor. It is ready, but its sole premise
`AlgebraicCurve.finiteDimensional_adjoin_of_transcendental` was *already ported*,
so it was ready before this head and is a pre-existing shelf head, not a
successor. It is scoped below anyway (§4) because it is the next largest ready
node in the same family.

## 2. The three nodes at a glance

| | successor 1 | successor 2 | sibling |
|---|---|---|---|
| headline | `exists_isIntegralQExp_smul_atkinLehnerSlash_of_even` | `exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed` | `finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring` |
| `S_` lines / declarations | 583 / 59 | 326 / 15 | 557 / 26 |
| substitutions already in port | **19** (163 lines) | 0 | 0 |
| of those port-`private` | **16 (137 lines, all in `Gamma0Integral.lean`)** | 0 | 0 |
| theorem premises | target 1 (+ 2 public) | target 5 (+ 3 public) | `AlgebraicCurve.finiteDimensional_adjoin_of_transcendental` |
| hub touch needed | **yes** (§3) | no | no |
| union budget (`port_plan`) | — | 1,232 net new lines / 100 declaration groups / 0 suspect substitutions | — |

All three are node-ready: each needs only its own proof.

## 3. Successor 1 — the Atkin–Lehner slash integrality (**hub decision required**)

```lean
theorem ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even (M ℓ : ℕ) [NeZero M]
    [NeZero ℓ] {k : ℤ} (hk : Even k)
    (f : ModularForm ((Gamma1 M ⊓ Gamma0 (M * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (p₁ : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp
        ((D : ℂ) • fun τ => ((⇑f : ℍ → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ)) p₁
```

**Mathematics.** The `ℓ ∣ γ 1 1` diamond condition from target 1 again, now with
integrality instead of rationality: slashing an integral `Γ₁(M) ⊓ Γ₀(Mℓ)`-form by
`γ` and pushing through the Atkin–Lehner/diamond operator `heckeDiagMatrix ℓ`
keeps an integral `q`-expansion up to one global positive integer `D`. It is the
`IsIntegralQExp` companion of SET-R-A's rationality pair and would be reused by
the mod-`p` weight-one machinery.

**Everything it imports is landed**: target 1, `exists_isIntegralQExp_smul_of_ratCast_qExpansion`
(public, from the C′ work), `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul`,
`Def_ModularCurve_X1`, `Def_ModularForm_HeckeOperator`. Its block is 31
declarations / 386 once / 223 in port; the big new items are `isRat_slash_mul`
(61), `isRat_alForm` (31), `conj_T_pow_mem` (30), `exists_weights` (27),
`IsRat.of_mul_eq` (26), `cardK` (23), `conj_mem_Gamma1` (18). Some are **already
public in `RationalityDvd.lean`** (`conj_mem_Gamma1` at line 485, `conj_T_pow_mem`)
and must be reused, not re-proved.

**The hub question.** Sixteen of the target's declarations are byte-identical to
`private` rows of `ModularForms/WeightOne/Gamma0Integral.lean` (137 lines). The
`port_advise` rows are:

| row | lines | content call |
|---|---:|---|
| `exists_weights` | 27 | **real** — weight bookkeeping `k + 4a + 6b = 12m`, used to raise weight; a later theory would want it |
| `of_mul_eq` | 26 | **real** — the multiplicativity that makes `IsRat` a ring-closure |
| `conj_mem_Gamma1` | 18 | **already public** in `RationalityDvd.lean:485`; reuse |
| `isRat_iff_exists_map` | 9 | **real** — the `ℚ[[q]]`-vs-`ℂ[[q]]` bridge |
| `isRat_E4`, `isRat_E6` | 7, 7 | **real** — rationality of `E₄`/`E₆` expansions |
| `mul`, `pow` | 6, 5 | **real** — `IsRat` closure |
| `levelOne_smul` | 7 | glue (slash of a level-one form) |
| `qExpansion_Eaux`, `constantCoeff_E4/E6/Eaux`, `isRat_Eaux`, `Eaux`, `IsRat` | 2–6 | glue / one-line defs |

**Caveat found while scoping: `Gamma0Integral.lean` carries the block more than
once.** Three inner namespaces hold a prelude of the same-looking names; measured
pairwise (declaration name + statement):

| pair | common names | identical | different |
|---|---:|---:|---:|
| `GammaNBounded` (99 decls) vs `X1DiamondRationalForms` (43) | 4 | **0** | 4 |
| `GammaNBounded` vs `X1BoundedDenominators` (38) | 7 | 2 | 5 |
| `X1DiamondRationalForms` vs `X1BoundedDenominators` | 21 | **17** | 4 |

So the three are **not** one duplicated block. `GammaNBounded`'s `IsRat` is a
different formulation (`∃ p : PowerSeries ℚ, p.map … = φ` against
`∀ n, ∃ r : ℚ, …`), and all four of its overlaps with `X1DiamondRationalForms`
differ; it is a different development, not a copy. The genuinely redundant pair
is `X1DiamondRationalForms` vs `X1BoundedDenominators`: **17 statement-identical
rows** (15 of them body-identical too; `exists_weights` and `isRat_Eaux` differ
only in proof), against 4 genuinely different rows
(`constantCoeff_Eaux`, `exists_E1`, `of_mul_eq` — the port's is `IsBdd.of_mul_eq`,
`qExpansion_Eaux`).

**Done, 2026-10-08 (manager's hub edit).** The sixteen statement-matching rows
above were promoted in `Gamma0Integral.lean`'s
`WLightS10.S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.X1DiamondRationalForms`
namespace — not the seven-plus-`IsRat` of the recommendation: the consumer must
import the hub for the content rows anyway, so keeping the glue rows `private`
decouples *nothing*, and promoting all sixteen avoids re-deriving 137 lines. The
pin's Atkin–Lehner `S_` file was appended to `SOURCES` to verify them. Checker
**6904 → 6920 identical, 0 mismatched, 0 missing** (+16); tier 1 green (36 s) and
the dependent wave green (**9,231 jobs**).

**The 17-row duplicate was then collapsed** (same session). The
`X1BoundedDenominators` copies were deleted (96 lines) and the namespace now
`open`s `X1DiamondRationalForms`, so its consumers resolve to the public copies.
The four genuinely different rows and the whole `GammaNBounded` block stay. The
module is **2,349 → 2,253 lines**, and rebuilds in **36 s → 15 s**; the checker is
unchanged (only `private` declarations were removed, and the public surface is
identical: still **6920 / 0 / 0** at that point), and the re-run dependent wave is
green (**9,234 jobs**). The first cut attempt used declaration-to-next-declaration
spans and severed `end Level`/`section` markers; the working cut delimits each
declaration at the next column-0 command (`DEF_BODY_CMD_RE`).
`RationalityDvd.conj_mem_Gamma1` is untouched.

## 4. The sibling — Deuring's degree inequality over a valuation subring

```lean
theorem ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    {k : Type*} [Field k] (π : A →+* k)
    (Γ : Subgroup (SL(2, ℤ)))
    (hF : ∃ t : LaurentBaseChange L (qExpFunctionFieldC ℚ Γ), Transcendental L t ∧ FiniteDimensional …)
    (a b : PowerSeries ℤ) (X : …) (hX : …) (x : qExpFunctionFieldC k Γ) (hx : …) (htr : Transcendental k x) :
    FiniteDimensional (adjoin k {x}) (qExpFunctionFieldC k Γ) ∧
      finrank (adjoin k {x}) (qExpFunctionFieldC k Γ) ≤ finrank (adjoin L {X}) (laurentBaseChange L …)
```

**Mathematics.** The elementary half of Deuring's reduction theory: the degree of
the reduced `q`-expansion function field over `k(x)` is bounded by the degree
upstairs over `L(X)`. No integral model and no good-reduction hypothesis; the
valuation subring `A` and `π` are inert data. The comparison is carried by the
shared integral series pair `a/b`.

**Clean.** One direct premise, already ported; 26 declarations / 557 lines, **0
substitutions** — nothing to reuse and nothing hub-`private` to reach. The big new
items are `main` (111), `card_le_finrank_of_linearIndependent` (89),
`transcendental_upstairs` (64), `exists_reduced_relation` (61),
`exists_polynomial_of_not_linearIndependent` (35).

## 5. Successor 2 — finiteness over `K(j)` for algebraically closed `K`

```lean
theorem ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K]
    (Γ : Subgroup (SL(2, ℤ))) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    ∃ x : qExpFunctionFieldC K Γ,
      (x : LaurentSeries K) = jqModC K ∧ Transcendental K x ∧
      FiniteDimensional (adjoin K {x}) (qExpFunctionFieldC K Γ)
```

**Mathematics.** The `q`-expansion model of `X(Γ)` over an arbitrary algebraically
closed field is a one-variable function field generated by `j(q)`: it takes the
residue-field theorem (our target 5, for characteristic `p`) and spreads it to all
algebraically closed `K` by extending the constants. It is what makes the
curve-theoretic treatment of modular curves available over `𝔽̄_p`.

**Clean, 15 declarations / 326 lines, 0 substitutions.** It cites target 5 plus
three already-ported premises. The big new items are `transfer` (114),
`isAlgebraic_residueField` (57), `map_mem_adjoin` (15), `image_intFormRatiosC`
(14). **One risk to hand-check**: its pin `S_` file imports
`Definitions/Def_ModularCurve_X0ModL.lean`, the deliberately-unported definition
module; the head's §3 recorded that target 5 needs only two of that file's 20
declarations, but this file may reach more. Resolve the import list before
dispatch.

## 6. The cut — one set, SET-R-D

The §3 hub edit is done, so the gate is gone: all three nodes go into **one set**,
[SET-R-D.md](SET-R-D.md), with three orders in dependency order. They share no
premises with each other, so the order is only a build-economy choice — cheapest
first, and the Atkin–Lehner one last since it is the largest and reads the
promoted hub:

| order | module | headline | `S_` lines |
|---|---|---|---:|
| 1 | `ModularCurve/Defs/QExpValuationReduction.lean` | `finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring` | 557 |
| 2 | `ModularCurve/X1/FunctionFieldIsAlgClosed.lean` | `exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed` | 326 |
| 3 | `ModularCurve/X1/IsIntegralAtkinLehner.lean` | `exists_isIntegralQExp_smul_atkinLehnerSlash_of_even` | 583 |

Total: 100 declarations / 1,232 net new lines. Orders 1–2 are pure new (no
substitutions, no hub); order 3 imports the promoted `X1DiamondRationalForms`
engine (§3) and `RationalityDvd`'s public prelude. The module paths are the
reviewer's proposal — the implementer may re-home a node if the mathematics
admits a leaf-side home, per the playbook's host rule, but must record it.
