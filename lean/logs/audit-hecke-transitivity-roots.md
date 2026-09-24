# Audit — Hecke-matrix theorems and transitivity of the roots of `Φ_ℓ`

Read-only audit. Sources: FLT clone `/home/haitao/proj/fermats-last-theorem` at
`aa2d8b3`; port `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/FLTForHuman/`.
Question: can the Hecke-matrix side prove *transitivity of roots* by simple group
theory, replacing the manipulations in
`lean/FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` (T12, the
895-line block)?

**Verdict in one line.** The Hecke-matrix layer is present and is already used —
but it supplies **permutation and invariance of the coset labels/functions**, not
the **transitivity of the conjugates under `Aut_{ℚ(j)}`** that an
"irreducible-by-transitivity" argument needs, and no transitivity theorem for the
`redMatrix` action exists in the pin, the port or mathlib. So it does not replace
the T12 manipulations as things stand. The pin's own cheaper route past the
root-counting is a **degree** argument (`minpoly.irreducible`), not a group
action; §4.

---

## 1. What "transitivity of roots" has to mean

The roots in question are the `ℓ + 1` conjugates

```
conj ℓ ζ 0        = j(q^{ℓ²})         (PhiGen.conj_zero)
conj ℓ ζ (b+1)    = j(ζ^b q)          (PhiGen.conj_succ)
```

and the target is `PhiIrreducible data` = `Irreducible data.toAdjoin`
(`Def_ModularCurve_PhiGen.lean`, the `PhiIrreducible` def). The standard
"group theory gives irreducibility" lemma is:

> `f` separable over `F`, `L` its splitting field; if a subgroup
> `G ≤ L ≃ₐ[F] L` acts transitively on the roots of `f`, then `f` is irreducible
> over `F` — the minpoly of a root has the whole `G`-orbit among its roots, and
> transitivity makes that orbit everything.

So the transitivity has to be by **`ℚ(j)`-automorphisms of the splitting field**
— equivalently by the deck group of the cover `X(ℓ) → X(1)`, i.e.
`PSL₂(𝔽_ℓ)` acting on `ℙ¹(𝔽_ℓ)` (the `ℓ+1` cosets). Nothing weaker proves
irreducibility.

The Hecke/coset transitivity that *is* available is on the **other** side:
`SL₂(ℤ)` permutes the `ℓ + 1` coset representatives `heckeRep ℓ x`
(`x : OnePoint (ZMod ℓ)`). That is a statement about *functions of `τ`* and
*coset labels*, not about `ℚ(j)`-automorphisms of the coefficient field. The two
transitivities are different objects; §3.

---

## 2. The Hecke-matrix layer we have

Port locations (`FLTForHuman/…`); the pin's copy is
`Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:82–455` plus the five
`S_ModularForm_hecke*` files.

| what | port | content |
|---|---|---|
| matrices | `ModularForms/Defs/HeckeOperator.lean:41,50,54` | `upperTriangularGL`, `heckeMatrix p j = !![1,j;0,p]`, `heckeDiagMatrix p = !![p,0;0,1]` |
| operators | `…/Defs/HeckeOperator.lean:136,139` | `heckeU k p`, `heckeT k p`, `heckeT_eq_heckeU_add` |
| q-coefficients | `…/Defs/HeckeOperator.lean:205,208` | `coeffHeckeT`, `coeffHeckeU` |
| coset stability | `…/Defs/HeckeRepresentatives.lean:66,83,100,117` | `heckeMatrix_mul_of_eq(')`, `heckeDiagMatrix_mul_of_eq(')`: `hecke* * mapGL g = mapGL g' * hecke*` |
| `U`/`T` as sums | `…/Defs/HeckeRepresentatives.lean:138,146,157,163,181` | `sum_range_eq_sum_zmod`, `heckeU_eq_sum_zmod`, `unit_of_apply_one_zero_eq_zero`, `affinePerm`, `heckeMatrix_mul_of_dvd` |
| **`ℙ¹` action** | `…/Defs/HeckeRepresentatives.lean:226,242,271` | `heckeRep p x`, `redMatrix g` (transpose-inverse mod `p`), **`heckeRep_mul`** |
| slash invariance | `…/Defs/HeckeRepresentatives.lean:198,233,331` | `heckeU_slash_mapGL`, `heckeT_eq_sum_onePoint`, `heckeT_slash_mapGL` |
| analytic translates | `ModularForms/HeckeQExpansion.lean:37,69` | `hasSum_qParam_heckeMatrix_smul`, `hasSum_qParam_heckeDiagMatrix_smul` |
| the one consumer | `ModularForms/PhiGenDescends.lean:87,118,126,143` | `apply_heckeRep_smul_smul`, `cosetPoly_eq_prod_onePoint`, `cosetPoly_smul'`, public `cosetPoly_smul` |

The load-bearing statement is `heckeRep_mul` (with `N = 1`, its `N`-divisibility
hypothesis is vacuous):

```
∃ g' : SL(2, ℤ), heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x)
```

i.e. the coset system is stable under right multiplication and `redMatrix g`
permutes the labels. `cosetPoly_smul` then closes by
`Equiv.prod_comp (MulAction.toPerm (redMatrix p g))`: **a reindexing of an
invariant product**, not transitivity.

mathlib supplies the underlying action and its two evaluation lemmas only:
`OnePoint.instGLAction`, `OnePoint.smul_infty_eq_ite`, `OnePoint.smul_some_eq_ite`
(`Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean:126,140,149`).
There is **no** `MulAction.IsPretransitive` for `GL(2,K)` on `OnePoint K` in
mathlib, and mathlib has `SpecialLinearGroup.map (Int.castRingHom (ZMod N))`
(`Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean:30`) but **not** its
surjectivity `SL(2,ℤ) ↠ SL(2,𝔽_ℓ)`.

---

## 3. Why the Hecke action is not the needed transitivity

1. **No transitivity statement exists.** `heckeRep_mul` gives
   "`g` permutes the labels", not "for all `x y` there is `g` with
   `redMatrix g • x = y`". The missing inputs are (i) transitivity of
   `SL(2,𝔽_ℓ)` on `ℙ¹(𝔽_ℓ)` and (ii) surjectivity of reduction
   `SL(2,ℤ) → SL(2,𝔽_ℓ)` (Smith normal form / elementary matrices), neither of
   which is in the pin, the port, or mathlib.
2. **The available automorphisms are not `ℚ(j)`-linear.** `qTwist (ζ^b)` is a
   ring automorphism of `LaurentSeries K`, and by `qTwist_qExpand` fixes
   `j(q^ℓ) = qExpand ℓ (coeffEmb jq)` (since `ζ^{bℓ} = 1`) while moving
   `j(q) = coeffEmb jq` to `conj ℓ ζ b.succ`. So it fixes `ℚ(j(q^ℓ))`, **not**
   `ℚ(j)`. The Fricke automorphism `frickeInvolutionFull ℓ`
   (`Defs/AtkinLehner.lean:70`) is a `ℚ`-algebra automorphism but swaps the two
   generators (`IsFrickeAut`: `σ jq = jqN`, `σ jqN = jq`,
   `Defs/AtkinLehner.lean:34,62`), so it also does not fix `ℚ(j)`. The desired
   group — the deck group of `X(ℓ) → X(1)`, whose fixed field is `ℚ(j)` — is not
   constructed anywhere.
3. **The deck group cannot even be stated yet.** The port's largest field here is
   `modularFunctionFieldFull ℓ = ℚ(jq, jqN)` — the function field of `X₀(ℓ)`,
   two generators. The Galois closure `X(ℓ)` (all `j((τ+b)/ℓ)` and `ζ_ℓ`) is not
   defined, and neither is `PSL₂(𝔽_ℓ) → Aut_{ℚ(j)}(·)`. That bridge is the
   monodromy / Riemann-existence step the notes already rule out as a *cheap*
   substitute.
4. **Circularity if Fricke is used.** `exists_isFrickeAut` (`Analytic/FrickeAut.lean:287`)
   is *built from* `exists_phiIrreducible_evalSymm` — i.e. from the 895 block — so
   it cannot be used to prove that block's results. The independent analytic
   Fricke lives in `ModularForms/HeckeFricke.lean` (slash relations on forms),
   not as a `ℚ(j)`-automorphism of the splitting field.

---

## 4. What T12 actually consumes, and the pin's existing alternatives

The 895 block proves: `conj_injective`; the Vieta/coeff refutation
`aeval_jq_ne_jqN` → `jqN_not_mem_adjoin_jq` (uses `one_le_coeff_jq`, the 386-line
eta-product module); `phiIrreducible_of_splits` by factor counting;
`swapBivar_monic_of_coeff_bounds` / `transposeToAdjoin_monic_of_qExpansion`
(pole bounds); and the symmetry layer `evalSymm_of_irreducible` /
`evalSymm_of_splits`.

The pin has a second, non-group-theoretic route to **irreducibility**:

* `phiIrreducible_all` (`S_ModularCurve_phiIrreducible_all.lean:397`) — for any
  datum at any level: `data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN N)` by matching degrees,
  then `minpoly.irreducible`. **No `conj_injective`, no Vieta refutation, no
  factor counting.** Its degree input is `finrank_adjoin_jqN_eq_dedekindPsi`
  (the FFG slot/coset-product route, `minpoly_jqN_map_eq_prod_slots`).

But that route is **not independent of the cone**: the integrality input
`exists_monic_evalAtJ_jqN_eq_zero` imports
`Thm_ModularCurve_exists_phiIrreducible_evalSymm`
(`P2M/Sol/S_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean:2,86`), and the
port mirrors this (`FunctionFieldGeneration/Capstone.lean:126`). Likewise the
slot-symmetry route to `EvalSymm` still needs the block's
`swapBivar_monic_of_coeff_bounds` (`evalSymm_of_squarefree.lean:412`,
`evalSymm_of_one_lt.lean`, `evalSymm_of_irreducible.lean`).

Port status:

| pin theorem | port |
|---|---|
| `exists_phiIrreducible_evalSymm` (cone, T12) | ✅ `ModularPolynomialProperties.lean:138` |
| `exists_phiIrreducible_of_finrank_eq` / `exists_phiIrreducible` | ✅ `FunctionFieldGeneration/Capstone.lean:169,277` |
| `minpoly_jqN_map_eq_prod_slots` (the coset/slot product) | ✅ `FunctionFieldGeneration/SlotProduct.lean:1084` |
| `phiIrreducible_all`, `phiIrreducible_of_prime` | ❌ absent |
| `evalSymm_of_prime`, `evalSymm_of_one_lt`, `evalSymm_of_squarefree` | ❌ absent |
| `swapBivar_monic_of_coeff_bounds`, `transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_irreducible` | ✅ (written once, in `ModularPolynomialIrreducible.lean:805,893,767`) |

---

## 5. If the group-theoretic route is pursued anyway

The minimal honest development is:

1. **`redMatrix` transitivity.** For `x y : OnePoint (ZMod p)` produce
   `g : SL(2,ℤ)` with `redMatrix p g • x = y`. Direct construction is short
   (map `∞` to a point, or fix `∞` via the Borel `[[1,t],[0,1]]`); it does not
   need `SL(2,ℤ) ↠ SL(2,𝔽_ℓ)` if the cases are handled explicitly. This is the
   only piece that is genuinely "simple group theory".
2. **The missing bridge.** A `ℚ(j)`-algebra homomorphism
   `PSL₂(𝔽_ℓ) → (splitting field ≃ₐ[ℚ(j)] splitting field)` compatible with the
   `redMatrix` action on the labels — i.e. the deck group of `X(ℓ) → X(1)`. This
   is the real work, and it is not in any of the three code bases.
3. **Distinctness.** `conj_injective` (already in T12) or the `q⁻¹`-coefficient
   separation used by `sv_inj` in the slot product.

Only after (2) does "separable + transitive `Aut_{ℚ(j)}` action ⟹ irreducible"
apply. `qTwist`/`redMatrix`/`frickeInvolutionFull` alone give (1) and (3), not
(2).

---

## 6. Recommendation

* If the goal is to **shorten the port**, the lever is the degree route, not
  group theory: port `phiIrreducible_all` and `evalSymm_of_prime`, and route
  `exists_monic_evalAtJ_jqN_eq_zero` through T11's plain datum
  (`exists_modularPolynomialData_coeff_eq`) instead of T12's
  `exists_phiIrreducible_evalSymm`, so that `aeval_jq_ne_jqN`,
  `jqN_not_mem_adjoin_jq` and `one_le_coeff_jq` drop off the critical path. The
  block's transpose/pole-bound half (`swapBivar_monic_of_coeff_bounds`) has **no**
  substitute and must stay.
* If the goal is a **conceptual** group-theoretic proof, the deliverable to
  build first is the full-level function field `X(ℓ)` and its deck group over
  `ℚ(j)`; the Hecke-matrix side is necessary but not sufficient.
