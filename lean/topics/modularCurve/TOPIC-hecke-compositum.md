# The Hecke-compositum degree — one body, two headlines

**Status: ground landed, body dispatched (2026-10-21).** The two `ModularCurve` nodes
`relfinrank_xHHeckeCompositum_eq_mul` (994 pin lines) and `relfinrank_x1HeckeCompositum_eq_mul`
(884) compute the degree of the Hecke compositum — the roof `FF(GA) ⊔ qℓ(FF(GB))` over the
ℓ-stretched base — and they are the **consumers of the `RelIndex` pair** landed immediately
before them: `main_C` calls both of that set's headlines. This note records why *one* of them is
ported and the other is a fifteen-line corollary.

Order: [WORKORDER-RI2-hecke-compositum.md](WORKORDER-RI2-hecke-compositum.md). Methods:
[../TOPIC-dedup-refactoring.md](../TOPIC-dedup-refactoring.md). Pin `aa2d8b3`.

## 1. The two nodes

| node | pin lines | decls | shelf |
|---|---:|---:|---|
| `ModularCurve.relfinrank_xHHeckeCompositum_eq_mul` | 994 | 75 | `needed 4`, hops 1 |
| `ModularCurve.relfinrank_x1HeckeCompositum_eq_mul` | 884 | 70 | `needed 4`, hops 1 |

Both say: with `FF K Γ := qExpFunctionFieldC K Γ`, `Γb` a level, `GA := Γb ⊓ Γ₀(Mℓ)`,
`GB := Γb ⊓ Γ₀(Mℓ')`, `QQ := qℓ(FF K Γb)` and `roof := FF K (GA) ⊔ qℓ(FF K (GB))`,

```
relfinrank (bc QQ) (bc roof) = relfinrank (bc (FF K Γb)) (bc (FF K GB))
                              * relfinrank (bc QQ) (bc (FF K GA))
```

— the roof's degree over the ℓ-stretched base factorises, because the roof's generator
`θ = j(q^{ℓMℓ'})` has degree ≤ the index `[Γb : GB]` (the `relIndex` bound of the previous set)
and the roof over `QQ` has degree ≤ `[GA : Γ₀(ℓMℓ')]` (the `relrank` bound), with the reverse
inequality from the tower law.

## 2. They are exact twins

`shapes.py` on the `x1` file: **all 61** theorem/lemmas have a same-shape twin in another pin file,
which is the `xH` file. By section:

| section | `x1` | `xH` |
|---|---:|---:|
| `Groups` | 239 | 351 |
| `Field` (generic) | 114 | 114 |
| `Laurent` | 134 | 134 |
| `Main` (`anSet`/`AA`/`FF`/`conj_hyp`) | 121 | 118 |
| `Fields` (abbrevs) | 26 | 26 |
| `OverC` (`main_C`) | 96 | 96 |
| `BaseChange` (`main_L`) | 74 | 74 |
| `solution` | 38 | 38 |

≈ 1,000 of the 1,878 lines are the same text twice, the difference being the group
(`CohCarrier.GammaH M H` ↝ `Gamma1 M`) and the three function fields built from it.

## 3. The finding: the `x1` theorem is the `xH` theorem at `H := ⊥`

`CohCarrier.GammaH M H` is `{γ ∈ Γ₀(M) : γ₁₁ ∈ H}`, so at the trivial subgroup it is `Γ₁(M)` —
and the port has that: **`CohCarrier.GammaH_bot : CohCarrier.GammaH M ⊥ = Gamma1 M`**
(`ModularForms/Defs/GammaH.lean:137`, public, landed with the `Γ_H` definition layer long before
this cut). The three field objects follow by `rfl`:

* `xHFunctionFieldC K M ⊥ = x1FunctionFieldC K M` (both `qExpFunctionFieldC K _`),
* `xHTopFunctionFieldC K M ⊥ t = x1x0FunctionFieldC K M t`,
* hence `xHFunctionField M ⊥ = x1FunctionField M` and the `Top`/`x0` pair likewise.

So the `x1` headline is `relfinrank_xHHeckeCompositum_eq_mul L M ⊥ ℓ ℓ' hℓ` after `simp only
[GammaH_bot, xHFunctionFieldC, x1FunctionFieldC, xHTopFunctionFieldC, x1x0FunctionFieldC]`. **The
`x1` pin file's 884 lines are not ported**: it is a cross-check for the reading, not a source.

That is the largest single dedup the column has made — 884 lines to ~15 — and it is *not* a
statement deviation: the checker verifies each headline against its own wrapper, and a proof that
instantiates a more general theorem verifies like any other.

## 4. The ground, and the four handoffs

Per the user's direction, the ground went **into the legacy modules**, not into new ones beside
them, and each module was moved off the frozen registry onto its own `spec-pin:` wire (the
`JqIntegralRatios` precedent of the previous set):

| module | gained | checker |
|---|---|---|
| `ModularCurve/Defs/Laurent.lean` | `qExpAlg` + `_apply`, `coe_qExpAlg`, `adjoin_qExpand_image`, `charZero_of_algebraRat`, `coeffEmb_apply`, `powerSeries_map_map` | **45 ok / 0 / 0** |
| `ModularCurve/JqIntegralRatios.lean` | `map_ofPowerSeries`, `coeffEmb_intSeriesC`, `intSeriesC_eq_zero_iff`, `coeffEmb_image_intFormRatiosC` | **27 ok / 0 / 0** |
| `ModularCurve/Degree/LaurentGlue.lean` | `laurentBaseChange_map`, `_sup`, `_qExpFunctionFieldC` | **11 ok / 0 / 0** |
| `ModularCurve/Degree/Relfinrank.lean` | `RelFinrankKit` (ten `IntermediateField.relfinrank` lemmas) + `relfinrank_laurentBaseChange_eq` | **14 ok / 0 / 0** |

The split is forced by the import graph and is also the right subject split: the ring maps and
their coefficient lemmas in `Defs/Laurent` (which owns `qExpand`/`coeffMap`/`coeffEmb`), the
`intSeriesC`-facing half in `JqIntegralRatios` (which owns `intSeriesC`/`intFormRatiosC`), the
`laurentBaseChange` transport in `LaurentGlue` (which owns `laurentBaseChange_adjoin`), and the
relative-degree toolkit in `Relfinrank` (which owns `relfinrank_laurentBaseChange`).

The whole wired surface after the four handoffs: **3,904 ok, 0 mismatch, 0 missing, 11 own, 0 kw
over 154 modules**, 577 `PORT_FILES` exempt (`spec/check_port.py --all`, every module re-checked
from scratch) — was 3,830 / 151 / 580. The +74 is 45 + 14 + 11 (the three newly wired modules) plus
4 (the declarations `JqIntegralRatios` gained); the three modules that left `PORT_FILES` are why the
exempt count drops. No wave build was run: the promotions and the appends change no proof term, and
the statement hash is the evidence.

Two of the ten toolkit lemmas are mathlib's (`relfinrank_mul_relfinrank`, `relfinrank_map_map`); the
other eight are new, and `relrank_adjoin_insert_eq` is the one that matters most — it converts the
`relrank (adjoin F S) (adjoin F (insert x S))` shape that
`relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` concludes in into a `Module.finrank`, which is
what makes the two bounds composable.

`laurentBaseChange_map`/`_sup` had to wait for `JqIntegralRatios`'s olean to be rebuilt (the
`WeightOne` chain was missing oleans — residue of an earlier killed build); the fix was one
single-module build, not a wave.

## 5. The landing: one module, two headlines

`ModularCurve/HeckeCompositum.lean` — 840 lines, 47 declarations, **two public headlines**
(`relfinrank_xHHeckeCompositum_eq_mul`, 994-pin-line development; `relfinrank_x1HeckeCompositum_eq_mul`,
the six-line `H := ⊥` corollary), the engine private in `namespace XHHeckeSol`. Checker
**2 ok / 0 mismatch / 0 missing / 0 own / 0 kw**; axioms `[propext, Classical.choice, Quot.sound]`
on both.

**No separate `x1` module, and no façade module.** The first placement tried was a
`X1/HeckeCompositum.lean` holding the corollary and nothing else — a whole module for six lines,
which is the pattern to stop. The second was the corollary in
`X1/FunctionFieldDegree.lean`, its subject home; that forces this module's import into an X₁
degree module, and the edge is not free: it changed what `coeffEmb_intSeriesC` resolves to inside
an unrelated proof there (the `Defs/Laurent`/`JqIntegralRatios` ground now publishes that name at
`ModularCurve` scope), and an existing `simp only` stopped making progress. The theorem is a
specialisation of the `xH` one, so it belongs **with it**, in the module that carries the
development — one module for the whole subject, two headlines. The module is named for the
subject (`ModularCurve/HeckeCompositum.lean`), not for one of the two levels.

Price: **840 lines** for 1,878 pin lines (≈ 55 % saved), checker **+2**, and the two headlines are
the only consumers of the previous set's theorems — that ground pays for itself one node later.

## 6. Residue

* the pin's `X1LDGroups` block (239 lines) is a sub-block of `XHLDGroups` (351); the body
  transcribes the `Γ_H` version and the `Γ₁` lemmas it needs, so ~239 lines are still written
  twice — but *once in the port*, not twice;
* `charZero_of_algebraRat` and `powerSeries_map_map` also exist `private` in
  `X1/FunctionFieldBaseChange.lean` and `ModularForms/WeightOne/Gamma0Integral.lean`; now public in
  `Defs/Laurent`, the two private copies can be deleted by whoever opens those modules next;
* `coeffEmb_intSeriesC` likewise exists public-but-elsewhere (`X1/FunctionFieldResidue.lean`,
  `ModularCurve.QExpDeuring`); the `Defs/Laurent` copy is the one wired.
