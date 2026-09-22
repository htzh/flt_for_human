# Audit — mathlib replacement opportunities for the slot-counting block

**Block audited:** `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` L405–L703
(299 lines), FLT pin `fermats-last-theorem@aa2d8b34`.
**Port under construction:** `lean/FLTForHuman/`, pinned mathlib at
`lean/.lake/packages/mathlib` (mathlib4 for Lean `v4.34.0`;
`lean/lean-toolchain` = `leanprover/lean4:v4.34.0`).
**Method:** read-only; every lemma below was opened in the pinned tree.

---

## 0. Verdict (short)

- There is **no** mathlib lemma that states the Γ₀(n) index formula, and
  **`dedekindPsi` does not exist anywhere in mathlib** (whole-tree grep, 0 hits).
  So the *endpoint* statement `slots n = dedekindPsi n` cannot be delegated.
- There **is** a real win of roughly **120–160 of the 299 lines**, split in two:
  1. the multiplicativity machinery `slotAt_mul` + `gcd_mul_*` + part of
     `slots_mul` (≈137 lines) is replaceable by a *closed form* for `slotAt`
     (`(d / gcd (n/d) d) * φ (gcd (n/d) d)`) plus mathlib's
     `Nat.Coprime.divisors_mul` and a 24-line `h_mul` — net **≈80–100 lines**;
  2. `dedekindPsi_prime_pow'`, `dedekindPsi_prime`, `dedekindPsi_pos`,
     `dedekindPsi_mul_prime_not_dvd`, `dedekindPsi_mul_prime_dvd` (64 lines) are
     verbatim re-proofs of FLT theorems that are **already public** — net
     **≈55–60 lines**.
- The prime-power half (`slotAt_prime_pow_mid`, `slots_prime_pow`) is *already*
  mathlib-driven and near-minimal; do not rewrite it away.
- The block also contains a **duplicate** of the port's `Spine.lean:179–201`
  `dedekindPsi_mul_prime_*` pair; the port should carry these once.

---

## 1. The block as written (line budget)

| declaration | span | lines |
|---|---|---|
| `slotAt` | 405–406 | 2 |
| `slots` | 408 | 1 |
| `slotCond_eq` / `slotCond_iff` | 410–416 | 7 |
| `gcd_eq_of_modEq` | 418–421 | 4 |
| `slotCond_mod_iff` | 423–426 | 4 |
| `slotAt_one` / `slotAt_self` | 428–434 | 7 |
| `slotAt_prime_pow_mid` | 436–452 | 17 |
| `slots_prime_pow` | 453–465 | 13 |
| `dedekindPsi_prime_pow'` | 466–485 | 20 |
| `slotAt_mul` | 486–593 | 108 |
| `gcd_mul_left_of_dvd` / `gcd_mul_right_of_dvd` | 594–610 | 17 |
| `slots_mul` | 612–640 | 29 |
| `slots_eq_dedekindPsi` | 641–659 | 19 |
| `dedekindPsi_pos` | 660–665 | 6 |
| `dedekindPsi_prime` | 666–674 | 9 |
| `dedekindPsi_mul_prime_not_dvd` | 675–679 | 5 |
| `dedekindPsi_mul_prime_dvd` | 680–703 | 24 |
| **total** | **405–703** | **299** |

---

## 2. Question 1 — is there a shorter mathlib route to `slots n = dedekindPsi n`?

### 2.1 `dedekindPsi` in mathlib — **absent**

```
grep -rni "dedekindpsi|dedekind_psi|dedekind psi" Mathlib/     # exit 1, no matches
```

The endpoint must stay in the port (its `Defs/Jq.lean:206` definition is the
right one; `dedekindPsi = 𝓛(μ²) · id` in `ArithmeticFunction` language, which the
port already exploits at `Jq.lean:266–292`).

### 2.2 `Nat.totient`, `Nat.card (ZMod n)ˣ`, `ZMod.card_units`

| lemma | path:line | statement |
|---|---|---|
| `Nat.totient_eq_card_coprime` | `Mathlib/Data/Nat/Totient.lean:51` | `φ n = #{a ∈ range n \| n.Coprime a}` |
| `Nat.filter_coprime_Ico_eq_totient` | `Mathlib/Data/Nat/Totient.lean:80` | `#{x ∈ Ico n (n+a) \| a.Coprime x} = φ a` |
| `Nat.periodic_coprime` | `Mathlib/Data/Nat/Periodic.lean:29` | `Periodic (Coprime a) a` |
| `Nat.totient_mul` | `Mathlib/Data/Nat/Totient.lean:133` | `φ (m*n) = φ m * φ n` for `Coprime m n` |
| `Nat.totient_prime_pow` | `Mathlib/Data/Nat/Totient.lean:211` | `0 < n → φ (p^n) = p^(n-1) * (p-1)` |
| `Nat.sum_totient` | `Mathlib/Data/Nat/Totient.lean:165` | `∑ d ∈ n.divisors, φ d = n` |
| `ZMod.card_units_eq_totient` | `Mathlib/Data/Nat/Totient.lean:113` | `Fintype.card (ZMod n)ˣ = φ n` (`[NeZero n]`) |
| `Nat.card_zmod` | `Mathlib/SetTheory/Cardinal/Finite.lean:249` | `Nat.card (ZMod n) = n` |

**How the block already uses mathlib here.** `slotAt_prime_pow_mid` (L436–452)
already calls `Nat.totient_eq_card_coprime`; `slots_prime_pow` (L453–465)
already calls `Nat.sum_divisors_prime_pow` and `Nat.sum_totient`. Nothing to gain
there. `ZMod.card_units_eq_totient` counts *units of `ZMod n`*, not lattice points
`b < d`; reaching `slotAt` from it would need a `ZMod.unitsEquivCoprime` bijection
and is strictly more work than the `Finset` count. **No win from the `ZMod` route.**

The useful, un-exploited mathlib fact here is `Nat.periodic_coprime` +
`Nat.filter_coprime_Ico_eq_totient`, which give the **closed form** used in §4.

### 2.3 `Finset` counting lemmas

| lemma | path:line | statement |
|---|---|---|
| `Finset.card_bij'` / `card_nbij'` | `Mathlib/Data/Finset/Card.lean:381` / `:411` (used in block L559) | bijection counting |
| `Finset.card_product` | `Mathlib/Data/Finset/Prod.lean:141` | `#(s ×ˢ t) = #s * #t` |
| `Finset.card_sigma` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:134` | `#(s.sigma t) = ∑ a ∈ s, #(t a)` |
| `Nat.Coprime.mul_injOn_divisors` | `Mathlib/Data/Finset/NatDivisors.lean:52` | `InjOn (·.1 * ·.2)` on `divisors m ×ˢ divisors n` |
| `Nat.Coprime.divisors_mul` | `Mathlib/Data/Finset/NatDivisors.lean:65` | `divisors (m*n) = (divisors m ×ˢ divisors n).attach.map (·.1 * ·.2)` for `Coprime m n` |
| `Nat.sum_div_divisors` | `Mathlib/NumberTheory/Divisors.lean:550` | `∑ d ∈ n.divisors, f (n/d) = ∑ d ∈ n.divisors, f d` |
| `Nat.sum_divisors_prime_pow` | `Mathlib/NumberTheory/Divisors.lean:516` | divisor sum at a prime power |
| `Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime` | `Mathlib/Data/Nat/GCD/Basic.lean:256` | `Coprime n m → (gcd d n * gcd d m = d ↔ d ∣ n*m)` |

`card_biUnion` is **not** the right tool: the fibres over divisors are already
disjoint and `Finset.sum_product`/`sum_sigma` express the split more directly.
The genuinely new ingredient versus the block is **`Nat.Coprime.divisors_mul`**:
it replaces the hand-rolled `Finset.sum_bij'` + inverse `gcd` computation in
`slots_mul`, and it obsoletes `gcd_mul_left_of_dvd`/`gcd_mul_right_of_dvd`
entirely (see §4).

### 2.4 Γ₀(n) cosets / explicit index — **not in mathlib**

`Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean` contains only:

- `Gamma0` (`:79`), `Gamma0_mem` (`:90`), `Gamma0Map` (`:95`), `Gamma1'` (`:105`),
  `Gamma0_is_congruence` (`:178`), `IsCongruenceSubgroup.finiteIndex` (`:181`),
  `instFiniteIndexGamma0` (`:187`).

`Mathlib/NumberTheory/ModularForms/Cusps.lean` adds only
`strictPeriods_Gamma0` (`:435`) and `strictWidthInfty_Gamma0` (`:445`).

There is **no** `Subgroup.index (Gamma0 N) = …`, no `natCard` of a quotient, and no
`MulAction.orbitRel` index result for Γ₀. A whole-mathlib grep for
`Gamma0` together with `index|natCard|card` returns exactly lines 187–188.
So the standard coset-representative description of Γ₀(n) has to be formalised
(the port's `slots`/`primCosetReps` route is that description). **No win.**

### 2.5 `ArithmeticFunction` — already the right layer for ψ, not for `slots`

Relevant API (all in `Mathlib/NumberTheory/ArithmeticFunction/`):
`IsMultiplicative.map_mul_of_coprime` (`Defs.lean:436`),
`IsMultiplicative.eq_iff_eq_on_prime_powers` (`Defs.lean:565`),
`isMultiplicative_sigma` (`Misc.lean:202`),
`isMultiplicative_moebius` (`Moebius.lean:128`).

The port already uses this for `dedekindPsi_mul_of_coprime` (`Jq.lean:284`).
`slots` is **not** a Dirichlet convolution (`slotAt n d` depends jointly on
`gcd (n/d) d`), so it cannot be pushed through `map_mul_of_coprime` directly;
the convolution route goes through the `slotAt` closed form
(`slots n = ∑_{c² ∣ n} μ c · σ (n/c²)`) and is *not* shorter than the
closed-form + `divisors_mul` route of §4 — it buys multiplicativity but costs the
same Möbius expansion plus a `σ` computation. Use it only if the port wants the
arithmetic-function vocabulary for its own sake.

---

## 3. Question 2 — reuse the already-proved `dedekindPsi_*` lemmas

The port already proves everything needed, publicly:

| port lemma | path:line | statement |
|---|---|---|
| `dedekindPsi_prime` | `FLTForHuman/ModularCurve/Defs/Jq.lean:215` | `ψ p = p + 1` for `p.Prime` |
| `dedekindPsi_prime_pow` | `FLTForHuman/ModularCurve/Defs/Jq.lean:221` | `ψ (p^k) = p^k + p^(k-1)`, `k ≠ 0` |
| `dedekindPsi_mul_of_coprime` | `FLTForHuman/ModularCurve/Defs/Jq.lean:284` | `ψ (M*N) = ψ M * ψ N`, `Coprime M N` |

The FLT block re-derives all four `dedekindPsi_*` items from scratch
(`dedekindPsi_prime_pow'`, `dedekindPsi_prime`, `dedekindPsi_mul_prime_not_dvd`,
`dedekindPsi_mul_prime_dvd` = L466–485 and L660–703, **64 lines**). FLT itself
already publishes the exact statements as reusable theorems:

| FLT public theorem | statement | block duplicate |
|---|---|---|
| `Thm_ModularCurve_dedekindPsi_prime` | `ψ p = p + 1` | L666–674 (9) |
| `Thm_ModularCurve_dedekindPsi_prime_pow` | `ψ (p^k) = p^k + p^(k-1)` | L466–485 (20) |
| `Thm_ModularCurve_dedekindPsi_mul_prime` | `ψ (M*ℓ) = (if ℓ ∣ M then ℓ else ℓ+1) * ψ M` | L675–703 (29) |
| `Thm_ModularCurve_dedekindPsi_pos` | `N ≠ 0 → 0 < ψ N` | L660–665 (6) |

And the pin's **sibling** `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean`
L436–465 re-proves exactly the same pair (`dedekindPsi_prime'`,
`dedekindPsi_mul_prime_not_dvd`, `dedekindPsi_mul_prime_dvd`), while the port's
`FunctionFieldGeneration/Spine.lean:179–201` carries a **third private copy**.

**Concrete replacements (block-local):**

- `dedekindPsi_prime_pow' hp k` (20 lines) →
  ```lean
  rw [ModularCurve.dedekindPsi_prime_pow p (k+1) hp (Nat.succ_ne_zero k), Nat.add_sub_cancel]
  ```
  (`p^(k+1-1)` is defeq/simp to `p^k`), i.e. **1–2 lines, save ≈18**.
- `dedekindPsi_prime hp` (9) → `ModularCurve.dedekindPsi_prime hp`
  (add `import Theorems.Thm_ModularCurve_dedekindPsi_prime`; the audited file
  currently imports only `_prime_pow` and `_mul_of_coprime`), **save ≈8**.
- `dedekindPsi_mul_prime_not_dvd` + `dedekindPsi_mul_prime_dvd` (29) →
  `ModularCurve.dedekindPsi_mul_prime M ℓ hℓ` plus `if_neg`/`if_pos` at the two
  call sites (L1106, L1357), **save ≈24**.
- `dedekindPsi_pos` (6) → `ModularCurve.dedekindPsi_pos` (public FLT theorem),
  **save ≈5**.

**Subtotal: save ≈55 (range 50–60).** For the port this also means
`Spine.lean:179–201` (≈23 lines) should import the promoted pair from
`Defs/Jq.lean` instead of holding a private copy.

---

## 4. Question 3 — replace `slotAt_mul` (108 lines) with a bijection/closed form

The current 108-line `slotAt_mul` is a fibre-wise CRT: a `Finset.card_bij'`
between `b < d₁d₂` and pairs `(b % d₁, b % d₂)`, whose bulk
(`hgg`, `hg₁g`, `hg₂g`, `hfwd`, `hbwd`, ~70 lines) is the forward/backward
`gcd`-divisibility algebra. It is already a bijection argument — just an
expensive one, because the predicate `gcd (gcd (n/d) b) d = 1` has to be tracked
through `Nat.chineseRemainder`.

**Much shorter route: don't prove the fibre identity at all.** Use the closed form

```
slotAt n d = (d / gcd (n / d) d) * φ (gcd (n / d) d)          (*)
```

and multiplicativity of the right-hand side. Reusable pieces already exist in
FLT's own `S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean`:

- `card_filter_coprime_range_mul` (there L18–31, 14 lines):
  ```
  ((range (g*m)).filter (fun b => Coprime g b)).card = m * φ g
  ```
  proved by induction using mathlib `Nat.periodic_coprime` +
  `Nat.count_eq_card_filter_range` (equivalently
  `Nat.filter_coprime_Ico_eq_totient`).
- `card_fibre` (there L33–45, 13 lines): the `m = d/g` case giving exactly `(*)`.
- `h_mul` (there L132–155, **24 lines**): `h (a₁a₂, d₁d₂) = h (a₁,d₁)·h (a₂,d₂)`
  for `Coprime (a₁d₁) (a₂d₂)`, using mathlib `Nat.totient_mul`,
  `Nat.Coprime.gcd_mul`, `Nat.div_mul_div_comm`.

Then **rewrite `slots_mul` with mathlib `Nat.Coprime.divisors_mul`** instead of
the hand-rolled `Finset.sum_bij'`:

```lean
private theorem slots_mul (M M' : ℕ) (hco : Nat.Coprime M M') :
    slots (M * M') = slots M * slots M' := by
  unfold slots
  -- mathlib rewrites divisors (M*M') into attach.map of divisors M ×ˢ divisors M'
  rw [Nat.Coprime.divisors_mul hco, Finset.sum_map, Finset.sum_attach, Finset.sum_product,
      Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
  rw [← Nat.div_mul_div_comm (Nat.mem_divisors.mp hd₁).1 (Nat.mem_divisors.mp hd₂).1,
      slotAt_eq, slotAt_eq, slotAt_eq]
  exact h_mul (M / d₁) d₁ (M' / d₂) d₂
    (by rw [Nat.div_mul_cancel (Nat.mem_divisors.mp hd₁).1,
            Nat.div_mul_cancel (Nat.mem_divisors.mp hd₂).1]; exact hco)
```

Estimated ≈20–28 lines for the new `slots_mul`, plus a 1-line `slotAt_eq`
(`unfold slotAt; exact card_fibre (n/d) d` after `slotCond_iff`) and the
14 + 13 + 24 supporting lines above.

**Bonus:** once `(* )` exists, `slotAt_prime_pow_mid` (17 lines) collapses to

```
rw [slotAt_eq, Nat.pow_div hik.le hp.pos,
    Nat.gcd_eq_right (Nat.pow_dvd_pow p (by omega)), Nat.div_self (pow_pos hp.pos i), one_mul]
```

(≈6 lines), and `slotAt_one`/`slotAt_self` each shrink to ~2 lines.

**Accounting for the counting machinery (L405–659, excluding the ψ lemmas):**

| removed | lines |
|---|---|
| `slotAt_mul` | 108 |
| `gcd_mul_left_of_dvd` + `gcd_mul_right_of_dvd` | 17 |
| `gcd_eq_of_modEq` + `slotCond_mod_iff` (only used inside `slotAt_mul`) | 8 |
| old `slots_mul` | 29 |
| `slotAt_prime_pow_mid` (17→6) | 11 |
| `slotAt_one`/`slotAt_self` (7→4) | 3 |
| **added** `card_filter_coprime_range_mul` + `card_fibre` + `slotAt_eq` + `h_mul` + new `slots_mul` | −(14+13+2+24+26) = −79 |
| **net save** | **≈97 (range 80–105)** |

The claim "slotAt_mul is replaceable by a CRT bijection" is therefore **yes, but
the win comes from proving a closed form instead of the fibre bijection**; the
bijection itself is what the pin already wrote and it is not where the lines are.

---

## 5. Question 4 — does the port need `slots` / the intermediate lemmas?

Consumer evidence in the pin (the only two uses of the counting API):

- `S_ModularCurve_jqN_prime_not_mem_full.lean:1438–1457` (`hTcard` for `T`)
- `:1663–1684` (`hTcard` for `T'`)

Both use **only** `slotAt` (to unfold a filter-card into `slotAt M (M/a)`, so
that `Nat.sum_div_divisors` applies) and then `slots_eq_dedekindPsi M hM0`.
**None** of `slotAt_one`, `slotAt_self`, `slotAt_prime_pow_mid`, `slots_prime_pow`,
`slotAt_mul`, `slots_mul`, `gcd_mul_*`, `dedekindPsi_prime_pow'` is referenced
outside the block. They are internal machinery.

The port's own consumers (`FunctionFieldGeneration/Spine.lean:137–146`, the
`minpoly_jqN_map_eq_prod_slots` input shape, and `:282`) are all phrased as a
product/sum over `M.divisors` with the same filter
`(Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)`.
So the port should expose **one** lemma of that shape, e.g.

```lean
theorem card_slotFilter_eq_dedekindPsi (M : ℕ) (hM : M ≠ 0) :
    (∑ a ∈ M.divisors,
      ((Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)).card) = dedekindPsi M
```

and keep `slotAt`/`slots` as `private` helpers. In-block this is a wash
(the proof still needs the per-divisor counts), but each `hTcard` block shrinks
from ~20 lines to ~4 (the `Multiset.card_bind` + `card_slotFilter_eq_dedekindPsi`
step replaces the `map_congr`/`card_map`/`unfold`/`Nat.div_div_self` dance and the
`slotAt` indirection), i.e. **≈30 lines saved across the two consumers**.

There is an alternative endpoint already fully written in FLT:
`ModularCurve.card_primCosetReps_eq_dedekindPsi`
(`S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean`, 290 lines), where
`primCosetReps N` counts triples `(a,b,d)` with `a*d = N`, `b < d`,
`gcd a (gcd b d) = 1`. Via `gcd_rotate` those triples are exactly the consumer's
`(a,b)` pairs with `d = M/a`, so this statement is directly usable by the port's
`hTcard`. Porting that file wholesale is **not** a line win over the audited block
(290 vs. ~255 for L405–659), but it is a **single reusable statement** that both
consumers and `root_shape` can share. If the port wants one public counting lemma,
pick between:
- `card_slotFilter_eq_dedekindPsi` (the divisor-sum shape, closest to `Spine.lean`
  and to `Inputs.minpoly_jqN_map_eq_prod_slots`), or
- `card_primCosetReps_eq_dedekindPsi` (the triple shape, already pinned and
  checker-covered).

Either way, **no consumer needs the `slotAt*` intermediate lemmas**.

---

## 6. Line-delta table (positive = savings)

| # | item | action | est. Δ |
|---|---|---|---|
| 1 | `slotAt_mul` (L486–593) | delete; closed form `(*)` + `h_mul` | +108 |
| 2 | `gcd_mul_left/right_of_dvd` (L594–610) | delete (`divisors_mul` supplies injectivity) | +17 |
| 3 | `gcd_eq_of_modEq`, `slotCond_mod_iff` (L418–426) | delete (only used by `slotAt_mul`) | +8 |
| 4 | `slots_mul` (L612–640) | rewrite via `Nat.Coprime.divisors_mul` | +5 |
| 5 | `slotAt_prime_pow_mid` (L436–452) | rewrite via `(*)` | +11 |
| 6 | `slotAt_one`/`slotAt_self` (L428–434) | rewrite via `(*)` | +3 |
| 7 | new `card_filter_coprime_range_mul` + `card_fibre` + `slotAt_eq` + `h_mul` | add | −79 |
| 8 | `dedekindPsi_prime_pow'` (L466–485) | reuse `ψ_prime_pow` | +18 |
| 9 | `dedekindPsi_prime` (L666–674) | reuse `ψ_prime` (+1 import) | +8 |
| 10 | `dedekindPsi_mul_prime_not_dvd`+`_dvd` (L675–703) | reuse `ψ_mul_prime` | +24 |
| 11 | `dedekindPsi_pos` (L660–665) | reuse public `dedekindPsi_pos` | +5 |
| | **block total (L405–703)** | | **≈+128 (range 110–150)** |
| 12 | two `hTcard` consumers (pin L1438–1457, 1663–1684) | one public `card_…_eq_dedekindPsi` | +30 |
| 13 | port `Spine.lean:179–201` duplicate pair | import promoted pair | +23 |

Sub-totals: counting machinery §4 = **≈+97**; ψ-lemma reuse §3 = **≈+55**.

---

## 7. Final verdict

A **real win exists**, but it is *not* "mathlib has the Γ₀ index formula" — it
does not, and `dedekindPsi` is absent from mathlib. The win is:

1. **drop the 108-line `slotAt_mul` fibre CRT** and replace the multiplicativity
   of `slots` with the closed form `slotAt n d = (d / gcd (n/d) d) * φ (gcd (n/d) d)`
   (provable in ~29 lines from mathlib `Nat.periodic_coprime` /
   `Nat.filter_coprime_Ico_eq_totient`) plus a 24-line `h_mul`, assembled with
   mathlib `Nat.Coprime.divisors_mul`. ≈**80–105 lines**;
2. **delete the four duplicated `dedekindPsi_*` developments** and call the
   already-public port/FLT theorems (`Jq.lean:215/221/284`,
   `Thm_ModularCurve_dedekindPsi_{prime,prime_pow,mul_prime,pos}`). ≈**50–60 lines**;
3. **expose one `Finset.card = dedekindPsi` statement** and keep `slots`/`slotAt`
   private; consumers shrink ≈30 lines.

Expected block size after the change: **≈150–190 lines versus 299** (≈35–50 %
reduction). The prime-power spine (`slotAt_prime_pow_mid` after §4,
`slots_prime_pow`, `slots_eq_dedekindPsi`'s induction) is genuinely near-minimal
and should be kept.
