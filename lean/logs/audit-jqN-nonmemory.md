# Proof-engineering audit: the two `jqN_prime_not_mem_adjoin` lemmas

Read-only audit of `anthropics/fermats-last-theorem` at git `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef` (short `aa2d8b3`).

Files (all paths relative to the clone `~/proj/fermats-last-theorem`):

| tag | path | lines |
|---|---|---|
| **F1** | `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` | 2002 |
| **F2** | `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_adjoin.lean` | 653 |
| **F3** | `P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` | 995 |
| **F4** | `P2M/Sol/S_ModularCurve_full_eq_adjoin_primes.lean` | 600 |
| **F5** | `P2M/Sol/S_ModularCurve_full_eq_adjoin_full_div_prime.lean` | 624 |
| **F6** | `P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean` | 752 |
| **F7** | `P2M/Sol/S_ModularCurve_jqN_sq_not_mem_adjoin.lean` | 585 |
| **D** | `Definitions/Def_ModularCurve_X0.lean` | 348 |

**Verdict in one line.** (B) genuinely independent for the general (M-arbitrary) statement, with a genuine but partial (A) reduction **only for squarefree M** (and, by strong induction with the *public* lemma's engine, for any M having a prime factor of exponent exactly 1). The reduction breaks exactly at *powerful* M (every prime factor exponent ≥ 2), and that case is load-bearing in the FLT development (e.g. M = 9, p = 2), so the net line saving in F1 is ≈ 0.

---

## 1. The two statements, verbatim

### 1a. Public Finset lemma (F2)

Module body (`private` inside `ModularCurve`, exported through the p2m `solution` wrapper):

- `F2:642` (theorem), `F2:650` (exported `solution`):

```
private theorem ModularCurve.jqN_prime_not_mem_adjoin (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ) [hr : Fact (Nat.Prime r)] (hrS : r ∉ S) : jqN r ∉ IntermediateField.adjoin ℚ (insert jq {x : LaurentSeries ℚ | ∃ p ∈ S, ∃ _ : NeZero p, x = jqN p})
```

The public wrapper `Theorems/Thm_ModularCurve_jqN_prime_not_mem_adjoin.lean` re-exports it as
`theorem ModularCurve.jqN_prime_not_mem_adjoin (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ) [hr : Fact (Nat.Prime r)] (hrS : r ∉ S) : jqN r ∉ IntermediateField.adjoin ℚ (insert jq {x : LaurentSeries ℚ | ∃ p ∈ S, ∃ _ : NeZero p, x = jqN p})`.

Its engine is `step_contradiction` (`F2:426-575`) plus the induction `jqN_prime_not_mem_adjoin_key` (`F2:577-634`).

### 1b. Private M-arbitrary lemma (F1)

`F1:1586-1592`:

```
private theorem jqN_prime_not_mem_adjoin (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank ℚ⟮jq⟯
          (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
        ∧ modularFunctionField d = modularFunctionFieldFull d) :
    jqN p ∉ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
```

Body: `F1:1593-1947`; `set_option maxHeartbeats 6400000 in` at `F1:1584`; `section NonMem0` `F1:1580-1949`.

### 1c. The outer theorem that consumes it

`F1:1977-1992`:

```
private theorem ModularCurve.jqN_prime_not_mem_full (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d], … = dedekindPsi d ∧ modularFunctionField d = modularFunctionFieldFull d) :
    jqN p ∉ modularFunctionFieldFull M := by
  intro hmem0
  obtain ⟨-, hgM⟩ := hall M dvd_rfl
  have hmem : jqN p ∈ IntermediateField.adjoin
      (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      ({jqN M} : Set (LaurentSeries ℚ)) := by
    rw [← hgM] at hmem0
    exact ModularCurve.W1.mem_adjoin_jqN_of_mem_mff hmem0
  exact ModularCurve.W1.jqN_prime_not_mem_adjoin M p hpM hall hmem
```

### 1d. Which one is needed, and they are not the same statement

- `grep` evidence: in F1 the **private** M-arbitrary lemma is invoked exactly once, at `F1:1992`. It is used only by `jqN_prime_not_mem_full` (`F1:1977`). The Finset lemma name does not occur as a call anywhere in F1 (the occurrences at `F1:25,31,126,219,248,349,403,852,1578` are p2m dependency strings, not uses), and F1 does **not** import its module.
- F1's import list (`F1:1-17`) contains **no** `Thm_ModularCurve_jqN_prime_not_mem_adjoin`. Conversely F2's import list (`F2:1-17`) contains no `Thm_ModularCurve_jqN_prime_not_mem_full`; a transitive-import BFS from `P2M.Sol.S_ModularCurve_jqN_prime_not_mem_adjoin` and from `P2M.Sol.S_ModularCurve_full_eq_adjoin_primes` (150 modules) never reaches the full-lemma module. So importing the Finset lemma into F1 is cycle-free.
- They are different statements by inspection:
  - F2: quantifies a **Finset of primes** `S` and a prime `r ∉ S`; base field `ℚ`; generator set `insert jq {jqN p | p ∈ S}`.
  - F1: quantifies a **single composite level** `M` with `[NeZero M]` and a prime `p ∤ M`; base field `ℚ⟮jq⟯`; generator set the singleton `{jqN M}`; carries a **divisor-wise `hall`** hypothesis.
  - No substitution makes them syntactically equal (`S` is prime-indexed; `M` is arbitrary and enters via `{jqN M}` over `ℚ⟮jq⟯`).

**Answer to "which is needed":** `jqN_prime_not_mem_full` needs the **private M-arbitrary** lemma (`F1:1586`), not the public Finset lemma.

---

## 2. Dependency list of the private proof (`F1:1586-1947`), with line numbers

`grep` on the exact block confirms the private lemma uses **none** of `jqN_prime_not_mem_adjoin` (F2), `jqN_pow_not_mem_adjoin_full` (F3), `step_contradiction`, `full_eq_adjoin_full_div_prime` (F5), `full_eq_adjoin_primes` (F4), `mem_adjoin_jqN_of_mem_mff`. It is a self-contained "slot/evaluation" argument.

Same-file (F1) facts used (definition line → use line):

| fact | def | used at |
|---|---|---|
| `TS_coeff_neg` | `F1:46` | 1895 |
| `qExpand_TS` | `F1:92` | 1883, 1907 |
| `iota_jqN` | `F1:102` | 1907 |
| `cycUnit_spec` | `F1:204` | 1601 |
| `isPrimitiveRoot_pow_div` | `F1:225` | 1604, 1608 |
| `slotAt` | `F1:405` | 1679 (`unfold slotAt`) |
| `slots_eq_dedekindPsi` | `F1:641` | 1684 |
| `dedekindPsi_pos` | `F1:660` | 1615, 1789 |
| `dedekindPsi_prime` | `F1:668` | 1635 |
| `sv` | `F1:704` | 1663 ff. |
| `sv_eq_TS` | `F1:714` | 1883, 1907 |
| `TS_congr'` | `F1:718` | 1884, 1908 |
| `sv_inj` | `F1:723` | 1708, 1743 |
| `aeval_intermediateField_eq_zero` | `F1:748` | 1860 |
| `mem_range_of_eval_eq_const` | `F1:804` | 1926 |
| `tight_one` | `F1:823` | 1631 |
| `gen_one` | `F1:835` | 1631 |
| `map_qExpand_minpoly_eq` | `F1:858` | 1641, 1644 |
| **`rval_aux`** (the slot product) | `F1:887` | 1643, 1645 |

Imported facts used:

| fact | use |
|---|---|
| `ModularCurve.finrank_adjoin_jqN_eq_of_prime` | 1636 and 1944 (final contradiction: `finrank = 1` vs `= p+1`) |
| `ModularCurve.functionFieldGeneration_of_squarefree` + `functionFieldGeneration_iff_full_eq` | 1637-1639 (to build `hallp`, the `p`-instance of `hall`) |
| `qExpand`, `coeffEmb`, `qExpand_qExpand`, `coeffEmb_qExpand`, `qExpand_congr` (`F1:799`), `qExpand_coeff_of_not_dvd` | throughout (1648 ff.) |

Key structural point: the two nontrivial inputs are (i) the slot product `rval_aux` for level `M` (line 1643, using `hall`) and for level `p` (line 1645, using the derived `hallp`), and (ii) the final `Tight p` fact `finrank_adjoin_jqN_eq_of_prime p`. Everything else is multiset/slot bookkeeping and one root-evaluation argument (`mem_range_of_eval_eq_const`) concluding `jqN p ∈ ℚ⟮jq⟯` followed by a degree contradiction.

`rval_aux` (`F1:887-1578`) is exactly the slot product exported as `ModularCurve.minpoly_jqN_map_eq_prod_slots` (`F1:1958-1974`, whose body is literally `ModularCurve.W1.rval_aux M ζ hζ hall`, `F1:1974`). So the private lemma **is** already the "~20-line-ish" derivation from the slot product — except the derivation is 362 lines, because the root-evaluation step is genuinely hard.

Also note: `mem_adjoin_jqN_of_mem_mff` (`F1:776-797`) is **not** used by the private lemma; it is used by the outer theorem at `F1:1991`.

---

## 3. The attempted reduction: containment analysis and case split

### 3a. Containment directions (the key observation, stated precisely)

Let `A_M := IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set _)` and `B_M := modularFunctionFieldFull M`.

- `A_M ⊆ B_M` **unconditionally**: `jqN M ∈ B_M` (`D:309-311`, `jqd_mem_full M dvd_rfl`) and `jq ∈ B_M` (`jqd_mem_full M (one_dvd M)` + `qExpand_one_apply`), so the `ℚ⟮jq⟯`-adjoin of `jqN M` lies in `B_M`.
- Under `Gen M`, i.e. `modularFunctionField M = B_M` (this is the second component of `hall M dvd_rfl`), also `B_M ⊆ A_M`: `modularFunctionField M = adjoin ℚ {jq, qExpand ℚ M jq}` (`D:250-251`) and `mem_adjoin_jqN_of_mem_mff` (`F1:776`) gives `modularFunctionField M ⊆ A_M`. Hence

  **`Gen M` ⟹ `A_M = B_M`.**

Consequences used below:
- `B_M`-non-membership is the *stronger* statement; it implies the private lemma's `A_M`-non-membership (since `A_M ⊆ B_M`).
- Under `hall` (which contains `Gen M`), the private lemma and `jqN_prime_not_mem_full` are **equivalent**, so any replacement must prove essentially `jqN p ∉ B_M`.

### 3b. What the intended decomposition M = M'·q gives

The only level-decomposition tool is `F5:601 full_eq_adjoin_full_div_prime`:

```
full_eq_adjoin_full_div_prime (M) [NeZero M] (p) [Fact (Nat.Prime p)] (a) (hpM : ¬ p ∣ M) :
  modularFunctionFieldFull (M * p ^ (a + 1)) =
    adjoin ℚ (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a)))
```

It requires `p ∤ M` and **adds `jqN (p^(a+1))`** — a prime power, not a prime value, as soon as `a+1 ≥ 2`.

The two available separation tools are both **prime-indexed**:

- `F2:577 jqN_prime_not_mem_adjoin_key` / `F2:426 step_contradiction (p r) (hrp : r ≠ p) … (hpF : jqN p ∉ F) (hrF : jqN r ∉ F) (hmem : jqN r ∈ adjoin F {jqN p}) : False`. It separates two **primes** `p ≠ r` over a base `F` containing `jq`.
- `F7:560 jqN_sq_not_mem_adjoin` adds a single prime **square** over a **squarefree** base: `jqN (p*p) ∉ ℚ(jq, jqN p, {jqN q | q ∈ S})`; it does not iterate to `p^e`, `e ≥ 3`.

### 3c. Case analysis for a hypothetical induction on M

Goal Φ(M): for prime `p ∤ M`, given `Hall M` (`F6:417`: `∀ d ∣ M, Tight d ∧ Gen d`), `jqN p ∉ B_M`.

1. **M squarefree** — **the reduction succeeds, shortly.** `full_eq_adjoin_primes` (`F4:579`, hypothesis `Squarefree N`) gives
   `B_M = adjoin ℚ (insert jq {jqN q | q ∈ M.primeFactors})`.
   Apply the public Finset lemma (`F2:642`) with `S = M.primeFactors`, `r = p`; `p ∉ M.primeFactors` since `p ∤ M` and `M ≠ 0`. This yields `jqN p ∉ B_M`, hence (via `A_M ⊆ B_M`) the private conclusion. This even handles `M = 1`. Estimated cost: 2 imports + ~15-30 lines.
2. **M has a prime `q ≠ p` of exponent exactly 1** (`q ∤ M/q`) — **the reduction also succeeds, by strong induction + `step_contradiction`.** Put `M' = M/q`. `F5:601` with `a = 0` gives `B_M = ℚ(B_{M'} ∪ {jqN q})`. `Hall M'` follows from `Hall M`. The induction hypothesis gives both `jqN p ∉ B_{M'}` and `jqN q ∉ B_{M'}` (since `q ∤ M'`), and `jq ∈ B_{M'}`. Applying `step_contradiction` with parameters `(p, r) := (q, p)` to `hmem : jqN p ∈ adjoin B_{M'} {jqN q}` (obtained from `jqN p ∈ B_M`) gives `False`. **This step does not use the tower lemma** — it uses the public lemma's engine. (Implementation caveat: `step_contradiction` is a plain `theorem` at `F2:426` but is not in F2's `p2m_export` list (`F2:400`) nor re-exported by the `Thm_` wrapper; it would need importing/exporting, `exists_phiIrreducible_evalSymm` and `cycUnit` are available.)
3. **M powerful** (every prime factor `q ≠ p` has exponent ≥ 2, e.g. `M = q^2`, `M = 9`, `M = 36`) — **the reduction breaks.** There is no prime of exponent 1 to peel. Building `B_M` from `B_{M/q}` requires adjoining `jqN(q^e)` with `e ≥ 2` (via `F5:601`), and *no* available tool separates a field missing `jqN p` from `jqN p` after adjoining a genuine **prime power**:
   - `step_contradiction` / `jqN_prime_not_mem_adjoin_key` only accept `jqN` of **primes** as the new generator (`F2:426`, `F2:577`);
   - `jqN_sq_not_mem_adjoin` (`F7:560`) adds a square only over a **squarefree** base (its base is `ℚ(jq, jqN p, {primes})`), so it cannot be iterated over a non-squarefree base;
   - the tower lemma is **circular** here (see 3d).
   
   Concretely, for `M = q^2`: `B_{q^2} = ℚ(B_q ∪ {jqN(q^2)})`. The public lemma gives `jqN p ∉ B_q`, and the tower lemma with base `1`, prime `q`, `a = 0` gives `jqN(q^2) ∉ B_q = ℚ(jq, jqN q)`. But from "`x ∉ F` and `y ∉ F`" one may **not** conclude "`y ∉ F(x)`"; that implication is exactly the extra content of the private lemma, and no library result supplies it for `jqN`. The existing separation results are all keyed to the *prime generator* `jqN p`, not to an arbitrary new element.

### 3d. The tower lemma is downstream, not a substitute

`F3:979-985`:

```
private theorem ModularCurve.jqN_pow_not_mem_adjoin_full (M) [NeZero M] (p) [Fact (Nat.Prime p)] (a)
    (hF : jqN p ∉ modularFunctionFieldFull M) :
    jqN (p ^ (a + 2)) ∉ adjoin ℚ ((modularFunctionFieldFull M : Set _) ∪ {x | ∃ i, i ≤ a + 1 ∧ x = jqN (p ^ i)})
```

The hypothesis `hF` is *literally* the conclusion of `jqN_prime_not_mem_full M p hpM`, i.e. the statement to be proved. The use site confirms the direction:

- `F6:526-527`: `h0 : jqN p ∉ modularFunctionFieldFull M := ModularCurve.jqN_prime_not_mem_full M p hpM …`;
- `F6:533`: `have h1 := ModularCurve.jqN_pow_not_mem_adjoin_full M p k h0`.

So `jqN_prime_not_mem_full` (private lemma) → `jqN_pow_not_mem_full` (`F6:523`) → tower lemma → `Tight d` (`F6:679-686`). The tower lemma **cannot** be used to replace the private lemma; doing so is circular.

### 3e. The powerful case is load-bearing

In `hall_all` (`F6:613-700`), `Tight d` is proved for `d = M · p^(a+1)` with `p = d.minFac`, `M` the `p`-free part (arbitrary, possibly powerful), and it calls `jqN_prime_not_mem_full M p hpM hallM` at `F6:527`. Example: `d = 36 = 9 · 2^2`, so `p = 2`, `M = 9 = 3^2` (powerful), `a = 1`. Hence a reduction that only covers squarefree (or exponent-1) `M` cannot prove `Tight 36`. The final targets `ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi` (`F6:712`), `modularFunctionField_eq_full` (`F6:721`), `functionFieldGeneration` (`F6:727`), `exists_phiIrreducible` (`F6:732`) all route through `hall_all` and therefore through the powerful case.

---

## 4. Verdict and estimated line savings

**(B) Genuinely independent for the M-arbitrary statement**, with a *partial* (A):

- Squarefree `M`: replaceable by a short derivation from the public Finset lemma + `full_eq_adjoin_primes` + the containment `A_M ⊆ B_M`. **~15-30 lines** (plus 2 imports) versus the current 362-line body.
- `M` with an exponent-1 prime factor: replaceable by strong induction using `full_eq_adjoin_full_div_prime` + `step_contradiction` (the public engine). No tower lemma needed.
- Powerful `M`: **not replaceable** by the public Finset lemma, by `step_contradiction`, by `jqN_sq_not_mem_adjoin`, or by the tower lemma. The precise reason: `B_M` requires adjoining prime-power generators `jqN(q^e)` (`e ≥ 2`); every separation tool in the repository is keyed to prime generators (`F2:426`, `F2:577`, `F7:560`), and the only prime-power tool (the tower lemma, `F3:979`) *assumes* the very non-membership being proved (`hF : jqN p ∉ mff M`) and is used with exactly that hypothesis at `F6:526-534`.

Because case 3 is required (e.g. `M = 9` at `F6:527`), **the net saving in F1 is ≈ 0** (the private lemma could only be *split*, not deleted). A full reduction would need a new theorem of the form "for coprime `q, p`, if `jqN p ∉ F` and `F` contains the `q`-primary data, then `jqN p ∉ F(jqN(q^e))`" — plausibly as hard as the private lemma itself. The 362-line slot argument (`rval_aux` for `M` and `p` + `mem_range_of_eval_eq_const` rigidity + `finrank_adjoin_jqN_eq_of_prime` contradiction) is the current formalization of exactly that missing disjointness statement.

---

## 5. Confidence and what to test in Lean

**Confidence: high, ~85-90%.** Positive evidence: (i) the tower lemma's hypothesis is verbatim the goal and its use site (`F6:527`→`F6:533`) confirms the dependency direction; (ii) an exhaustive name scan shows the only `jqN`-non-membership tools are prime- or square-over-squarefree-indexed; (iii) the private lemma's block uses none of the public/tower machinery, so it is not currently derived from them; (iv) the public lemma is not even imported by F1. Residual ~10-15%: a Lean-level combination (e.g. tensor/linear-disjointness of the two prime towers) that I did not find and that no `jqN` lemma currently states.

Concrete Lean tests to run (in a scratch copy — this audit was read-only):

1. **Squarefree sub-lemma.** Add imports `Theorems.Thm_ModularCurve_jqN_prime_not_mem_adjoin`, `Theorems.Thm_ModularCurve_full_eq_adjoin_primes`; prove
   `private theorem jqN_prime_not_mem_adjoin_squarefree (M) [NeZero M] (p) [Fact (Nat.Prime p)] (hM : Squarefree M) (hpM : ¬ p ∣ M) (hgen : modularFunctionField M = modularFunctionFieldFull M) : jqN p ∉ adjoin ℚ⟮jq⟯ ({jqN M} : Set _)`
   by `full_eq_adjoin_primes M hM` + `ModularCurve.jqN_prime_not_mem_adjoin M.primeFactors …` + `A_M ⊆ B_M`. Expect success; this validates case 1 and the containment.
2. **Exponent-1 sub-lemma.** With `M := M' * q`, `q ∤ M'`, `q ≠ p`, instantiate `step_contradiction` with `(p, r) := (q, p)`; check the rewrites `mff(M'*q) = adjoin ℚ (insert (jqN q) (mff M'))` (`F5:601` with `a = 0`) and `adjoin_adjoin_left`. This validates case 2 (and shows the tower lemma is unnecessary there).
3. **Powerful counterexample attempt.** Try to prove `jqN 2 ∉ modularFunctionFieldFull 9` (or `jqN 3 ∉ mff 4`) using only the public Finset lemma, `step_contradiction`, `jqN_sq_not_mem_adjoin`, and the tower lemma `jqN_pow_not_mem_adjoin_full`. Expect the goal to stall at `jqN 2 ∉ adjoin (mff 3) {jqN 9}` (resp. `jqN 3 ∉ adjoin (mff 2) {jqN 4}`), since the added generator is a prime power and `step_contradiction` requires a prime. Confirming a stall here makes the (B) verdict a Lean-verified fact.
4. **Circularity check.** `#check @ModularCurve.jqN_pow_not_mem_adjoin_full` to confirm the `hF : jqN p ∉ modularFunctionFieldFull M` argument position, and `grep` that its only call (`F6:533`) passes `jqN_prime_not_mem_full`'s output.

---

## Appendix: exact grep evidence

```
$ grep -rn "jqN_prime_not_mem_adjoin" F2 F1
F2:642  private theorem ModularCurve.jqN_prime_not_mem_adjoin (S : Finset ℕ) …
F2:650  theorem solution (S : Finset ℕ) …
F1:1586 private theorem jqN_prime_not_mem_adjoin (M : ℕ) [NeZero M] (p : ℕ) …
F1:1992   exact ModularCurve.W1.jqN_prime_not_mem_adjoin M p hpM hall hmem
(plus p2m_open/p2m_export dependency strings, which are not uses)
```

```
$ sed -n '1586,1947p' F1 | grep -n "jqN_prime_not_mem_adjoin\|jqN_pow_not_mem_adjoin_full\|step_contradiction\|full_eq_adjoin_full_div_prime\|full_eq_adjoin_primes"
(no output)
```

```
$ diff F1 S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean
44 changed lines; every difference is a P2MW.S_ModularCurve_* namespace string,
except the trailing `solution` wrapper.  The entire private block F1:1586-1947 is
verbatim identical in both generated files.
```

Caveat: F1 and `P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` are generated by the p2m tooling and duplicate this block verbatim (same line numbers 1586-1947). Any replacement must be made in the p2m source that generates both, or in both files.
