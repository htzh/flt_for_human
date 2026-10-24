# The modular equation at transcendental `j` — the roots are the Vélu quotients

**Status: the whole theory is landed (2026-10-23) — all 8 nodes, 543 pin lines,
green and checker-clean.** The forward node and the two faces sit in
`FLTForHuman/ModularCurve/ModularPolynomialVelu.lean` (the forward
`…isRoot_map_j_veluQuotient_j_of_addOrderOf_eq`, the product form
`…fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`, the converse
`…mem_of_isRoot_map_j_of_transcendental_of_odd`); the rigidity ladder is in
`WeierstrassCurve/IsogenyEndDatum/TranscendentalRigidity.lean` (R1, R2) and
`WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` (R3); the support columns are
`WeierstrassCurve/Velu/SubfieldMembership.lean` (M1, M2) and
`WeierstrassCurve/Velu/CyclicSubgroupCount.lean` (C). Each of the five modules reads
`0 mismatch / 0 missing` and every headline's axioms are
`[propext, Classical.choice, Quot.sound]`. The set's record is
[../../logs/modular-equation-transcendental-j.md](../../logs/modular-equation-transcendental-j.md);
the forward node's own landing record stays in
[../../logs/modular-polynomial-velu.md](../../logs/modular-polynomial-velu.md),
which also carries the standards pass of §2.6. This note states the mathematics of
both halves and gives the port structure: nodes, homes, order, budget, and the one
block of the pin the port does **not** take.

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

Companions: the `N = 2` analogue of the product half is
[TOPIC-fibre-two-coefficient-normalization.md](TOPIC-fibre-two-coefficient-normalization.md)
(and its row [WORKORDER-B2-fibre-two.md](WORKORDER-B2-fibre-two.md)); the classical
mathematics of `Φ_N` is [../../../base/006-the-modular-equation.md](../../../base/006-the-modular-equation.md);
the level-`N`/`Φ_N` shelf is
[TOPIC-levelN-and-modular-polynomial.md](TOPIC-levelN-and-modular-polynomial.md).

## 0. The answer

**Yes, port the two halves together.** The forward node landed alone because the
`--ready` reading priced it at `needed 1 / 87`; that is true of the node, but it is
only the `⇒` of an `⇔`. The full statement is one set equality,

$$\{\,r : \Phi_N(j(W), r) = 0\,\} \;=\; \{\, j(W/H) \;:\; H \le W[N]\ \text{cyclic},\ |H| = N \,\},$$

for an elliptic `W` over `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)` with `j(W)`
transcendental and `N` odd. Both directions need the same three-node rigidity
ladder (156 pin lines), both need the count `ψ(N)`, and the converse consumes the
forward node as a black box — it cannot be split again. The remaining work over
both consumers is **543 pin lines in 8 nodes**, not the 1,675 the two frontier
readings add up to, because the port already has a strictly stronger discriminant
lemma that removes a 1,045-line block of the pin (§2.4).

## 1. The mathematics

### 1.1 The datum: `Φ_N`

`ModularPolynomialData N` bundles `Φ : Polynomial (Polynomial ℤ)` with the three
facts the theory uses: `Φ` is monic in `Y`, of `Y`-degree `ψ(N)` (the Dedekind psi
count of cyclic order-`N` subgroups), and

$$\Phi_N\bigl(j(q),\, j(q^N)\bigr) \;=\; 0 \quad\text{in } \mathbb{Q}((q)).$$

That is the classical construction: `Φ_N(X,Y) = ∏_{C} (Y − j(E/C))` over the
`ψ(N)` cyclic order-`N` subgroups of a curve with `j(E) = X`, which lands in
`ℤ[X,Y]`. Here `Φ` is an *input*, not constructed — the theory below is the
moduli interpretation of that datum.

### 1.2 The forward inclusion (landed)

For odd `N = 2n+1`, a point `Q` with `addOrderOf Q = N`, and the odd Vélu quotient
`W/⟨Q⟩` elliptic, `j(W/⟨Q⟩)` is a root of `Φ_N(j(W), Y)`. The proof is one
instantiation of the general theorem that a cyclic kernel of order `N` over an
algebraically closed characteristic-`0` field forces the modular-polynomial
relation, with the Vélu function-field embedding supplying the isogeny and
`ker = ℤQ` supplying the cyclic kernel of order `N`. Landing record: [../../logs/modular-polynomial-velu.md](../../logs/modular-polynomial-velu.md).

### 1.3 What transcendental `j` buys: `End(W) = ℤ`

The injectivity `H ↦ j(W/H)` is what fails in general and what the transcendental
hypothesis repairs. A transcendental `j(W)` is not integral over `ℤ`, so no
endomorphism can force it to be: every `IsogenyEndDatum` endomorphism of `W` is
multiplication by an integer,

$$\forall D : \text{IsogenyEndDatum},\quad \exists m : \mathbb{Z},\ \forall P,\ D.\mathrm{pointEnd}\,P = m \bullet P.$$

The pin's route is a contradiction: a non-scalar endomorphism produces (via the
characteristic-polynomial/degree count `exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`
and squarefree values) an endomorphism of some degree `N` with `N` not a square,
whence `aeval W.j (Φ_N(X,X)) = 0`; the diagonal leading coefficient is a unit
(`isUnit_leadingCoeff_diag`), so `W.j` is integral over `ℤ` — against transcendence.
With `End(W) = ℤ`, two cyclic subgroups with the same quotient `j` must coincide
(the isogeny between the quotients pulls back to a scalar endomorphism), which is
the injectivity used by both halves.

### 1.4 The count: `ψ(N)` cyclic subgroups

For `K` algebraically closed with `(N : K) ≠ 0`, `E[N] ≅ (ℤ/N)²` (from
`nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`), and the number of cyclic
subgroups of order `N` in `(ℤ/N)²` is `ψ(N)`
(`AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy`).
Both are in the port; the node that assembles them for a Weierstrass curve is 22
lines.

### 1.5 The converse inclusion — the second half

`ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd`
(145 lines): if `L` is a subfield of `𝕂` containing the coefficients `a₁,a₂,a₃,a₄,a₆`
of `W` and the coordinates of every `N`-torsion point, then every root
`r` of `Φ_N(j(W), Y)` lies in `L`.

The proof is the set equality of §0, done inside a fixed `L`:

1. write `N = 2n+1`; let `B` be the type of cyclic subgroups `H ≤ W[N]` of order `N`,
   with `Nat.card B = ψ(N)` (§1.4);
2. choose a generator `g` of each `H` (local helper `exists_generator_of_isAddCyclic`)
   and put `jH := j(W/⟨g⟩)`, defined because `Δ(W/⟨g⟩) ≠ 0` (§2.4);
3. `jH ∈ L`: the summing set's coordinates lie in `L` by the torsion hypothesis
   (`oddOrderSummingSet_coords_mem`), and the Vélu quotient's `j` stays in any
   subfield containing the coefficients and the summing-set coordinates
   (`veluQuotient_j_mem_of_mem`, §1.6);
4. `jH` is a root: this is the **forward node** (§1.2);
5. `jH` is injective: the **transcendental distinctness** (§1.3);
6. `Φ_N(j(W),·)` has `ψ(N)` roots because it is monic of degree `ψ(N)` over an
   algebraically closed field (`card_roots_fibrePoly_of_monic`);
7. so `{jH} ⊆ roots` with equal cardinality, hence `roots = {jH}`; the given root
   `r` is some `jH`, and `r ∈ L` by (3).

Step (7) is the set equality; the pin's public theorem states only its corollary
`r ∈ L`, which is what the ramification-bound family consumes (§4).

### 1.6 The subfield membership and the product form

Two support facts make step (3) and the prime-level capstone work:

- `j_mem_of_a_mem` (32 lines): `j ∈ K` for any subfield `K` containing
  `a₁,a₂,a₃,a₄,a₆` (the `b`-invariants are polynomial in the `a`'s);
- `veluQuotient_j_mem_of_mem` (91 lines): if the summing set `T` has coordinates in
  `K` then `j(W/T) ∈ K` — the quotient's coefficients are `a₄ − 5ΣT`,
  `a₆ − b₂ΣT − 7 veluWSum`, so this reduces to the two sum-membership helpers
  (`veluTSum_mem`, `veluWSum_mem`) and the previous fact.

For prime `ℓ ≠ 2` the forward inclusion plus injectivity plus the count `ψ(ℓ) = ℓ+1`
give the factorization

$$\Phi_\ell\bigl(j(W), Y\bigr) \;=\; \prod_{i < \ell+1} \bigl(Y - j(W/\langle Q_i\rangle)\bigr),$$

`fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental` (97 lines), stated over an
arbitrary index type `ι` of cardinality `ℓ + 1` with an injective assignment of
order-`ℓ` points. That is the `N = 2` row's statement
(`fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j`, already landed) at general odd prime
level.

### 1.7 Why one theory

The two halves are the two inclusions of the same equality, and they share the
rigidity ladder and the count. Read downward they have two different faces, which
is why the pin keeps three public statements rather than one:

- the **root-membership face** (`mem_of_isRoot_…`) feeds the ramification bounds
  `hasRamBound_{one,two,three}_of_isRoot_…` and then the `j`-line/level-lowering
  chain;
- the **product face** (`fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`)
  feeds `…_of_isAlgClosed` and the arithmetic-Frobenius/places argument of the
  level-lowering route;
- the **forward node** also feeds the arithmetic specialization
  `modularPolynomial_eval_jInt_jQuotVelu_eq_zero` over `ℤ`/`ℚ̄` (Mazur step 3).

Porting them together therefore lands one reusable statement of the moduli
interpretation and its two corollaries at once.

## 2. The port structure

### 2.1 Nodes, sizes, homes

| id | node | pin `S_` lines | status | home |
|---|---|---:|---|---|
| F | `ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq` | 87 | **landed** | `ModularCurve/ModularPolynomialVelu.lean` |
| R1 | `ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag` | 14 | **landed** | new `WeierstrassCurve/IsogenyEndDatum/TranscendentalRigidity.lean` (with R2) |
| R2 | `WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j` | 62 | **landed** | new `WeierstrassCurve/IsogenyEndDatum/TranscendentalRigidity.lean` |
| R3 | `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental` | 80 | **landed** | append to `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` |
| P | `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental` | 97 | **landed** | `ModularCurve/ModularPolynomialVelu.lean` |
| M1 | `WeierstrassCurve.j_mem_of_a_mem` | 32 | **landed** | new `WeierstrassCurve/Velu/SubfieldMembership.lean` |
| M2 | `WeierstrassCurve.veluQuotient_j_mem_of_mem` | 91 | **landed** | same module |
| C | `WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed` | 22 | **landed** | new `WeierstrassCurve/Velu/CyclicSubgroupCount.lean` |
| B | `ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd` | 145 | **landed** | `ModularCurve/ModularPolynomialVelu.lean` |

### 2.2 Dependency graph

```
   R1 isUnit_leadingCoeff_diag (14)
    │
   R2 exists_forall_pointEnd_eq_zsmul_of_transcendental_j (62)      [V6's aeval_j_diag, landed]
    │
   R3 zmultiples_eq_of_veluQuotient_j_eq_of_transcendental (80)     [the landed _forall_… hEnd variant 525]
    ├───────────────────────────┬──────────────────────────┐
    ▼                           ▼                          │
   F (landed, 87)              P fibrePoly = ∏ (97)         │
    │        ▲                                            │
    │        └── R3, M2, C, D_port, card_roots_fibrePoly  │
    ▼                                                     │
   B mem_of_isRoot (145)  ◄── M1 j_mem_of_a_mem (32) ──► M2 veluQuotient_j_mem_of_mem (91)
                          ◄── C  natCard_… (22)
```

R1, C and M1/M2 get new modules rather than appends to the legacy
`ModularPolynomialLeadingCoeff`/`CyclicCount` homes: the hosts stay untouched and
each new module owns one subject. `R3` is the one append, to the already-wired
`CyclicQuotientJInjective`, where its `hEnd` sibling lives.

`P` and `B` are the two outputs; they share `F`, `R3` and the promotions of §2.5.
`B` additionally uses `M1/M2`, `C`, the port's discriminant lemma `D_port` (§2.4),
and `card_roots_fibrePoly_of_monic`.

### 2.3 Reuse map — what the port already has

| input | port home |
|---|---|
| `WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq` (V6 capstone) | `WeierstrassCurve/IsogenyEndDatum/DiagonalPhi.lean` |
| `exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq` | `WeierstrassCurve/IsogenyEndDatum/CharPolySquare.lean` |
| `Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul` | `NumberTheory/SquarefreeValues.lean` |
| `ModularCurve.nonempty_modularPolynomialData` | `ModularCurve/Degree/PhiData.lean` |
| `isUnit_leadingCoeff_diag_of_not_isSquare` | `ModularCurve/ModularPolynomialLeadingCoeff.lean` |
| `zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int` | `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` |
| `nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` | `Elliptic/TorsionZMod.lean` |
| `AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy` | `WeierstrassCurve/Velu/CyclicCount.lean` |
| `ModularCurve.dedekindPsi_prime` | `ModularCurve/Defs/DedekindPsi.lean` |
| `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq` | `WeierstrassCurve/Velu/Discriminant.lean` |

`R1` and `R3` are each a short wrapper: `R1` is two lines over the landed
`isUnit_leadingCoeff_diag_of_not_isSquare`; `R3` is the pin's 80-line
`S_` that derives `CharZero`/`IsAlgClosed`/gates for `𝕂` and discharges the
`hEnd` hypothesis of the landed variant with `R2`. (`R3`'s pin proof uses a
private `Ws13B.charZero_hahn`; the port spells it
`charZero_of_injective_ringHom HahnSeries.C_injective`, the same substitution the
landed forward module uses.)

### 2.4 The detour the port does not take — 1,045 lines

The pin's converse imports
`WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero` (100 lines),
which it proves through a ψ₂²-route:

- `veluX_oddOrderSummingSet_injOn_psi2Sq_roots` (781 lines): `veluX S` is injective
  on the roots of `Ψ₂²`;
- `eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero` (164 lines): the
  quotient's `veluX` sends ψ₂²-roots to ψ₂²-roots;

then counting ψ₂² roots and images to show `Δ ≠ 0`. The first node has **no other
consumer**; the second's only consumer is the third.

The port does not need any of it. `WeierstrassCurve/Velu/Discriminant.lean` has

```lean
theorem veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
    [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1)
```

from which `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`
follows in three lines, with **no** `[IsAlgClosed]` and **no** `(2 : F) ≠ 0` — strictly
stronger than the pin's node. So the converse, and every other consumer of the
pin's discriminant node (it has 9, including the Mazur chain), can call the port's
lemma directly. **1,045 pin lines drop out of the demand** and no statement changes.
This is the same trade as the general cyclic-kernel theorem above: the port's
route through the discriminant product formula replaces the pin's counting route.

### 2.5 Promotions (ground prepared 2026-10-23)

Both outputs need three facts the port used to keep `private` in
`ModularCurve/Degree/PhiData.lean`: `monic_fibrePoly`, `natDegree_fibrePoly` and
`card_roots_fibrePoly_of_monic`. The promotion is **landed**: all three now sit at
their pin names in `ModularCurve/Defs/FibrePoly.lean` (the pin's definition-layer
home, with bodies `Monic.map`, `natDegree_map` and the root count), and the
`private` copies in `PhiData` are gone (it imports them). That module was a
`PORT_FILES` legacy module; it was handed over in the same pass — `spec-pin:` for
`Definitions/Def_ModularCurve_FibrePoly.lean`, the `ReduceModBivar` block and the
three `Theorems/Thm_ModularCurve_*_fibrePoly.lean` wrappers, removed from
`spec/old_check_stmts.py`, dedup/move_dead clean. It reads **10 ok / 0 mismatch /
0 missing / 0 own**.

### 2.6 Ground already prepared

The standards pass for this theory (2026-10-23):

| module | what was done | state |
|---|---|---|
| `ModularCurve/Defs/FibrePoly.lean` | promotions of §2.5; `spec-pin:` wiring; out of `PORT_FILES`; dedup 0 clusters; move_dead 0 | **10 ok / 0 mismatch** |
| `ModularCurve/Degree/PhiData.lean` | the three `private` copies deleted (dedup); one dead theorem deleted (`nonempty_modularPolynomialData_mul_of_coprime`, dead in the pin too: defined twice there, used nowhere) | 10 ok / 0 mismatch |
| `WeierstrassCurve/Velu/PointMapOddOrder.lean` | `spec-pin:` wiring; out of `PORT_FILES`; five `dif_pos`/`dif_neg` deprecations renamed to `dite_eq_left`/`dite_eq_right` | **2 ok / 0 mismatch**, 0 warnings |
| `ModularCurve/ModularPolynomialLeadingCoeff.lean` | `spec-pin:` wiring; out of `PORT_FILES`; the ten private `w1_*` pin part labels stripped (`order_eq`, `slot_factor`, `diag_lc_pow`, …); the trailing `#print axioms` removed | **1 ok / 0 mismatch**, 0 warnings |
| `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` | machine token dropped from the one private helper (`cmm5_dp_natCard_ker_comp` → `natCard_ker_comp`); already wired | 0 warnings |
| `ModularCurve/ModularPolynomialVelu.lean` | header made self-contained (no cross-project jargon), premise homes and history moved to the log | 1 ok / 0 mismatch |

Whole wired set after the pass: `4941 ok, 0 mismatch, 0 missing, 19 own, 0 kw` over
213 modules (`spec/check_port.py --all`, corpus `aa2d8b3`) — the measurement *before*
the eight nodes landed; after them it is `4950 ok` over 217 modules (see the log).
The build of the touched closure is `lake build
FLTForHuman.ModularCurve.ModularPolynomialVelu` under the pinned `v4.34.0`.

## 3. Sets, order, budget## 3. Sets, order, budget

| set | nodes | new pin lines | why this cut |
|---|---|---:|---|
| **M-SET-1** rigidity ladder | R1, R2, R3 | 156 | both outputs need R3; nothing else can start without R2 |
| **M-SET-2** product form | P | 97 | `F` + R1, R3; the prime-level capstone |
| **M-SET-3** membership and count | M1, M2, C | 145 | independent of M-SET-1/2; needed only by B |
| **M-SET-4** converse | B | 145 | consumes F, R3, M2, C, `D_port`, promotions |
| **total** | **8** | **543** | vs 1,675 raw for the two frontier readings |

Order: promotions → M-SET-1 → (M-SET-2 and M-SET-3 in parallel) → M-SET-4. R1/R2
first because R3 (hence both outputs) needs them; M-SET-3 can be taken any time and
is the natural second dispatch for a two-agent wave.

Measured frontier readings, for the record: `P` is `5 / 340`; `B` is `11 / 1,578`
with the unsubstituted discriminant block. After the §2.4 substitution and the
landed `F`, `B` is `6 new nodes / 446` and `P` is `4 new nodes / 253`.

### 3.1 Verification

Per module, the playbook recipe: `lake env lean` on the file, `python3
spec/check_port.py <module>` (target `0 mismatch / 0 missing`), `#print axioms`
on the headline. For the set, the consumer zone is **landed**:
`lean/spec/TranscendentalJConsumer.lean` (a `spec/` probe, outside every lake
target, run with `lake env lean`, ~4.2 s). It executes three compositions:

* **zone 1** — the product form read at one of its own factors: `j(W/⟨Q i⟩)` is a
  root of `Φ_ℓ(j(W), Y)`, consuming the product headline (hence the forward root
  and the transcendental distinctness);
* **zone 2** — that root handed to the converse, so it lies in any subfield
  containing the coefficients and the `ℓ`-torsion coordinates: the product face and
  the membership face composed on one object, running through the membership and
  count modules;
* **zone 3** — the count at a prime, `ψ(ℓ) = ℓ + 1`, composing the count module with
  `ModularCurve.dedekindPsi_prime`.

Deleting any of the five modules breaks the consumer.

## 4. Downstream## 4. Downstream

| consumer | what it uses | distance to the root |
|---|---|---|
| `hasRamBound_{one,two,three}_of_isRoot_…_of_odd` | `B` (root membership) | the `j`-line ramification family |
| `mem_of_isRoot_map_j_of_transcendental` | `B` | the `N`-torsion-field form |
| `fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed` | `P` | level-lowering (places/Frobenius) |
| `modularPolynomial_eval_jInt_jQuotVelu_eq_zero` | `F` | Mazur step 3 (the arithmetic specialization) |

The Mazur consumer is its own small set (6 nodes / 1,408; the port's discriminant
lemma prunes part of it too) and is **not** in this theory: it works over `ℤ`/`ℚ̄`
with the level structure `hQfix`, no transcendental `j` in the statement.

## 5. What the notes must not claim

- The converse's public statement is **`r ∈ L`**, not `r = j(W/H)`. The set
  equality is internal to its proof; if the port exposes it, that is a new public
  lemma (a generalisation of the pin's statement, to be recorded as `own:`/derived,
  not as the pin's text).
- **`P` is prime-level only** (`[Fact ℓ.Prime]`, `ℓ ≠ 2`, `card ι = ℓ + 1`). The
  odd-`N` factorization is not the pin's statement; the general
  `fibrePoly_j_eq_prod_veluQuotient_j` is a different, unported node.
- The theory lives over `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)` (that is where the
  transcendental `j` is available); only `F` and `R2` are stated over a general
  algebraically closed char-`0` field.
- `Φ_N` is an **input datum** here — `ModularPolynomialData` — not constructed in
  these nodes. Do not describe the set as proving existence or integrality of
  `Φ_N`.
- The ψ₂²/discriminant block is **not ported**: do not cite
  `veluX_oddOrderSummingSet_injOn_psi2Sq_roots` or its sibling as needed.
