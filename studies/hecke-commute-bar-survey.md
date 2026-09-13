# Survey: the Jacobian and the Hecke action behind `ModularCurve.heckeOperatorsCommuteBar`

Research survey to prepare a math note. It maps the proof of the commutativity
of the Hecke operators on `J_0(N)` and isolates the two objects the note should
explain: how the "Jacobian" is constructed in the FLT development, and how the
Hecke operator acts on it. Everything is read from the local clone
`~/proj/fermats-last-theorem` pinned at `aa2d8b3`; all citations below are
public URLs at that sha. Conventions are those of [../AGENTS.md](../AGENTS.md).

## 0. The target

The theorem is a one-liner in the repository; the mathematics is entirely in
the reduction chain it invokes:

```lean
theorem ModularCurve.heckeOperatorsCommuteBar (N : ℕ) [NeZero N] :
    ModularCurve.HeckeOperatorsCommuteBar N := by
  p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeOperatorsCommuteBar.solution
```

([`Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean`, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean#L9)).

The proposition itself is a pairwise-commutation statement for one operator per
prime:

```lean
def heckeOperatorBar (ℓ : Nat.Primes) : Module.End ℤ (JZero N) :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ).toIntLinearMap

def HeckeOperatorsCommuteBar : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeOperatorBar N ℓ * heckeOperatorBar N ℓ' = heckeOperatorBar N ℓ' * heckeOperatorBar N ℓ
```

([`Definitions/Def_ModularCurve_HeckeModule.lean`, lines 16–27](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean#L16-L27)).

Two things are being asserted at once, and the note should keep them apart:

* `JZero N` is the **object** (the group playing the role of `J_0(N)(ℚ̄)`);
* `heckeOperatorBar N ℓ` is the **operator**, an additive endomorphism of it.

Once commutation holds, the individual operators generate a commutative
`ℤ`-subalgebra of `Module.End ℤ (JZero N)`, and `HeckeAlg = MvPolynomial
Nat.Primes ℤ` acts on `JZero N` through `heckeEvalBar` / `heckeModuleBar`
([`Def_ModularCurve_HeckeModule.lean`, lines 51 and 82](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean#L51-L84);
`HeckeAlg` and `heckeGen` at
[`Def_HeckeGalois_EichlerShimura.lean`, lines 14 and 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L14-L16)).
That module structure is the payoff: it is what later lets the development
speak of Hecke eigenspaces, Eisenstein ideals and newform eigenplanes in
`J_0(N)`, and what makes Galois and Hecke actions commute
([`Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.lean`, line 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.lean#L5)).

## 1. The curve, as a function field

`JZero N` is not built from a scheme. The curve `X_0(N)` enters only through
its field of modular functions:

```lean
def modularFunctionFieldFull : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ (divisorExpansions N)
```

where `divisorExpansions N = {qExpand ℚ d jq | d ∣ N, d ≠ 0}`, i.e.
`ℚ(j(q^d) : d ∣ N) ⊂ ℚ((q))`
([`Def_ModularCurve_X0.lean`, lines 297–306](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L297-L306)).
The substitution `q ↦ q^N` is `qExpand` / `qExpandₐ`
([lines 25 and 98](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L25-L105)).
Base change to the algebraic closure is

```lean
abbrev modularFunctionFieldBar :=
  laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
```

([`Def_ModularCurve_ArithmeticGalois.lean`, line 111](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean#L111)).

For the note, the honest reading is: this is `ℚ̄(X_0(N))`, obtained by
base-changing the `q`-expansion field. The fact that it really is a
one-variable function field over `ℚ̄` is a theorem, not a definition
(`ModularCurve.isCurveOver_modularFunctionFieldBar`, and the genus formula
`ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula`; see the def-page
gloss for [ModularCurve_ArithmeticGalois](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_ArithmeticGalois.html)).

## 2. The "Jacobian": `Pic0` of the function field

This is the construction the user asked to focus on. It is a *divisor class
group*, not a variety.

### 2.1 Places and divisors

A `Place K F` is a valuation subring `𝒪 ⊆ F` that contains `K`, is proper, and
is a principal ideal ring — i.e. the local ring of a closed point. From it one
gets the residue field, the degree `deg v = finrank_K κ(v)`, the normalized
order `ord_v`, the ramification index and the inertia degree
([`Def_AlgebraicCurve_DivisorClassGroup.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean),
def-page gloss [here](https://tianyipeng.github.io/fermats-last-theorem/def/AlgebraicCurve_DivisorClassGroup.html);
`Place` itself and the pull/push calculus live in
[`Def_AlgebraicCurve_DivisorPushPull.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean)).

```lean
abbrev Divisor K F := Place K F →₀ ℤ          -- finitely supported ℤ-valued functions
def degree (D : Divisor K F) : ℤ := ∑ v ∈ D.support, D v * v.deg
def degZero : AddSubgroup (Divisor K F) := degree.ker
def IsPrincipal (D : Divisor K F) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ v, D v = v.ord f
def principal : AddSubgroup (Divisor K F)
```

([`Def_AlgebraicCurve_DivisorClassGroup.lean`, lines 190–210](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L190-L210)).
The class `HasPrincipalDivisors K F` asserts that every nonzero `f` has a
degree-zero principal divisor; it is a hypothesis, not automatic, because the
general `Place`/`Divisor` API is stated for arbitrary field extensions:

```lean
abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal
abbrev Pic0 : Type _ :=
  Divisor.degZero ⧸ (Divisor.principal).addSubgroupOf Divisor.degZero
```

([lines 217–225](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L217-L225)).

### 2.2 The modular instance

```lean
abbrev JZero : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
```

([`Def_ModularCurve_ArithmeticGalois.lean`, line 115](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean#L115)).

So `JZero N` is **degree-zero divisor classes on `ℚ̄(X_0(N))`**, i.e. the group
of `ℚ̄`-points of the Jacobian. Two facts make this the right group and not a
formal shadow:

* `ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar` supplies the
  hypothesis, so `Pic0` is the genuine class group
  ([`Thm_..._hasPrincipalDivisors_modularFunctionFieldBar.lean`, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean#L10)).
* Over `ℚ̄` every place has degree one:
  `ModularCurve.deg_eq_one_modularFunctionFieldBar`, so `degree` is literally
  the sum of the multiplicities
  ([`Thm_..._deg_eq_one_modularFunctionFieldBar.lean`, line 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean#L12)).

This is the key conceptual point for the note: `J_0(N)(ℚ̄)` is realized as
`Div^0 / Prin`, with no `H^1`, no Abel–Jacobi map and no Riemann–Roch in play
in this theorem. The scheme-theoretic relative Jacobian
(`ModularCurve.exists_relJacobian_jZero`,
[`Thm_ModularCurve_exists_relJacobian_jZero.lean`, line 46](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_relJacobian_jZero.lean#L46))
is a *different* construction used elsewhere (Néron models, good reduction);
the note should say so explicitly to avoid a misreading.

## 3. The Hecke action: a divisor correspondence

### 3.1 The two degeneracy maps

The operator is built from the two standard maps `F_N → F_{Nℓ}`, both realized
as `ℚ`-algebra maps of the `q`-expansion fields:

```lean
def heckeAlphaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  IntermediateField.inclusion (laurentBaseChange_mono' L (full_degeneracy_le (dvd_mul_right N ℓ)))

def heckeBetaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  { heckeBetaBarRingHom L N ℓ with commutes' := ... }
```

([`Def_ModularCurve_HeckeOperator.lean`, lines 66 and 98](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean#L66-L104)).

* `heckeAlphaBar` is **inclusion of function fields** — the pullback of the
  forgetful projection `X_0(Nℓ) → X_0(N)` (it is the identity on underlying
  Laurent series).
* `heckeBetaBar` is **`q ↦ q^ℓ`** (`qExpand L ℓ`) — the pullback of the other
  degeneracy map, the one that quotients by the canonical `ℓ`-subgroup. Its
  action on series is recorded by `coe_heckeBetaBar`.

The def-page gloss is careful and worth quoting in the note: the module "only
constructs these maps: no primality of `ℓ` is assumed, `ℓ ∣ N` and `ℓ = 1` are
permitted, nothing is proved about the operators, and neither orientation is
identified with the classical action `a_n ↦ a_{nℓ} + ℓ a_{n/ℓ}` on
`q`-expansions" ([ModularCurve_HeckeOperator def page](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_HeckeOperator.html)).
The identification with the two geometric degeneracy morphisms `π` and `πw`
lives in separate theorems (`...pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi`,
`...restrictAlong_heckeBetaBar_of_comp_piw`); these are the results a math
narrative can lean on to say "the two standard degeneracy maps".

### 3.2 Pullback and pushforward on divisors

Along an integral map `φ : F →ₐ[K] F'` the two operations are, on a single
place,

```lean
-- pushforward: sum over the fibre, weighted by inertia degree
theorem pushforward_single (w : Place K F') (n : ℤ) :
    pushforward F (Finsupp.single w n) =
      Finsupp.single (w.restrict F) (n * w.inertiaDeg F)

-- pullback: weight by ramification index at the place above
theorem pullback_apply (D : Divisor K F) (w : Place K F') :
    pullback F' D w = w.ramificationIndex F * D (w.restrict F)
```

([`Def_AlgebraicCurve_DivisorPushPull.lean`, lines 453 and 574](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean#L453-L575)).
The hypotheses that control degrees and principality are

* `FundamentalIdentity K F F'`: for each `v`,
  `∑_{w | v} e_w · deg w = [F' : F] · deg v`;
* `PushforwardNormFormula`: the norm compatibility making `φ_*` send principal
  divisors to principal divisors;
* plus finiteness `Module.Finite F F'`.

They are packaged as the instance-free predicates `FundamentalIdentityAlong`,
`FiniteAlong`, `NormFormulaAlong`
([`Def_AlgebraicCurve_Correspondence.lean`, lines 28–47](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L28-L47)).

### 3.3 The correspondence, and where each hypothesis is used

A divisor correspondence is "pull back along one leg, push forward along the
other":

```lean
def correspondence : Divisor K F →+ Divisor K F :=
  (pushforwardAlong ψ hψ).comp (pullbackAlong φ hφ)          -- ψ_* ∘ φ^*
```

([`Def_AlgebraicCurve_Correspondence.lean`, line 137](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L137)).
It preserves degree-zero divisors when the fundamental identity holds along
the pullback leg `φ`, and preserves principal divisors when `ψ` is finite and
satisfies the norm formula; hence it descends to `Pic0`:

```lean
def correspondence : Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (degZeroCorrespondence φ ψ hφ hψ hFI) (...)
```

([line 183](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L183) —
note the hypothesis split: **fundamental identity on `φ`, finiteness + norm
formula on `ψ`**).

For the Hecke situation the roles are `φ = heckeBetaBar` (pullback leg) and
`ψ = heckeAlphaBar` (pushforward leg):

```lean
def heckeDivBar : Divisor ... →+ Divisor ... :=
  Divisor.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ) hβ hα

def heckePic0Bar (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) :
    Pic0 L (...) →+ Pic0 L (...) :=
  Pic0.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ) hβ hα hFI hfin hN
```

([`Def_ModularCurve_HeckeOperator.lean`, lines 136 and 141](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean#L136-L148)).
So, reading it mathematically,

`T_ℓ = (α_ℓ)_* ∘ (β_ℓ)^*` on divisor classes,

with `α_ℓ` the forgetful leg and `β_ℓ` the `q ↦ q^ℓ` leg. The transposed
orientation `heckeDivBarTranspose = (β_ℓ)_* ∘ (α_ℓ)^*` is also defined
([lines 157–168](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean#L157-L168)); the exchange argument will effectively show `T_ℓ` is self-transpose under the two legs.

### 3.4 The operator is total, with a junk branch

`heckeOperatorAlong` is a plain **total** definition: it takes the
correspondence when the four analytic inputs are available, and `0` otherwise.

```lean
def HeckeInputsAlong : Prop :=
  ∃ (_ : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ)),
    FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin

def heckeOperatorAlong : Pic0 L (...) →+ Pic0 L (...) :=
  if h : HeckeInputsAlong L N ℓ then ... heckePic0Bar ... else 0
```

([`Def_ModularCurve_HeckeOperatorTotal.lean`, lines 13 and 22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperatorTotal.lean#L13-L28)).

This "conditional operator with junk value `0`" is an encoding artefact, but it
has a visible consequence for the proof shape: the commutation proof begins by
splitting on `HeckeInputsAlong`, and in the junk branch **both** operators are
`0`, so the equation is `0 = 0`
([`S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean`, lines 18–33](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean#L18-L33)).
The note should mention this once, in a "Lean detours" box, and then never
rely on it: mathematically the interesting case is the branch where the
correspondence exists.

## 4. Proof chain at a glance

Read top-down; each arrow is an import/citation in the corresponding
`P2M/Sol` proof.

| Layer | Declaration | File |
|---|---|---|
| statement | `ModularCurve.HeckeOperatorsCommuteBar` | [`Def_ModularCurve_HeckeModule.lean:25`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean#L25) |
| all pairs from one exchange | `heckeOperatorsCommuteBar_of_heckeExchangeAt` | [`Thm_..._of_heckeExchangeAt.lean:9`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean#L9) |
| fixed pair, case split + `Pic0` descent | `heckeOperatorBar_comm_of_heckeExchangeAt` | [`Thm_..._comm_of_heckeExchangeAt.lean:9`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean#L9) |
| divisor commutation descends to `Pic0` | `Pic0.correspondence_correspondence_comm` | [`Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean:6`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean#L6) |
| the two composites agree on divisors | `heckeDivBar_comm_of_heckeExchangeAt` | [`Thm_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean:6`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean#L6) |
| composite = one "roof" correspondence | `heckeDivBar_heckeDivBar_of_heckeExchangeAt` | [`Thm_..._heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean:6`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean#L6) |
| the exchange input | `HeckeExchangeAt` | [`Def_ModularCurve_DegeneracyTower.lean:121`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L121) |
| general Weil exchange | `Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong` | [`Thm_..._pullbackAlong_pushforwardAlong_....lean:10`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10) |
| local crux | `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` | [`Thm_..._sum_ramificationIndex_mul_inertiaDeg_exchange.lean:10`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L10) |

The top-level `P2M` solution additionally discharges the geometric inputs that
produce the exchange: principal divisors (`hP`), separability in
characteristic zero, the function-field generation hypothesis, and the modular
polynomial data
([`S_ModularCurve_heckeOperatorsCommuteBar.lean`, lines 73–112](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar.lean#L73-L112)).

## 5. Junction 1: all primes from two primes

`heckeOperatorsCommuteBar_of_heckeExchangeAt` reduces the statement over all
prime pairs to a single "exchange" hypothesis at the common level
`M = N · ℓ · ℓ'`:

* if `ℓ = ℓ'`, the equation is `rfl` (same operator);
* otherwise it sets `M = Nℓℓ'`, obtains `HasPrincipalDivisors` at levels
  `Nℓ`, `Nℓ'`, `M`, and calls `heckeOperatorBar_comm_of_heckeExchangeAt`
  twice — once for `(ℓ, ℓ')` and once for `(ℓ', ℓ)`
  ([`S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean`, lines 13–23](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean#L13-L23)).

Mathematically this is the observation that two distinct primes are handled
symmetrically, and that it suffices to build a common level where both
correspondences live.

## 6. Junction 2: from divisor exchange to operator commutation

`HeckeExchangeAt` is the geometric heart. Spelled out, with
`u = towerInclBar : F_{Nℓ} → F_M` and `u' = towerSubstBar : F_{Nℓ'} → F_M`
(the map `q ↦ q^ℓ` into level `M`), it says

```
β_ℓ^* ( (α_{ℓ'})_* D )  =  u_* ( (u')^* D )        for every divisor D on F_{Nℓ'} .
```

([`Def_ModularCurve_DegeneracyTower.lean`, lines 121–133](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L121-L133)).
The two legs of the square commute by construction:

```lean
theorem heckeSquareBar_commutes :
    (towerInclBar L h₁).comp (heckeBetaBar L N ℓ) =
      (towerSubstBar L (N * ℓ') ℓ h₂).comp (heckeAlphaBar L N ℓ')
```

([line 104](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L104-L107)):
both sides are `q ↦ q^ℓ` followed by inclusion into level `M`.

`heckeOperatorBar_comm_of_heckeExchangeAt` then

1. splits on `HeckeInputsAlong` (junk branch as in §3.4);
2. rewrites both operators as `Pic0.correspondence` (`heckeOperatorAlong_eq`);
3. applies `Pic0.correspondence_correspondence_comm`, which reduces a
   `Pic0` identity to the divisor identity by `Pic0.mk_surjective` — the
   quotient is handled by choosing a representative
   ([`S_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean));
4. supplies that divisor identity from `heckeDivBar_comm_of_heckeExchangeAt`.

Note the mathematical content of step 3: because `Pic0` is a *quotient* by
principal divisors, the whole commutativity question happens at the divisor
level and then descends. Nothing about principal divisors is needed for the
commutation itself beyond well-definedness.

## 7. Junction 3: both composites are the same roof

This is where the two primes are actually exchanged. The key lemma is

```
heckeDivBar_ℓ (heckeDivBar_{ℓ'} D)
  = correspondence (towerSubstBar N (ℓ·ℓ')) (towerInclBar : F_N → F_M) D
```

([`Thm_..._heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean`, line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean#L6)).
In symbols, starting from `T_ℓ T_{ℓ'} D = (α_ℓ)_* (β_ℓ)^* (α_{ℓ'})_* (β_{ℓ'})^* D`:

1. `HeckeExchangeAt (ℓ, ℓ')` replaces `(β_ℓ)^* (α_{ℓ'})_*` by
   `(incl)_* (subst_ℓ)^*`;
2. `(α_ℓ)_* (incl)_* = (incl')_*` and `(subst_ℓ) ∘ β_{ℓ'} = subst_{ℓℓ'}`
   (the latter is `towerSubstBar_comp_heckeBetaBar`, i.e.
   `qExpand_qExpand`).

Running the same argument with `ℓ` and `ℓ'` swapped gives the roof with
`subst_{ℓ'ℓ}`; since `ℓ'ℓ = ℓℓ'` in `ℕ` (and `qExpand_qExpand` composes
accordingly), `correspondence_congr` identifies the two roofs
([`S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean`, lines 24–26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean#L24-L26)).

So the mathematical one-liner the note should extract is:

> Two Hecke correspondences commute because each factor can be moved past the
> other across the commuting degeneracy square; both orders collapse to the
> single correspondence through the common level `Nℓℓ'` given by
> `q ↦ q^{ℓℓ'}`, and `ℓℓ' = ℓ'ℓ`.

## 8. The crux: exchanged legs in a linearly disjoint square

The exchange input `HeckeExchangeAt` is an instance of a general theorem about
a **commuting square of function fields**

```
        a : F → A
   b : F → B        with  b' ∘ b = a' ∘ a,
        a' : A → E
   b' : B → E
```

asserting

```
b^* ( a_* D )  =  (b')_* ( (a')^* D ) .
```

Stated in full, with the hypotheses that `E` is generated by `A` and `B` over
`F` and that the degrees are multiplicative
(`[E:F] = [A:F]·[B:F]`), plus finiteness and separability of `E/F`:

```lean
theorem AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (a : F →ₐ[K] A) (b : F →ₐ[K] B) (a' : A →ₐ[K] E) (b' : B →ₐ[K] E)
    (hsq : b'.comp b = a'.comp a) (hfin : FiniteAlong K (a'.comp a))
    (hsep : SeparableAlong K (a'.comp a))
    (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
    (hLD : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b)
    (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D) =
      Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D)
```

([`Thm_..._pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10);
def-page gloss: "Push–pull exchange for a linearly disjoint square of fields",
[AlgebraicCurve_Correspondence](https://tianyipeng.github.io/fermats-last-theorem/def/AlgebraicCurve_Correspondence.html)).

### 8.1 How it is proved

The proof reduces to a single place and then to a finite sum over the
**bifibre** `T = {W : W|_A = w_A, W|_B = w_B}`. Applying
`pushforwardAlong_single` and `pullbackAlong_single` turns both sides into
multiples of the same target place, and the identity becomes the numerical
statement

```
∑_{W ∈ T} e_{W/A} · f_{W/B}  =  f_{w_A/F} · e_{w_B/F} ,
```

where `e` is the ramification index and `f` the inertia degree
([`S_AlgebraicCurve_Divisor_..._pullbackAlong_....lean`, lines 86–110](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L86-L110)).
This is exactly `Place.sum_ramificationIndex_mul_inertiaDeg_exchange`
([`Thm_..._sum_ramificationIndex_mul_inertiaDeg_exchange.lean`, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L10)).

### 8.2 The local statement

Its proof (255 lines in `P2M/Sol`) is a place-theoretic computation:

1. reduce to the **Galois case** by passing to the normal closure `Env F E` of
   `E/F` inside `AlgebraicClosure E`, where ramification/inertia behave
   uniformly;
2. use multiplicativity of `e` and `f` in towers
   (`ramificationIndex_eq_mul_ramificationIndex_restrict`,
   `inertiaDeg_eq_mul_inertiaDeg_restrict`) to express each summand as
   `e_{W/F} f_{W/F}` times the fixed factor
   `e_{w_A/F} f_{w_B/F}`;
3. apply the Galois bifibre count
   `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` together with
   `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`;
4. cancel the positive factor `e_{w_A/F} · f_{w_B/F}`
   ([`S_..._exchange.lean`, lines 160–255](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L160-L255)).

Mathematically this is the classical **exchange / projection formula** for a
fibre square of curves: pullback after pushforward can be rewritten as
pushforward after pullback precisely when the two legs are linearly disjoint
(`E = F(A,B)`, `[E:F] = [A:F][B:F]`) and the covers are separable — the
ramification indices of one leg pair against the inertia degrees of the other.
The note should present the local statement as the real theorem and the
divisor identity as its integrated form.

### 8.3 The Hecke instance

The Hecke square satisfies all hypotheses:

* `hsq` is `heckeSquareBar_commutes`;
* `hfin`/`hsep` come from `finiteAlong_comp` and
  `separableAlong_of_charZero` on the integral maps
  ([`S_ModularCurve_heckeOperatorsCommuteBar.lean`, lines 29–46 and 98–105](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar.lean#L29-L105));
* `hgen` is the function-field generation statement at level `M`;
* `hLD`, the degree of the diagonal in the Hecke square, is
  `finrankAlong_towerSubstBar_comp_heckeAlphaBar`
  ([`Thm_..._finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean`, line 11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean#L11)),
  which is the `[Nℓℓ' : Nℓ'] = ℓ`-type degree count; it needs `ℓ ≠ ℓ'`.

## 9. What the note should *not* claim

* **Not a scheme.** The Jacobian here is `Pic0` of `ℚ̄(X_0(N))` as a group; no
  representability, no universal property, no `𝔾_m`/Pic functor.
* **No Riemann–Roch / Abel–Jacobi.** The commutation proof never uses divisors
  of functions to construct classes beyond the quotient by principals, and
  never invokes the theorem that every degree-zero class has a representative
  of degree zero (that is `Pic0` by construction).
* **Orientation is a convention.** The Lean picks `T_ℓ = (α_ℓ)_* (β_ℓ)^*` with
  `α` the inclusion and `β` the `q ↦ q^ℓ` leg; the def page explicitly
  disclaims the identification with `a_n ↦ a_{nℓ} + ℓ a_{n/ℓ}`. A note that
  wants the classical formula must import that identification separately.
* **Junk branch.** `heckeOperatorAlong` is `0` when its analytic inputs are
  unavailable; the theorem is unconditional, and the junk case is a formal
  case split, not mathematics.
* **Bad primes are not excluded.** The statement quantifies over all primes
  `ℓ : Nat.Primes`; nothing separates `ℓ ∣ N`. This is a statement about the
  pairwise commutativity of the full family, not about a chosen Hecke algebra
  of level `N` away from the level.

## 10. Suggested note outline (math-first)

1. **Motivation.** `T_ℓ` should act on `J_0(N)`; the development needs the
   action to be a ring action, hence needs `T_ℓ T_{ℓ'} = T_{ℓ'} T_ℓ`.
2. **The curve as a `q`-expansion field.** `F_N = ℚ(j(q^d) : d ∣ N)`,
   `ℚ̄(X_0(N)) = ℚ̄ ⊗ F_N`. State `isCurveOver` as a fact, not as a definition.
3. **Places, divisors, `Pic0`.** The three-line construction
   `Divisor = Place →₀ ℤ`, `deg`, `principal`, `Pic0 = Div^0/Prin`; degree-one
   places over `ℚ̄`; `HasPrincipalDivisors`.
4. **Why `Pic0` is the Jacobian.** Explain that over an algebraically closed
   field the `ℚ̄`-points of `J_0(N)` are exactly degree-zero divisor classes;
   flag that the scheme-theoretic Jacobian is a separate construction used for
   Néron models.
5. **The two degeneracy maps.** `α` (forget) and `β` (`q ↦ q^ℓ`), with their
   geometric meaning; the pullback/pushforward formulas.
6. **The Hecke correspondence.** `T_ℓ = α_* β^*`; the hypotheses that make it
   descend to `Pic0` (`FundamentalIdentity` on `β`, finiteness + norm formula
   on `α`).
7. **The exchange theorem.** State the linearly disjoint square identity and
   prove the local bifibre identity; this is the mathematical heart.
8. **Assembly.** `T_ℓ T_{ℓ'} = T_{ℓ'} T_ℓ` via the common roof at `Nℓℓ'`;
   the commutative `ℤ`-subalgebra and the `HeckeAlg`-module structure.
9. **Lean detours** (short): total-operator junk branch, `p2m_exact_reverting`,
   `attribute [-instance]`/`[-simp]` noise in the `Thm_` wrappers.

## 11. Citation index

Pinned at `aa2d8b3` (local clone `~/proj/fermats-last-theorem`, equal to
`anthropics/fermats-last-theorem@aa2d8b3`).

Definitions — raw sources:

* [`Def_ModularCurve_X0.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean) — `qExpand` (25), `qExpandₐ` (98), `modularFunctionFieldFull` (305).
* [`Def_ModularCurve_ArithmeticGalois.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean) — `modularFunctionFieldBar` (111), `JZero` (115).
* [`Def_AlgebraicCurve_DivisorClassGroup.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) — `HasPrincipalDivisors` (217), `Pic0` (223).
* [`Def_AlgebraicCurve_DivisorPushPull.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean) — `pushforward` (448), `PushforwardNormFormula` (483), `pullback` (549), `pullback_apply` (574), `FundamentalIdentity` (611).
* [`Def_AlgebraicCurve_Correspondence.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean) — `correspondence` on divisors (137) and on `Pic0` (183).
* [`Def_ModularCurve_HeckeOperator.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean) — `heckeAlphaBar` (66), `heckeBetaBar` (98), `heckeDivBar` (136), `heckePic0Bar` (141).
* [`Def_ModularCurve_HeckeOperatorTotal.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperatorTotal.lean) — `HeckeInputsAlong` (13), `heckeOperatorAlong` (22).
* [`Def_ModularCurve_HeckeModule.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean) — `heckeOperatorBar` (16), `HeckeOperatorsCommuteBar` (25), `heckeModuleBar` (82).
* [`Def_ModularCurve_DegeneracyTower.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean) — `towerInclBar` (27), `towerSubstBar` (54), `heckeSquareBar_commutes` (104), `HeckeExchangeAt` (121).

Theorems (public wrappers):

* [`Thm_ModularCurve_heckeOperatorsCommuteBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean) (9).
* [`Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean) (9).
* [`Thm_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean) (9).
* [`Thm_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean) (6).
* [`Thm_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean) (6).
* [`Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean) (6).
* [`Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean) (10).
* [`Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean) (10).
* [`Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean) (12).
* [`Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean) (10).
* [`Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.lean) (5).
* [`Thm_ModularCurve_exists_relJacobian_jZero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_relJacobian_jZero.lean) (46).

Proof modules (`P2M/Sol`):

* [`S_ModularCurve_heckeOperatorsCommuteBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar.lean).
* [`S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean).
* [`S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean).
* [`S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean).
* [`S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean).
* [`S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean).

Generated English glosses (hosted by the author):

* [ModularCurve_HeckeModule](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_HeckeModule.html)
* [ModularCurve_HeckeOperator](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_HeckeOperator.html)
* [ModularCurve_DegeneracyTower](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_DegeneracyTower.html)
* [AlgebraicCurve_Correspondence](https://tianyipeng.github.io/fermats-last-theorem/def/AlgebraicCurve_Correspondence.html)
* [AlgebraicCurve_DivisorClassGroup](https://tianyipeng.github.io/fermats-last-theorem/def/AlgebraicCurve_DivisorClassGroup.html)
* [ModularCurve_ArithmeticGalois](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_ArithmeticGalois.html)

## 12. Open questions before writing the note

1. Does the note want the classical `a_n ↦ a_{nℓ} + ℓ a_{n/ℓ}` formula? If so,
   a separate identification theorem is needed (the def page says it is not in
   `Def_ModularCurve_HeckeOperator`). Candidate: the `heckeOperatorBar_points_eq_comp_of_transform`
   / `pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso` results.
2. Should the note treat the scheme-theoretic Jacobian (`exists_relJacobian_jZero`)
   at all, or only flag it? The commutation theorem does not use it.
3. How much of §8.2 (normal closure, Galois bifibre count) to unwind? `base/`
   style would unwind it to the level of the fundamental identity
   `∑ e_w f_w = [E:F]`, which is standard and self-contained.
