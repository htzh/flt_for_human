# TOPIC l2 — the `Γ₁` / diamond vocabulary

Work order for SET-2 of [PORTING-Level.md](../PORTING-Level.md).
Target module: `FLTForHuman/ModularForms/Level/Diamond.lean`, namespace
`ModularForm.Level`, pinned `aa2d8b3`, mathlib `v4.34.0`. Prerequisite: SET-1's
`Defs/GammaH.lean` and the existing `Defs/HeckeRepresentatives.lean`.

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. `lake env lean <module>` **~4 s**, `lake build
> <module>` **~2–5 s**, a heartbeat timeout **~15–20 s then an error**, a healthy
> full `lake build` **seconds to about a minute**. Run every build under
> `timeout 60 lake env lean <file>` / `timeout 90 lake build <module>`; expect
> ≤ 30 s; never raise `maxHeartbeats`; tell a blow-up (high user CPU) from lock
> contention (~0 CPU) by `time`.

## The mathematics

`Γ₁(M)` is the stabiliser of the point `P` in the level structure; equivalently
the kernel of the lower-right character. The *diamond operator* `⟨d⟩` is the
slash by any `γ ∈ Γ₀(M)` with `γ₁₁ ≡ d (mod M)`; two such lifts differ by an
element of `Γ₁(M)`, so `⟨d⟩` is well defined on `Γ₁(M)`-forms. Mathlib has
`Gamma1` and `Gamma0Map`; it has no `IsDiamondLift` and no diamond operator.
Base note: [base/018](../../../base/018-congruence-subgroups-and-invariance.md)
§4.4–§4.5.

## The declarations

Statements verbatim from `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean`,
except the one strengthening marked **(Tier 2)**.

```lean
-- :193, :207
def wt (N p : ℕ) (x : OnePoint (ZMod p)) : ZMod N := x.elim (p : ZMod N) (fun _ => 1)
def lift (σ : SL(2, ℤ)) (x : OnePoint (ZMod p)) : SL(2, ℤ) := x.elim σ (fun _ => 1)

-- :213, :219, :225, :231, :239, :371
theorem lift_mem (σ) (hσ : σ ∈ Gamma0 N) (x) : lift σ x ∈ Gamma0 N
theorem lift_apply_one_one (σ) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p) (x) :
    (((lift σ x) 1 1 : ℤ) : ZMod N) = wt N p x
theorem d_mul (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N) :
    (((γ₁ * γ₂) 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N)
theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1
theorem mem_Gamma1_of_d_eq_one (hγ : γ ∈ Gamma0 N) (hd : ((γ 1 1 : ℤ) : ZMod N) = 1) :
    γ ∈ Gamma1 N
theorem isUnit_d (hγ : γ ∈ Gamma0 N) : IsUnit ((γ 1 1 : ℤ) : ZMod N)
theorem isUnit_wt (hp : p.Prime) (hpN : ¬ p ∣ N) (x) : IsUnit (wt N p x)

-- :469, :474, :482, :492, :504, :510
def IsDiamondLift (d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ Gamma0 M ∧ ((γ 1 1 : ℤ) : ZMod M) = (d : ZMod M)
theorem exists_isDiamondLift_of_coprime (h : Nat.Coprime d M) : ∃ γ : SL(2, ℤ), IsDiamondLift M d γ
theorem IsDiamondLift.coprime (h : IsDiamondLift M d γ) : Nat.Coprime d M
theorem conj_mem_Gamma1 (hγ : γ ∈ Gamma0 M) (hx : x ∈ Gamma1 M) : γ * x * γ⁻¹ ∈ Gamma1 M
theorem mem_coe_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (mapGL ℝ γ) = x
theorem toConjAct_inv_smul_coe_Gamma1 (hγ : γ ∈ Gamma0 M) :
    toConjAct (mapGL ℝ γ)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M)

-- :535, :543, :556, :592
def slashOfMemGamma0 (hγ : γ ∈ Gamma0 M) (f : CuspForm (Γ₁ℝ M) k) : CuspForm (Γ₁ℝ M) k
def slashLinOfMemGamma0 (hγ : γ ∈ Gamma0 M) :
    CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k
theorem slash_eq_slash_of_isDiamondLift (hγ : IsDiamondLift M d γ) (hγ' : IsDiamondLift M d γ')
    (f : CuspForm (Γ₁ℝ M) k) :
    ⇑f ∣[k] (mapGL ℝ γ) = ⇑f ∣[k] (mapGL ℝ γ')
def diamondLinOne (d : ℕ) : CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k
```

**(Tier 2) strengthen `HeckeRepresentatives.heckeRep_mul`** to the pin's full
statement (`Def_CuspForm_Gamma1HeckeOperators.lean:281–285`), re-adding the
`g' 1 1` and `wt` conjuncts the Γ₀ effort deliberately dropped:

```lean
theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ Gamma0 N)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      ((g' 1 1 : ℤ) : ZMod N) * wt N p x = ((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x) ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x)
```

The two Γ₀ consumers in `HeckeInvariance.lean` only destructure
`⟨g', hg', hmul⟩`, so adding a middle conjunct changes the pattern-match arity
there; update them to `⟨g', hg', _, hmul⟩`. Check with
`timeout 90 lake build FLTForHuman.ModularForms.HeckeInvariance` (and
`…HeckeT`).

## The reorg (the point of this topic)

`WeightOne/` has grown private copies of the `Γ₁` conjugation lemmas. Promote
once here and replace each copy by an import:

| private copy | file:line | replace with |
|---|---|---|
| `Gamma_le_Gamma1` | `WeightOne/Gamma1IntegralBasis.lean:148` | the one-liner from `mem` (public) |
| `Gamma_le_Gamma1` | `WeightOne/Gamma1Basis.lean:3345` | same |
| `conj_mem_Gamma1` | `WeightOne/Gamma1IntegralBasis.lean:939` | `Level.Diamond.conj_mem_Gamma1` |
| `conj_mem_Gamma1` | `WeightOne/Gamma0Rationality.lean:1664` | same |
| `neg_one_mem_Gamma1` | `WeightOne/Gamma1IntegralBasis.lean:604`, `WeightOne/Gamma1Basis.lean:4171` | `neg_one_mem_Gamma1` here (extra `N ∣ 2` hypothesis) |
| `conj_mem_Gamma` | `WeightOne/Gamma1Basis.lean:3341`, `WeightOne/Gamma0Rationality.lean:1680` | a public `Gamma`-conjugation lemma here |
| `T_mem_Gamma1` / `T_pow_mem_Gamma1` | `WeightOne/Gamma1Basis.lean:1228`, `WeightOne/Gamma0Rationality.lean:1657` | public `T`-membership here |

Rules: replace one file at a time; build after each; do not promote a copy whose
statement carries extra hypotheses (give it its own public name instead). Keep
the `grep -c` before/after counts in the log.

## Verification

- Statements: `Def_CuspForm_Gamma1HeckeOperators.lean` appended to `SOURCES`;
  `Level/Diamond.lean` to `PORT_FILES`. The Tier-2 `heckeRep_mul` statement is
  longer than the current port copy, so the checker will diff it against the
  pin's public block (already in `SOURCES`, via `HeckeRepresentatives`).
- Consumer: extend `spec/LevelConsumer.lean` with a `[diamond]` zone —
  `exists_isDiamondLift_of_coprime` at `M = 2`, `diamondLinOne 1 = LinearMap.id`
  (`diamondLinOne_one`), and `slash_eq_slash_of_isDiamondLift` on a concrete
  pair.
- `#print axioms` clean; full `lake build` green with 0 warnings.

## Definition of done

Module green; checker 0/0; consumer 0 errors; the `WeightOne` copies replaced
with a measured `grep -c` saving; `logs/level-port.md` §2; `README.md` rows.
