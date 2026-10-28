# WORKORDER — the leaves block's six row orders (LV-1 … LV-6)

**SET**: [SET-LEAVES.md](SET-LEAVES.md) §0–§5. **Six orders, two waves**, one agent per order,
three in flight. This file is the whole hand-off: each section is self-contained (statement, pin
source, home, vocabulary, traps, gates). Do not re-plan the cut, do not roam the pin outside the
files named in your section.

## House rules (every order)

- **Read the pin, not this file's paraphrase.** The statement authority is the `Theorems/` wrapper
  (the text below is its exact statement); the proof source is the `P2M/Sol/S_*.lean` file named in
  your section. The pin clone is at `~/proj/fermats-last-theorem`, pinned `aa2d8b3`.
- **Port whole declarations, never a weakened statement.** The `theorem` header line below is the
  checker's text: spell binders exactly as the wrapper does. A `def`'s pin binders stay in their
  `variable … in` form. Where the pin states a declaration `private` in the `S_` file and again in
  the public wrapper, state it **once**, public, at the wrapper's name.
- **Adapters stay `private`.** A lemma whose only consumer is your headline and which only re-ties
  an existing API is `private`; real mathematics is public at the pin's name.
- **Do not edit another order's files**, any `spec/` file, `spec/decl_markers.tsv`, the lakefile, or
  `spec/old_check_stmts.py`. Do not add a module to make a diff go away.
- **A module's `spec-pin:` block names its pin sources**: one line per `Theorems/Thm_*.lean` wrapper
  and one per `P2M/Sol/S_*.lean` copy transcribed. Never add a `spec-pin:` line for a wrapper whose
  statement is not in the same edit: that is a false ported marker and the tree's worst failure.
- **Build discipline (copy).** Edit loop
  `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is **low
  on purpose**: a declaration that exceeds it has an instance-inference defect, and the low cap is
  what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
  `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
  wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. Log
  output in `lean/tmp/`. Every command under 2 minutes.
- **Blockers: raise one at first belief, then keep working.** If a name cannot be matched, a
  prerequisite is unported, or an edit to a module outside your section is needed, send a short
  message — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`" — and continue with whatever is
  independent. Never work around a hub defect locally, never grind out a diagnosis first.
- **Report at the end** with: the modules and their line counts, the added declaration list, the
  `check_port` counts, the axiom probe, the dedup count, the build bound, and the friction entries.
- **Gates, as exact commands** (from `lean/`, `<M>` = your module's path and dotted name):
  1. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <M>.lean` → silent, zero warnings.
  2. `flock /tmp/lean-build.lock lake build <M.dotted>` → success (background channel on a busy
     tree, FR-0060).
  3. `python3 spec/check_port.py --force <M>.lean` → every added declaration `ok`, 0 mismatch /
     0 missing / 0 own (the only exceptions are the two recorded `JqCoefficients` `own:` rows).
  4. `#print axioms` on every headline in a `lean/tmp/` probe file →
     `[propext, Classical.choice, Quot.sound]`.
  5. `python3 tools/deps/dedup.py --within --tier shape <M>.lean` → 0 clusters.
  6. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option`; no linter
     suppression; no `git`; no tree build; every command under 2 minutes.

---


## LV-1 — L-siegel: the level-`N` Bernoulli weight and the addition law of the Siegel unit

**Silo**: 1,158 (504 + 323 + 176 + 155). **Net**: ≈917. **Wave A.**
**Files**: **new** `lean/FLTForHuman/ModularCurve/SiegelUnit/BernoulliWeight.lean` (rows 504, 323,
176) and insert row 155 into `lean/FLTForHuman/ModularCurve/SiegelUnit/Basic.lean`.
**Pin**: wrappers and `S_` copies of the four rows:
`Theorems/Thm_ModularCurve_SiegelUnit_{mem_span_levelBernoulliWeight_dilate_iff_even,
sum_totient_mul_levelBernoulliWeight_dilate_eq_zero, sum_levelBernoulliWeight_add_mul,
siegelFun_add_level}.lean`
and `P2M/Sol/S_ModularCurve_SiegelUnit_{…}.lean` of the same four names.

### ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even
```lean
theorem ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even (N : ℕ) [NeZero N]
    (φ : ZMod N → ℚ) :
    φ ∈ Submodule.span ℚ (Set.range fun s : ZMod N => fun r : ZMod N =>
        ((6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2 : ℤ) : ℚ)) ↔
      ∀ r : ZMod N, φ (-r) = φ r := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero
```lean
theorem ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero (N : ℕ) [NeZero N]
    (s : ZMod N) (hs : s ≠ 0) :
    ∑ r : ZMod N,
        (((N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N) : ℕ) : ℤ) *
          (6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2) = 0 := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul
```lean
theorem ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul (N : ℕ) [NeZero N] (p r : ℤ) :
    ∑ s : ZMod N,
        (6 * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) ^ 2
          - 6 * (N : ℤ) * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) + (N : ℤ) ^ 2) =
      (N : ℤ) * (6 * (p % (Int.gcd r N : ℤ)) ^ 2
        - 6 * (Int.gcd r N : ℤ) * (p % (Int.gcd r N : ℤ)) + (Int.gcd r N : ℤ) ^ 2) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.SiegelUnit.siegelFun_add_level
```lean
theorem ModularCurve.SiegelUnit.siegelFun_add_level (N : ℕ) (r s : ℤ) :
    (∀ z : ℂ, siegelFun N r (s + N) z =
        Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * siegelFun N r s z) ∧
    (∀ τ : UpperHalfPlane, siegelFun N (r + N) s (τ : ℂ) =
        -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) * siegelFun N r s (τ : ℂ)) := by sorry  -- PIN PROOF (do not transcribe)
```

**Vocabulary.** Mathlib only for the first three (`ZMod`, `Nat.totient`, `Int.gcd`,
`Mathlib.NumberTheory.ZetaValues`, `Mathlib.Analysis.Fourier.ZMod`,
`Mathlib.NumberTheory.DirichletCharacter.*`, `Mathlib.Analysis.SumOverResidueClass`,
`Mathlib.Analysis.PSeries`). Row 155 imports `Defs/SiegelFunction.lean` (`siegelFun`) and uses
`SiegelUnit/Basic.lean`'s private engine.

**What to write.** (1) The pin's `wt` (the level-`N` weight polynomial, `S_…:22`, a `def`) public at
its pin name, then row 504 as the span characterisation — note the wrapper inlines `wt`, so the
headline's statement is the wrapper's and `wt`'s is the `S_` copy's. (2) The 323/176 shared prelude
once (`sum_zmod_comp_val_affine` 36, `sum_range_affine_unit` 32, `sum_zmod_Bt` 20,
`emod_progression` 17, `gcd_bookkeeping` 15, `sum_range_Bt_aux` 11, and the rest of that file's
public block), then 323 and 176. (3) Row 155 in `SiegelUnit/Basic.lean`: the `_add_level` family
(`qa_add_level`, `pref_add_level`, `sprod_add_level`, and the three `_left` forms) public at the
pin's names, then the headline.

**Traps.** (i) 504's `S_` file is analytic: the Fourier series of the second Bernoulli polynomial
(`hasSum_cos_div_sq`, `hasSum_cos_wt`, `tsum_psi_eq_sum_residues`,
`stdAddChar_eq_cosZ_add_sinZ`, `eq_zero_of_convolution`) is the route; `psi_eq_zero` and
`mem_span_iff_even` are its two steps. (ii) `zmod` division/totient bookkeeping is `Nat` arithmetic
on `r.val`; the pin's `emod_progression` is the one place to be careful with `ZMod.val` casts.
(iii) Row 155: keep `SiegelUnit/Basic.lean`'s existing `private` engine `private`; use
`siegelFun_eq`, `qa`, `pref`, `sprod`, `multipliable_one_sub_pow_mul`, `qa_ne_zero` from it. The
module already has the two `siegelFun` headlines of MC-5 — do not touch them.
(iv) `Complex.exp` arguments: keep the pin's `Real.pi`/`Complex.I` spelling and the `↑N`
coercions; the two conclusions of 155 are different (`z : ℂ` vs `τ : ℍ`).

**Gates.** As the house rules. Wire: two `spec-pin:` lines per row (its wrapper and its `S_` copy)
in the module carrying it — six in the new module, one pair in `SiegelUnit/Basic.lean`.


## LV-2 — L-starbank (norm): the σ-norm of Δ, the closure and the one-point case

**Silo**: 995 (471 + 304 + 220). **Net**: ≈819. **Wave A.**
**File**: **new** `lean/FLTForHuman/ModularCurve/StarBank/Norm.lean`.
**Pin**: `Theorems/Thm_ModularCurve_StarBank_{deltaNorm,closure,onePoint}.lean` and
`P2M/Sol/S_ModularCurve_StarBank_{deltaNorm,closure,onePoint}.lean`.

### ModularCurve.StarBank.deltaNorm
```lean
theorem ModularCurve.StarBank.deltaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.StarBank.closure
```lean
theorem ModularCurve.StarBank.closure {K : Type*} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) {M : ℕ} {G R : Polynomial K}
    (hstar : Polynomial.aeval (jqModC K) G *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p)
    (hpress : R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))))
    (hnorm : (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1)) :
    ∃ c : K, c ≠ 0 ∧ G.comp R ∣ Polynomial.C c * G ^ (p + 1) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.StarBank.onePoint
```lean
theorem ModularCurve.StarBank.onePoint {K : Type*} [Field K] {M : ℕ}
    (hM : (M : K) ≠ 0) {c : K} (hc : c ≠ 0) {β₀ : K}
    (hstar : Polynomial.aeval (ModularCurve.jqModC K)
          (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) ^ M
        = 1) :
    ∃ γ : K, γ ≠ 0 ∧
      (ModularCurve.jqModC K - HahnSeries.C β₀)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)
        = HahnSeries.C γ := by sorry  -- PIN PROOF (do not transcribe)
```

**Vocabulary.** `ModularCurve.qTwist`/`qTwist_single` (`Defs/Twist.lean`), `qExpand` and its
coefficient lemmas (`Defs/Laurent.lean`), `etaProd`, `jNum`, `jqModC`, `jqNModC`
(`Defs/Jq.lean`, `Defs/JqCoeff.lean`), `ModularCurve.StarBank.press` and the existing
`StarBank` API (`ModularCurve/ModularPolynomialStarBank.lean`, **import only — it is legacy, do not
edit**), mathlib's `PowerSeries.WithPiTopology` (`multipliable_one_sub_X_pow`, `tprod`, `rescale`,
`expand`) and `HahnSeries.ofPowerSeries`.

**What to write.** The `W1` prelude each `S_` file carries, once per lemma that a row needs, at the
pin's names; then the three headlines once each, public, at the wrapper's name (the pin declares
them `private` in its `S_` file and restates them in the wrapper — one statement, the wrapper's).

**Traps.** (i) 471 is a **topological product** computation: `map_etaProd_eq_tprod`,
`rescale_tprod_one_sub_X_pow`, `expand_tprod_one_sub_X_pow`, `prod_one_sub_root_mul`,
`prod_twist_factor`, then the `uFam`/`hFam`/`gFam`/`g'Fam`/`cFam` family and `regroup`. Read mathlib's
`PowerSeries.WithPiTopology` API before writing; the `tprod`/`multipliable` congruence is what
bites. (ii) `closure`'s four hypotheses are the star datum; keep the wrapper's binder order and the
`∏ b ∈ Finset.range p` spelling. (iii) `onePoint` needs the `C`-valued coefficient comparison
(`coeff_C_mul`, `coeff_C_of_ne`, `eq_C_of_pow_eq_C`) and the order/leadingCoeff computation
(`leadingCoeff_laurent_pow`, `order_laurent_pow`). (iv) `coeff_one_etaProd` is **not** needed by any
of these three rows and is not to be promoted: the pin's norm argument uses the `tprod` family.
(v) Do not import `Defs/QExpandCharP`: no characteristic-`p` argument is in this order.

**Gates.** As the house rules. Wire: two `spec-pin:` lines per row (wrapper + `S_` copy), six in the
new module.


## LV-3 — L-starbank (Hasse): the star polynomial, the root count, Eisenstein integrality; and the tate `c₄`

**Silo**: 760 (210 + 192 + 161 + 156 + 41). **Net**: ≈501. **Wave A.**
**Files**: **new** `lean/FLTForHuman/ModularCurve/StarBank/Hasse.lean` (rows 210, 192, 161, 156) and
insert row 41 into `lean/FLTForHuman/ModularCurve/Defs/TateFormal.lean` (already wired and migrated;
add its two `spec-pin:` lines).
**Pin**: `Theorems/Thm_ModularCurve_StarBank_{starK,count,eisInt_series,eisInt_not_dvd_num}.lean`,
`Theorems/Thm_ModularCurve_c4_tateLaurent.lean`, and the matching `P2M/Sol/S_*.lean`.

### ModularCurve.StarBank.starK
```lean
theorem ModularCurve.StarBank.starK (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hHasse : 5 ≤ ℓ → ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
        (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
        ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
        ∧ HahnSeries.ofPowerSeries ℤ ℤ T
            = Polynomial.aeval (jqModC ℤ) G
              * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                  * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ (ℓ - 1)) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.StarBank.count
```lean
theorem ModularCurve.StarBank.count {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ}
    (hp0 : (p : K) ≠ 0) (hp2 : 2 ≤ p) {R G : Polynomial K} (hR : R.Monic)
    (hRdeg : R.natDegree = p) (hG : 0 < G.natDegree) {c : K} (hc : c ≠ 0)
    (hdvd : G.comp R ∣ Polynomial.C c * G ^ (p + 1)) :
    ∃ β₀ : K, (∀ β : K, G.IsRoot β → β = β₀) ∧
      R = (Polynomial.X - Polynomial.C β₀) ^ p + Polynomial.C β₀ := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.StarBank.eisInt_series
```lean
theorem ModularCurve.StarBank.eisInt_series {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ)
        = ((bernoulli (ℓ - 1)).num : ℂ) • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))
      ∧ PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num
      ∧ ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.StarBank.eisInt_not_dvd_num
```lean
theorem ModularCurve.StarBank.eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.c4_tateLaurent
```lean
theorem ModularCurve.c4_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by sorry  -- PIN PROOF (do not transcribe)
```

**Vocabulary.** `ModularCurve.jqModC`, `qTwist`, `etaProd`, `eisenstein4`, `tateLaurent`, `qExpand`;
mathlib's `bernoulli`, `ModularForm.E`, `PowerSeries.constantCoeff`, `Polynomial.IsRoot`,
`Polynomial.X`. `ArithmeticFunction.sigma` and `ModularForms.EisensteinSeries.QExpansion` for the
`eisInt` pair.

**What to write.** (1) The `eisInt` pair's 99-line shared prelude once
(`eisInt_not_dvd_den_shift` 42, `eisInt_coeff` 37, `eisInt_dvd_den` 13,
`eisInt_bernoulli_ne_zero` 7), then `eisInt_series` and `eisInt_not_dvd_num` as public headlines.
(2) `starK` (the Hasse hypothesis ⇒ a star polynomial) with its local `Dseries`/`hahnMapRingHom`
layer. (3) `count` (the root count). (4) `c4_tateLaurent` in `Defs/TateFormal.lean`: one line at the
wrapper's statement.

**Traps.** (i) `starK` takes the Hasse hypothesis as a **hypothesis** (`hHasse`, with `5 ≤ ℓ`): the
row is the implication, not the existence. Keep `[Fact ℓ.Prime]` and `[CharP K ℓ]`. (ii) `count`'s
`Kbar2` in the `S_` file is a local abbreviation for the algebraic closure (the parser reads it as
`BassSerre.Gp` — it is not): write it locally, `private`. (iii) `count`'s proof is the odd/even
root-count dichotomy for `G.comp R ∣ C c * G^(p+1)`; the pin uses `Polynomial.splits` and
`natDegree` bookkeeping over an algebraically closed field — keep `hp0 : (p : K) ≠ 0` and `hp2`.
(iv) `eisInt_series`'s `T` is a `PowerSeries ℤ` with a prescribed map to ℂ and a divisibility of
every positive coefficient; `hk : 3 ≤ ℓ - 1` is needed for `E`'s weight. (v) `c4_tateLaurent`'s
wrapper sets `synthInstance.maxHeartbeats 400000`; **do not copy the option** — at the port's cap
the statement is `HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4)`
and the instance is `tateLaurent`'s, already elliptic.

**Gates.** As the house rules. Wire: two `spec-pin:` lines per row — eight in `StarBank/Hasse.lean`,
two in `Defs/TateFormal.lean`.


## LV-4 — L-coset and L-eta: the primitive-coset polynomial; the integral q-expansion coefficients

**Silo**: 1,051 (522 + 529). **Net**: ≈760. **Wave B.**
**Files**: **new** `lean/FLTForHuman/ModularCurve/ModularPolynomialCoset.lean` (152, 149, 149, 72)
and insert 244, 237, 48 into `lean/FLTForHuman/ModularCurve/JqCoefficients.lean`.
**Pin**: `Theorems/Thm_ModularCurve_{ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex,
eq_cosetTwoVarPoly_of_forall_isRoot, separable_cosetTwoVarPoly,
hasSum_cosetSubst_coeff_mul_qParam_pow, hasSum_coeff_etaProd_pow, coeff_jNum_le_six,
eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero}.lean` and the matching `P2M/Sol/S_*.lean`.

### ModularCurve.ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex
```lean
theorem ModularCurve.ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (hC : ∃ ζ : ℂˣ, IsPrimitiveRoot ζ N ∧ ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ))
        (ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC ℂ) t))
    (K : Type*) [Field K] (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) :
    ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (ModularCurve.qExpand K N (ModularCurve.jqModC K)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC K) t) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot
```lean
theorem ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0)
    (P : Polynomial (LaurentSeries K)) (hP : P.Monic) (hdeg : P.natDegree = (ModularCurve.primCosetReps N).card)
    (hroot : ∀ t ∈ ModularCurve.primCosetReps N, P.IsRoot (ModularCurve.cosetConj ζ J t)) :
    P = ModularCurve.cosetTwoVarPoly ζ N J := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.separable_cosetTwoVarPoly
```lean
theorem ModularCurve.separable_cosetTwoVarPoly (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0) :
    (ModularCurve.cosetTwoVarPoly ζ N J).Separable := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow
```lean
theorem ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (S : LaurentSeries ℂ) (τ : ℂ) (x : ℂ)
    (h : HasSum (fun m : ℤ => S.coeff m * Function.Periodic.qParam 1 ((a * τ + b) / d) ^ m) x) :
    HasSum (fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * Function.Periodic.qParam N τ ^ m) x := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero
```lean
theorem ModularCurve.eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero (P : Polynomial ℤ) (n : ℕ)
    (hP : P.natDegree ≤ n) (h : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ 0 → (evalAtJ P).coeff m = 0) : P = 0 := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.hasSum_coeff_etaProd_pow
```lean
theorem ModularCurve.hasSum_coeff_etaProd_pow (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.coeff_jNum_le_six
```lean
theorem ModularCurve.coeff_jNum_le_six :
    PowerSeries.coeff 0 jNum = 1 ∧ PowerSeries.coeff 1 jNum = 744 ∧ PowerSeries.coeff 2 jNum = 196884 ∧
      PowerSeries.coeff 3 jNum = 21493760 ∧ PowerSeries.coeff 4 jNum = 864299970 ∧
      PowerSeries.coeff 5 jNum = 20245856256 ∧ PowerSeries.coeff 6 jNum = 333202640600 := by sorry  -- PIN PROOF (do not transcribe)
```

**Vocabulary.** `ModularCurve.primCosetReps`/`cosetConj`/`cosetTwoVarPoly`
(`Defs/PrimCosetReps.lean`, legacy — **import only**), `cosetSubst` (`Defs/PhiGen.lean`, legacy —
import only), `ModularPolynomialData` (`Defs/Polynomial.lean`), `qExpand`/`jqModC`/`coeffMap`
(`Defs/Laurent.lean`, `Defs/JqCoeff.lean`), `etaProd`/`jNum`/`evalAtJ` (`Defs/Jq.lean`),
`Function.Periodic.qParam`, `IsPrimitiveRoot`.

**What to write.** (1) The coset module: 152's descent engine (`conjR`, `phiAt`, `coeffMap_*`,
`coeffMap_injective`), then the two coset-polynomial rows sharing `cosetConj_injOn` (63 lines) and
its three coefficient lemmas (`coeff_cosetSubst_of_lt`, `coeff_cosetSubst_neg_sq`,
`ne_zero_of_mem`), then `hasSum_cosetSubst_coeff_mul_qParam_pow`. (2) In `JqCoefficients.lean`: the
module's pentagonal-series engine is already there (`etaProd_eq_pentagonalSeries`,
`coeff_etaProd_*`, `coeff_jNum_one/two`) — extend it to `jNum`'s coefficients 0–6 (row 237), to
`etaProd ^ a` (row 244), and prove row 48 by the window-`[-n, 0]` comparison. Add the three
`Theorems/` and three `P2M/Sol/` `spec-pin:` lines with the rows; do **not** delete the module's
`PORT_FILES` row (the manager does that at review, with the two `own:` markers already in
`spec/decl_markers.tsv`).

**Traps.** (i) 152 is a **descent from ℂ to an arbitrary field `K`**: `coeffMap` along `Int.castRingHom`
/ `algebraMap`, the `phiAt` evaluation and `coeffMap_injective`. The `S_` file's namespace is
`CosetDescentAux`; use the port's own subject name. (ii) `eq_cosetTwoVarPoly_of_forall_isRoot` and
`separable_cosetTwoVarPoly` are over a general field with `hJ : J.coeff (-1) ≠ 0` and
`hJ' : ∀ m < -1, J.coeff m = 0`; keep both. (iii) `cosetConj_injOn` is the shared 63-line engine;
write it once, public at the `S_` name. (iv) `JqCoefficients.lean` is **legacy and still on
`PORT_FILES`**: it is being migrated by this touch; add only its wire lines and the rows. Its
existing public `coeff_jq_zero`/`coeff_jq_one` are `own:` rows in the marker table — if
`check_port` reports them `MISSING`, that is the pre-wire state, not a defect: report the count.
(v) `evalAtJ` is a `RingHom` (`Defs/Jq.lean`); row 48's hypothesis is on the coefficients in
`[-n, 0]`, and the proof is the `natDegree`/coefficient comparison — not `evalAtJ_injective`
(which is a different, unbounded statement in `PhiGenDescendsStructure.lean`).

**Gates.** As the house rules. Wire: two `spec-pin:` lines per row — eight in the new module, six in
`JqCoefficients.lean`.


## LV-5 — L-x1coeff: the coefficient-map dictionary over the q-expansion function fields

**Silo**: 1,348. **Net**: ≈1,069. **Wave B.**
**File**: **new** `lean/FLTForHuman/ModularCurve/X1/CoeffMap.lean` (all seven rows).
**Pin**: `Theorems/Thm_ModularCurve_{existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap,
finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap,
exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem,
mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC,
isIntegral_adjoin_of_isIntegral_adjoin_coeffMap,
laurentBaseChange_qExpFunctionFieldC_eq,
linearIndependent_coeffMap_comp_of_linearIndependent}.lean` and the matching `P2M/Sol/S_*.lean`.

### ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
```lean
theorem ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ₀ : ModularCurve.qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] ModularCurve.qExpFunctionFieldC K₀ Γ) :
    ∃! σ : ModularCurve.qExpFunctionFieldC K Γ ≃ₐ[K] ModularCurve.qExpFunctionFieldC K Γ,
      ∀ (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ),
        (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀) →
        ((σ x : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) =
          ModularCurve.coeffMap φ ((σ₀ x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) : LaurentSeries K₀) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
```lean
theorem ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))
    (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀))
    (hx : (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀))
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
      (ModularCurve.qExpFunctionFieldC K Γ)] :
    FiniteDimensional (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ) ∧
      Module.finrank (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
          (ModularCurve.qExpFunctionFieldC K₀ Γ) ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
```lean
theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
    ∃ (k : ℤ) (g h : ModularForm Γ k), h ≠ 0 ∧
      x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
```lean
theorem ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
    (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (x : LaurentSeries ℚ) :
    x ∈ ModularCurve.qExpFunctionFieldC ℚ Γ ↔ x ∈ ModularCurve.intFormRatiosC ℚ Γ := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.isIntegral_adjoin_of_isIntegral_adjoin_coeffMap
```lean
theorem ModularCurve.isIntegral_adjoin_of_isIntegral_adjoin_coeffMap {k L : Type*} [Field k]
    [Field L] (σ : k →+* L) (j x : LaurentSeries k)
    (h : IsIntegral (Algebra.adjoin L ({coeffMap σ j} : Set (LaurentSeries L))) (coeffMap σ x)) :
    IsIntegral (Algebra.adjoin k ({j} : Set (LaurentSeries k))) x := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq
```lean
theorem ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq
    (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) = ModularCurve.qExpFunctionFieldC L Γ := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent
```lean
theorem ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by sorry  -- PIN PROOF (do not transcribe)
```

**Vocabulary.** `ModularCurve.qExpFunctionFieldC`, `intFormRatiosC`, `x1FunctionFieldBar`
(`X1/Defs.lean`), `coeffMap`, `laurentBaseChange` (`Defs/Laurent.lean`), `coeffMap_intSeriesC`
(`X1/DiamondCorrespondence.lean`, public — import, do not restate), `qExpand`/`qExpandAlgHomC`
(`Defs/Laurent.lean`, `X0/FunctionFieldFull.lean`), `UpperHalfPlane.qExpansion`,
`IntermediateField.adjoin`, `Module.finrank`, `Transcendental`.

**What to write.** The 95-line shared prelude (`linearIndependent_coeffMap` 59,
`coeffMap_mem` 21) once, then the seven headlines. The order is the theory's own: 92
(base change of the field) and 45 (linear independence transport) are the two small structural
lemmas; 120 (`↔` membership) and 98 (integrality) are the coefficient dictionary; 211 (ratio of
modular forms) and 314/468 (the algEquiv dictionary and its finrank inequality) are the two
substantial ones.

**Traps.** (i) 468 is an existence-and-uniqueness of a `qExpFunctionFieldC K Γ ≃ₐ[K] …` over a base
change `φ : K₀ →+* K`: its proof builds `Rsub`, `iotaR`, `sigmaR`, `eR` and concludes through
`algEquiv_eq_of_iota`. Do not collapse it into a `RingEquiv` transport. (ii) 468's and 314's
wrappers carry `attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one`; keep
these **out** of the module (the port's `qExpandAlgHomC` is an abbrev of `qExpandAlg`). (iii) 211's
`hT : ModularGroup.T ∈ Γ` and the `hx : x ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)` are the
statement's hypotheses; the conclusion is a `∃ k g h, h ≠ 0 ∧ …` with `UpperHalfPlane.qExpansion 1`
coerced from `PowerSeries ℂ` to `LaurentSeries ℂ`. (iv) 314's `hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀)`
is a hypothesis, not a goal. (v) 45 is `LinearIndependent` transport along
`coeffMap (algebraMap κ k)` applied to `f : Fin n → LaurentSeries κ` — the composition spelling in
the statement (`⇑(coeffMap …) ∘ f`) is the checker's text.

**Gates.** As the house rules. Wire: two `spec-pin:` lines per row, fourteen in the new module.


## LV-6 — L-other: the Pic0 identification's compatibility, the diamond commutation, and the
## three period/analytic/cusp rows

**Silo**: 1,485. **Net**: ≈1,027. **Wave B.**
**Files**: **new** `lean/FLTForHuman/ModularCurve/X1/Pic0Correspondence.lean` (536); inserts into
`lean/FLTForHuman/ModularCurve/X1/DiamondCorrespondence.lean` (468),
`lean/FLTForHuman/ModularCurve/ComplexPlaceDictionaryOf.lean` (57),
`lean/FLTForHuman/ModularForms/EichlerShimura/PeriodOf.lean` (98),
`lean/FLTForHuman/ModularCurve/Period/QExpansionDiff.lean` (167),
`lean/FLTForHuman/ModularCurve/Analytic/QParamUnique.lean` (159).
**Pin**: the six wrappers `Theorems/Thm_ModularCurve_{pic0Congr_jOne_jH_bot_compat,
diamondOneBar_comm, realizeOf_eq_div, periodAlongOf_eq_neg_conj_periodAlongOf_J_smul,
eq_qExpansionDiffAlong_of_isQExpansionDiffAlong, tendsto_atImInfty_of_hasSum_qParam}.lean` and the
matching `P2M/Sol/S_*.lean`.

### ModularCurve.pic0Congr_jOne_jH_bot_compat
```lean
theorem ModularCurve.pic0Congr_jOne_jH_bot_compat (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥)
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥) :
    let e : ModularCurve.JOne M ≃+ ModularCurve.JH M ⊥ :=
      AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ModularCurve.JOne M),
        e (ModularCurve.heckeOperatorOneBar M ⟨ℓ, hℓ⟩ x) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ) (e x)) ∧
    (∀ (d : ℕ) (hd : d.Coprime M) (x : ModularCurve.JOne M),
        e (ModularCurve.diamondOneBar M d x) = ModularCurve.diamondHBar M ⊥ (ZMod.unitOfCoprime d hd) (e x)) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JOne M),
        e (σ • x) = σ • e x) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.diamondOneBar_comm
```lean
theorem ModularCurve.diamondOneBar_comm (M d e : ℕ) :
    ModularCurve.diamondOneBar M d * ModularCurve.diamondOneBar M e =
      ModularCurve.diamondOneBar M e * ModularCurve.diamondOneBar M d := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.realizeOf_eq_div
```lean
theorem ModularCurve.realizeOf_eq_div
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm Γ k) (x : LaurentSeries ℂ)
    (hx : x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : UpperHalfPlane) (hτ : (h : UpperHalfPlane → ℂ) τ ≠ 0) :
    ModularCurve.realizeOf Γ x τ = (g : UpperHalfPlane → ℂ) τ / (h : UpperHalfPlane → ℂ) τ := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
```lean
theorem ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
    (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)))
    (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ g =
      -(starRingEnd ℂ) (ModularCurve.periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong
```lean
theorem ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) {φ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ) : φ = qExpansionDiffAlong σ := by sorry  -- PIN PROOF (do not transcribe)
```

### ModularCurve.tendsto_atImInfty_of_hasSum_qParam
```lean
theorem ModularCurve.tendsto_atImInfty_of_hasSum_qParam (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (c : ℕ → ℂ) (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : Filter.Tendsto F UpperHalfPlane.atImInfty (nhds (c 0)) := by sorry  -- PIN PROOF (do not transcribe)
```

**Vocabulary.** `AlgebraicCurve.Pic0.congr` (`AlgebraicCurve/Pic0Congr.lean`),
`IntermediateField.equivOfEq` (mathlib), `HeckeDiamondInputsAll` (`X1/Inputs.lean`),
`HeckeDiamondInputsHAll`/`diamondHBar` (`XH/Operators.lean`), `heckeOperatorOneBar`
(`X1/HeckeModule.lean`), `heckeOperatorHAlong` (`XH/HeckeOperator.lean`), `diamondOneBar`
(`X1/Diamond.lean`), `JOne`/`x1FunctionFieldBar` (`X1/Defs.lean`), `JH`/`xHFunctionFieldBar`
(`XH/FunctionField.lean`), `ModularCurve.realizeOf` (`ComplexPlaceDictionaryOf.lean`),
`ModularCurve.periodAlongOf` (`ModularForms/EichlerShimura/PeriodOf.lean`),
`IsQExpansionDiffAlong`/`qExpansionDiffAlong` (`Period/QExpansionDiff.lean`),
`qParam`/`coeff_unique` (`Analytic/QParamUnique.lean`).

**What to write.**
1. **536** in the new module: the statement is a `let e := Pic0.congr …` under which the Hecke,
   diamond and Galois commutations are asserted. The `S_` file's 56-declaration engine
   (`slashForm` family, `ιC`/`qC`, `IsDiaGen`, `heckeAlpha_heq`/`heckeBeta_heq`,
   `coeffMap_qExpand`, `qExpand_mem_laurentBaseChange`, `T_mem_Gamma1`) is half in
   `X1/DiamondCorrespondence.lean`/`X1/AtkinLehnerExchange.lean` already — check by name before
   transcribing, and keep what is ported public where it is.
2. **468** in `X1/DiamondCorrespondence.lean`: the commutation headline; its engine
   (`conjForm`, `coeffMap_intSeriesC`, `isIntegralQExp_intCast`, `ne_zero_of_isIntegralQExp`,
   `conj_mem_Gamma1`) is already public there. Add the row's two `spec-pin:` lines.
3. **57** in `ComplexPlaceDictionaryOf.lean`: `realizeOf_eq_div`, one short proof from `realizeOf`'s
   definition and the q-expansion ratio hypothesis.
4. **98** in `PeriodOf.lean`: the `J`-conjugation law of `periodAlongOf`.
5. **167** in `Period/QExpansionDiff.lean` (migrated in the prep): the uniqueness of the
   q-expansion differential; the `S_` file's `Etale.Field`/`Kaehler` imports travel with it.
6. **159** in `Analytic/QParamUnique.lean` (migrated in the prep): the public headline over the
   module's existing **private** `tendsto_atImInfty`/`coeff_unique` engine. **Its wire line for the
   wrapper must be added in the same edit as the statement** — a `spec-pin:` for
   `Thm_ModularCurve_tendsto_atImInfty_of_hasSum_qParam.lean` without the declaration would be a
   false ported marker.

**Traps.** (i) 536's `let` in the statement: the checker's text carries the `let e : JOne M ≃+ JH M ⊥
:= …` and the three `∧`-ed conclusions; the `haveI : NeZero ℓ` inside is part of the statement.
(ii) 536's engine is the pin's `ES1Sol` prelude — do not carry the `p2m_` scaffolding, and keep
`Finset.range`/`Finset.univ` spellings. (iii) 468's wrapper has no binders beyond `(M d e : ℕ)`; the
real work is the engine, so write the engine only where it is not already in the port (it largely
is). (iv) 167: `φ = qExpansionDiffAlong σ` from `IsQExpansionDiffAlong σ φ`; the proof is the
uniqueness of a `K`-linear map agreeing with `θ` on exact differentials and satisfying the Leibniz
rule, and the definition is a `Classical.choose` — the row is what makes it canonical.
(v) 159: the module's engine is `private`; do not promote it (no consumer outside), and do not
restate it. (vi) 98: the wrapper's `attribute [-simp] ModularCurve.Period.jConjMat_*` line names
`PeriodHomPair.lean`'s lemmas; keep it out of the module.

**Gates.** As the house rules. Wire: two `spec-pin:` lines per row — twelve across the six files,
one of them (159) added with its statement.


---

## Dispatch and review

Wave A: LV-1, LV-2, LV-3. Wave B (after the wave-A review): LV-4, LV-5, LV-6. The manager writes
the wave's consumer zone (`spec/ModularCurveLeavesConsumer.lean`, extended per wave), reviews each
order's tree against the gates, and deletes `JqCoefficients.lean`'s `PORT_FILES` row at the LV-4
review. The successor read (`SET-LEAVES.md` §0's command) closes the set.
