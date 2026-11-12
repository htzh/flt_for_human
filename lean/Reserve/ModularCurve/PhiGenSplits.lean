/-
  T13 — the consequence, part 2: the splitting of the modular polynomial.

  `PhiGen.splits_of_prime` is the cone's content: the level-`p` datum, read at the
  level-`p` nome, is the conjugate product `∏_i (Y - conj_i)`. The proof joins the
  whole cone — T11's descent (a), T9's integrality (b), T8's membership (c), T11's
  assembly (d), this topic's `eq_of_prime` for uniqueness, and (d)'s coefficient
  comparison for the read-off — first over `CyclotomicField p ℚ`, then transported
  to an arbitrary `ℚ`-algebra `K` along an embedding sending the chosen primitive
  root to `ζ`.

  `PhiGen.splits_prime_at_slot` is the cone's exported statement, math/010 §3's
  formula with the general level datum `(e, u)`:
  `Φ_p(j(u^p q^{pe}), Y) = (Y - j(u^{p^2} q^{p^2e})) ∏_b (Y - j(u ζ^b q^e))`,
  obtained from `splits_of_prime` at the primitive `p`-th root `ζ ^ (N / p)` and
  pushed through `qExpand K e ∘ qTwist u`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_splits_of_prime.lean` (353 lines) and
  `P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean` (288 lines). Both
  public statements are the `Theorems/` wrappers verbatim.

  ## Dedup

  The `TS` prelude both pin files repeat is `Defs/TS.lean` (`TS` and its ten
  coefficient lemmas) plus `Defs/Laurent.lean`'s `coeffEmb_qExpand`; the port
  writes only the three live bridges (`iota_jq`, `conj_zero_eq`, `conj_succ_eq`).
  The pin's ~200 lines of prelude that neither exported theorem uses
  (`phiAtSeed*`, `qTwistEquiv*`, `qTwist_TS_one_cycle`, `phiProd_conj_eq`,
  `roots_phiProd_conj*`, `iota_jqN`, `qTwist_iota_of_pow_eq_one`, and the at-slot
  roots API `prod_form_ne_zero`/`roots_prime_at_slot*`/`isRoot_prime_at_slot_iff`)
  exist for the char-`p` `*_of_isPrimitiveRoot` variants, which are outside the
  44-node cone and are not ported here.

  ## The any-field twin

  These two theorems are stated over a `ℚ`-algebra `K` because the cone's argument runs
  through `eq_of_prime`/`evalAtI` over `ℚ`. The same two statements over an *arbitrary*
  field — the pin's char-`p` text, `jqModC K` in place of `coeffEmb K jq` — are the separate
  module `PhiGenSplitsAnyField.lean`, which obtains them by transporting `splits_of_prime`
  through the integral cyclotomic order `ℤ[ζ_p]`. They are not instances of
  these: the char-`p` proof *calls* `splits_of_prime`.

  ## Assumptions

  `Defs/TS`, `Defs/Laurent` (`coeffEmb_qExpand`), `Defs/Twist`, `Defs/Jq`,
  `Defs/PhiGen` (`conj`, `phiProd`), `Defs/Polynomial`; T8's
  `mem_adjoin_jq_of_phiGenDescends`; T9's `PhiGenDescends.intCoeffs`; T11's
  `exists_phiGenDescends`, `exists_modularPolynomialData_coeff_eq`; this topic's
  `ModularPolynomialData.eq_of_prime`.
  Checked by `spec/check_port.py` through the `spec-pin:` lines below; the module is
  not listed in `spec/old_check_stmts.py`.

  spec-pin: Theorems/Thm_ModularCurve_PhiGen_splits_of_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Split`.
