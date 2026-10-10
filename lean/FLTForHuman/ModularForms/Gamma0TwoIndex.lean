/-
  The index `[SL(2, ℤ) : Γ₀(2)] = 3`, as the `N = 2` case of the port's general
  theorem `ModularCurve.Gamma0_index`, `[SL(2, ℤ) : Γ₀(N)] = ψ(N)` (Dedekind psi);
  `ψ(2) = 3` because `ψ(p) = p + 1` for `p` prime.

  The pin proves this case twice: once for general `N` in
  `P2M/Sol/S_ModularCurve_Gamma0_index.lean` (via the first-column/`ℙ¹(ℤ/N)`
  bijection), and again, privately, in
  `P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` lines 94–174 for the
  Sturm-bound route. This module previously transcribed the second block
  verbatim; it now consumes the general theorem instead, so the module path and
  the public name `ModularForm.Gamma0_two_index_eq_three` are unchanged while the
  ~130-line private duplicate is gone. The general theorem was ported as SET-3 of
  the level effort (`lean/logs/level-port.md` §3); the post-SET-3 dedup pass (§4)
  did not list this module, and the decision is recorded in §6 of that file.

  FLT provenance, pinned `aa2d8b3`:
  * `P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` lines 94–174 — the statement
    (the pin's private coset block and its `Gamma0_two_index_eq_three`).
  * `P2M/Sol/S_ModularCurve_Gamma0_index.lean` — the general theorem delegated to,
    ported at `FLTForHuman/ModularCurve/Gamma0Index.lean` (`ModularCurve.Gamma0_index`),
    with `dedekindPsi` and `dedekindPsi_prime` in
    `FLTForHuman/ModularCurve/Defs/Jq.lean`.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L94-L174
-/
import FLTForHuman.ModularCurve.Gamma0Index
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section

namespace ModularForm

/-- **The index is three.** `SL(2, ℤ) ⧸ Γ₀(2)` has three cosets: the `N = 2` case
of `ModularCurve.Gamma0_index`, `[SL(2, ℤ) : Γ₀(N)] = ψ(N)`, with `ψ(2) = 3`. -/
theorem Gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  rw [ModularCurve.Gamma0_index 2,
    ModularCurve.dedekindPsi_prime (by norm_num : Nat.Prime 2)]

end ModularForm

end
