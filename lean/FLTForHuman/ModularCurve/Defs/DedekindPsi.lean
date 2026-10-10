/-
  The `ModularCurve`-namespaced spelling of the Dedekind `ψ` function.

  The mathematics lives in `FLTForHuman/NumberTheory/DedekindPsi.lean` — ψ is
  generic number theory and has no business in a `jq` file. But the pin states it
  in `Definitions/Def_ModularCurve_X0.lean` inside `namespace ModularCurve`, and
  the port has a handful of *qualified* uses (`ModularCurve.dedekindPsi`,
  `ModularCurve.dedekindPsi_prime`, `ModularCurve.dedekindPsi_pos`) in
  `ModularForms/Gamma0TwoIndex.lean`, `WeierstrassCurve/Velu/CyclicCount.lean`,
  `ModularCurve/Degree/PlaceDegree.lean` and the `spec/` probes. This module keeps
  those names alive at the pin's namespace, so nothing downstream changes.

  Nothing is proved here: every declaration is a one-line delegation, and each
  keeps the pin's kind (`def`/`theorem`) and statement so the statement checker
  still diffs them against the pin.

  FLT provenance, pinned `aa2d8b3`: `Definitions/Def_ModularCurve_X0.lean` lines
  111–212.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean
-/
import FLTForHuman.NumberTheory.DedekindPsi

set_option autoImplicit false

namespace ModularCurve

/-- The Dedekind psi function, at the pin's name and namespace. -/
def dedekindPsi (N : ℕ) : ℕ := _root_.dedekindPsi N

@[simp]
theorem dedekindPsi_one : dedekindPsi 1 = 1 :=
  _root_.dedekindPsi_one

theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 :=
  _root_.dedekindPsi_prime hp

theorem dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) :=
  _root_.dedekindPsi_prime_pow p k hp hk

theorem dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) :
    dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N :=
  _root_.dedekindPsi_mul_of_coprime M N h

theorem dedekindPsi_mul_prime (M ℓ : ℕ) [NeZero M] (hℓ : ℓ.Prime) :
    dedekindPsi (M * ℓ) = (if ℓ ∣ M then ℓ else ℓ + 1) * dedekindPsi M :=
  _root_.dedekindPsi_mul_prime M ℓ hℓ

theorem dedekindPsi_pos (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N :=
  _root_.dedekindPsi_pos N hN

end ModularCurve
