window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Nat.Factorization.Induction"] = {
  "module": "Mathlib.Data.Nat.Factorization.Induction",
  "cards": {
    "Nat.recOnPosPrimePosCoprime": {
      "seed": true,
      "refs": [{"where":"type","name":"Nat.Prime","module":"Mathlib.Data.Nat.Prime.Defs","kind":"def"},{"where":"type","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"type","name":"Nat.Coprime","module":"Init.Data.Nat.Coprime","kind":"def"},{"where":"body","name":"Nat.recOnPrimePow","module":"Mathlib.Data.Nat.Factorization.Induction","kind":"def"},{"where":"body","name":"Dvd.dvd","module":"Init.Prelude","kind":"abbrev"}],
      "range": {"start":{"line":46,"column":0},"end":{"line":63,"column":47}},
      "name": "Nat.recOnPosPrimePosCoprime",
      "module": "Mathlib.Data.Nat.Factorization.Induction",
      "kind": "def",
      "elaborated_type": "{motive : ℕ → Sort u_1} →\n  ((p n : ℕ) → Nat.Prime p → 0 < n → motive (p ^ n)) →\n    motive 0 →\n      motive 1 → ((a b : ℕ) → 1 < a → 1 < b → a.Coprime b → motive a → motive b → motive (a * b)) → (a : ℕ) → motive a",
      "doc": "Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and\n`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. ",
      "short": "recOnPosPrimePosCoprime",
      "signature_source": "@[elab_as_elim]\ndef recOnPosPrimePosCoprime {motive : ℕ → Sort*}\n    (prime_pow : ∀ p n : ℕ, Prime p → 0 < n → motive (p ^ n))\n    (zero : motive 0) (one : motive 1)\n    (coprime : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :\n    ∀ a, motive a :=",
      "body_source": "recOnPrimePow zero one <| by\n    intro a p n hp' hpa hn hPa\n    by_cases ha1 : a = 1\n    · rw [ha1, mul_one]\n      exact prime_pow p n hp' hn\n    refine coprime (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) ?_ ?_\n      (prime_pow _ _ hp' hn) hPa\n    · contrapose! hpa\n      simp [lt_one_iff.1 (lt_of_le_of_ne hpa ha1)]\n    · simpa [hn, Prime.coprime_iff_not_dvd hp']",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Nat/Factorization/Induction.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "CardNTorsion"
      ]
    },
    "Nat.recOnPrimePow": {
      "seed": false,
      "refs": [],
      "range": {"start":{"line":24,"column":0},"end":{"line":44,"column":33}},
      "name": "Nat.recOnPrimePow",
      "module": "Mathlib.Data.Nat.Factorization.Induction",
      "kind": "def",
      "elaborated_type": "{motive : ℕ → Sort u_1} →\n  motive 0 →\n    motive 1 → ((a p n : ℕ) → Nat.Prime p → ¬p ∣ a → 0 < n → motive a → motive (p ^ n * a)) → (a : ℕ) → motive a",
      "doc": "Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,\nwe can define `P` for all natural numbers. ",
      "short": "recOnPrimePow",
      "signature_source": "@[elab_as_elim]\ndef recOnPrimePow {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)\n    (prime_pow_mul : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → motive a → motive (p ^ n * a)) :\n    ∀ a, motive a :=",
      "body_source": "Nat.strongRec fun n ↦\n    match n with\n    | 0 => fun _ => zero\n    | 1 => fun _ => one\n    | k + 2 => fun hk => by\n      letI p := (k + 2).minFac\n      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)\n      letI t := (k + 2).factorization p\n      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _\n      haveI htp : 0 < t := hp.factorization_pos_of_dvd (k + 1).succ_ne_zero (k + 2).minFac_dvd\n      convert! prime_pow_mul ((k + 2) / p ^ t) p t hp _ htp (hk _ (Nat.div_lt_of_lt_mul _)) using 1\n      · rw [Nat.mul_div_cancel' hpt]\n      · rw [Nat.dvd_div_iff_mul_dvd hpt, ← Nat.pow_succ]\n        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp\n      · simp [htp.ne', hp.one_lt]",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Nat/Factorization/Induction.lean",
      "has_source": true,
      "has_refs": false,
      "worksheets": [
        "CardNTorsion"
      ]
    }
  }
};
