window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.Data.Int.Init"] = {
  "module": "Mathlib.Data.Int.Init",
  "cards": {
    "Int.inductionOn'": {
      "refs": [{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Int.inductionOn'.neg","module":"Mathlib.Data.Int.Init","kind":"def"},{"where":"body","name":"Int.inductionOn'.pos","module":"Mathlib.Data.Int.Init","kind":"def"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"},{"where":"body","name":"cast","module":"Init.Prelude","kind":"def"}],
      "range": {"start":{"line":93,"column":0},"end":{"line":108,"column":53}},
      "name": "Int.inductionOn'",
      "module": "Mathlib.Data.Int.Init",
      "kind": "def",
      "elaborated_type": "{motive : ℤ → Sort u_1} →\n  (z b : ℤ) →\n    motive b → ((k : ℤ) → b ≤ k → motive k → motive (k + 1)) → ((k : ℤ) → k ≤ b → motive k → motive (k - 1)) → motive z",
      "doc": "Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater\nthan `b`, and the `pred` of a number less than `b`. ",
      "short": "inductionOn'",
      "signature_source": "@[elab_as_elim] protected def inductionOn' : motive z :=",
      "body_source": "cast (congrArg motive <| show b + (z - b) = z by lia) <|\n  match z - b with\n  | .ofNat n => pos n\n  | .negSucc n => neg n\nwhere\n  /-- The positive case of `Int.inductionOn'`. -/\n  pos : ∀ n : ℕ, motive (b + n)\n  | 0 => cast (by simp) zero\n  | n + 1 => cast (by lia) <| succ _ (Int.le_add_of_nonneg_right (natCast_nonneg _)) (pos n)\n  /-- The negative case of `Int.inductionOn'`. -/\n  neg : ∀ n : ℕ, motive (b + -[n+1])\n  | 0 => pred _ Int.le_rfl zero\n  | n + 1 => cast (by lia) <| pred _ (by lia) (neg n)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Int/Init.lean",
      "has_source": true,
      "has_refs": true
    },
    "Int.strongRec": {
      "refs": [{"where":"type","name":"GE.ge","module":"Init.Prelude","kind":"def"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"Int.inductionOn'","module":"Mathlib.Data.Int.Init","kind":"def"},{"where":"body","name":"Int.decLt","module":"Init.Data.Int.Basic","kind":"def"}],
      "range": {"start":{"line":186,"column":0},"end":{"line":192,"column":40}},
      "name": "Int.strongRec",
      "module": "Mathlib.Data.Int.Init",
      "kind": "def",
      "elaborated_type": "{m : ℤ} →\n  {motive : ℤ → Sort u_1} →\n    ((n : ℤ) → n < m → motive n) → ((n : ℤ) → n ≥ m → ((k : ℤ) → k < n → motive k) → motive n) → (n : ℤ) → motive n",
      "doc": "A strong recursor for `Int` that specifies explicit values for integers below a threshold,\nand is analogous to `Nat.strongRec` for integers on or above the threshold. ",
      "short": "strongRec",
      "signature_source": "@[elab_as_elim] protected def strongRec (n : ℤ) : motive n :=",
      "body_source": "by\n  refine if hnm : n < m then lt n hnm else ge n (by lia) (n.inductionOn' m lt ?_ ?_)\n  · intro _n _ ih l _\n    exact if hlm : l < m then lt l hlm else ge l (by lia) fun k _ ↦ ih k (by lia)\n  · exact fun n _ hn l _ ↦ hn l (by lia)",
      "source_file": "lean/.lake/packages/mathlib/Mathlib/Data/Int/Init.lean",
      "has_source": true,
      "has_refs": true
    }
  }
};
