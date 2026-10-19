window.PLAY_WORKSHEETS = window.PLAY_WORKSHEETS || {};
window.PLAY_WORKSHEETS["CardNTorsion"] = {
  "slug": "CardNTorsion",
  "file": "lean/play/CardNTorsion.lean",
  "title": "the card `n`-torsion theorem",
  "tagline": "`#E[n](K) = n²`",
  "subject": "the card `n`-torsion theorem: the `n`-torsion of an elliptic curve over an algebraically closed field has `n²` elements",
  "reads": "FLTForHuman/Elliptic/TorsionCard.lean, the port of the pinned FLT P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean, re-exported at Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean:8-9 <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean#L8-L9>",
  "pin": "",
  "check": "cd lean && lake env lean play/CardNTorsion.lean   (~3 s, oleans warm)",
  "status": "open",
  "date": "2026-10-14",
  "imports": ["FLTForHuman.Elliptic.TorsionCard"],
  "opens": ["WeierstrassCurve.Affine","WeierstrassCurve","WeierstrassCurve.Affine.Point"],
  "namespace": "Play",
  "zones": [{"id":"A","title":"the statement, unpacked"},{"id":"B","title":"the counting mechanism"},{"id":"C","title":"the assembly: prime powers and CRT"},{"id":"D","title":"the engine: division polynomials and the bridge"},{"id":"E","title":"things to poke at"},{"id":"Q","title":"question log"}],
  "blocks": [
    {
      "type": "code",
      "line": 28,
      "text": "import FLTForHuman.Elliptic.TorsionCard",
      "zone": null
    },
    {
      "type": "code",
      "line": 30,
      "text": "set_option autoImplicit false",
      "zone": null
    },
    {
      "type": "code",
      "line": 32,
      "text": "noncomputable section",
      "zone": null
    },
    {
      "type": "code",
      "line": 34,
      "text": "open scoped WeierstrassCurve.Affine",
      "zone": null
    },
    {
      "type": "code",
      "line": 35,
      "text": "open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point",
      "zone": null
    },
    {
      "type": "code",
      "line": 37,
      "text": "namespace Play",
      "zone": null
    },
    {
      "type": "prose",
      "md": "The port's main theorem as the compiler sees it. Everything below is a\nreading of this one line.",
      "zone": "A",
      "line": 41
    },
    {
      "type": "check",
      "line": 43,
      "raw": "#check @FLTForHuman.Elliptic.card_torsion_of_isAlgClosed",
      "zone": "A",
      "name": "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed",
      "display": "@FLTForHuman.Elliptic.card_torsion_of_isAlgClosed",
      "card": "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed"
    },
    {
      "type": "example",
      "line": 50,
      "text": "example {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]\n    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=\n  FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W hn",
      "zone": "A",
      "doc": "The statement, re-spelled and closed by the port's theorem.\n\n`W⁄K` is `Affine.baseChange W K`, so `(W⁄K).Point` is the group of `K`-points of\nthe base change of `W` — the pin writes it `W.toAffine⟮K⟯`, and the port's own\nsource spells it `(W.baseChange K).toAffine.Point`."
    },
    {
      "type": "example",
      "line": 58,
      "text": "example {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F) :\n    (W⁄K).Point = (W.baseChange K).toAffine.Point := rfl",
      "zone": "A",
      "doc": "The two spellings of the point group are the same type. The port's internal\nproofs use the long one; `rw` matches on the syntax, so a rewrite that targets\nthis type must be written the way the statement under use spells it."
    },
    {
      "type": "prose",
      "md": " `[W.IsElliptic]` is nonsingularity of the curve: the discriminant is a unit.\nThis instance is the only place the geometry enters the count. ",
      "zone": "A",
      "line": 61
    },
    {
      "type": "check",
      "line": 63,
      "raw": "#check @isElliptic_iff",
      "zone": "A",
      "name": "isElliptic_iff",
      "display": "@isElliptic_iff",
      "card": "WeierstrassCurve.isElliptic_iff"
    },
    {
      "type": "prose",
      "md": " `Submodule.torsionBy ℤ M n` is the pin's local `nTorsion n`, and membership is\nby definition `n • P = 0`. The port deletes the wrapper and uses mathlib's\nsubmodule directly, which is why the pin's `solution` bridge disappears. ",
      "zone": "A",
      "line": 65
    },
    {
      "type": "check",
      "line": 68,
      "raw": "#check @Submodule.mem_torsionBy_iff",
      "zone": "A",
      "name": "Submodule.mem_torsionBy_iff",
      "display": "@Submodule.mem_torsionBy_iff",
      "card": "Submodule.mem_torsionBy_iff"
    },
    {
      "type": "example",
      "line": 70,
      "text": "example {M : Type*} [AddCommGroup M] (n : ℕ) :\n    {P : M | n • P = 0} = (Submodule.torsionBy ℤ M n : Set M) := by\n  ext P\n  simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 78,
      "text": "example {M : Type*} [AddCommGroup M] : Submodule.torsionBy ℤ M 0 = ⊤ := by\n  ext P; simp",
      "zone": "A",
      "doc": "The degenerate case of the induction, live: the `0`-torsion is *everything*\n(`0 • P = 0` for every `P`), so the `n = 0` branch of `card_nTorsion` is not a\ncount at all — it is discharged because the hypothesis `(0 : K) ≠ 0` is false."
    },
    {
      "type": "example",
      "line": 82,
      "text": "example {M : Type*} [AddCommGroup M] : Submodule.torsionBy ℤ M 1 = ⊥ := by\n  ext P; simp",
      "zone": "A",
      "doc": "The `1`-torsion is trivial, again with no algebraic-closedness needed."
    },
    {
      "type": "prose",
      "md": " ### Q1 — are `⊤`/`⊥` special, or just true and false?\n\nThey are *not* built into the elaborator: `⊤` and `⊥` are notation for `Top.top`\nand `Bot.bot`, and ordinary typeclass resolution picks the instance from the\nexpected type — which is what \"the UI specializes them to module\" is. Same\nnotation, different term, decided by the type: ",
      "zone": "A",
      "line": 85
    },
    {
      "type": "example",
      "line": 91,
      "text": "example {M : Type*} [AddCommGroup M] : (⊤ : Submodule ℤ M) = Top.top := rfl",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 92,
      "text": "example {M : Type*} [AddCommGroup M] : (⊥ : Submodule ℤ M) = Bot.bot := rfl",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 98,
      "text": "example {M : Type*} [AddCommGroup M] : ((⊤ : Submodule ℤ M) : Set M) = Set.univ := rfl",
      "zone": "A",
      "doc": "The instances are not special either: `⊤`'s carrier is *defined* to be\n`Set.univ` and `⊥`'s to be `{0}` (mathlib's `top_coe`/`bot_coe` are literally\n`rfl`). Note `{0}`, not `∅`: a submodule must contain `0`, so the bottom of the\nsubmodule lattice is the singleton — where for `Set M` it is the empty set."
    },
    {
      "type": "example",
      "line": 99,
      "text": "example {M : Type*} [AddCommGroup M] : ((⊥ : Submodule ℤ M) : Set M) = {0} := rfl",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 100,
      "text": "example {M : Type*} [AddCommGroup M] : (⊥ : Set M) = ∅ := rfl",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 105,
      "text": "example {M : Type*} [AddCommGroup M] (x : M) :\n    (x ∈ (⊤ : Submodule ℤ M)) ↔ True := Iff.rfl",
      "zone": "A",
      "doc": "Membership is definitional too, which is why `simp` gets these cheaply:\n`x ∈ ⊤` *is* `True` (that is why mathlib states `Submodule.mem_top` as a bare\nproposition, not an `↔`), and `x ∈ ⊥` *is* `x = 0` (`Submodule.mem_bot`)."
    },
    {
      "type": "example",
      "line": 107,
      "text": "example {M : Type*} [AddCommGroup M] (x : M) :\n    (x ∈ (⊥ : Submodule ℤ M)) ↔ x = 0 := Iff.rfl",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " But the two equations above at the *submodule* level are **not** `rfl` — and\nneither is their carrier equality. `torsionBy ℤ M 0` is\n`(DistribSMul.toLinearMap ℤ M 0).ker`: the kernel of the zero map, carrier\n`{x | (0 : ℤ) • x = 0}`. That set is `univ` only by the `zero_smul` law of the\n`Module` structure, and laws of a structure are fields and theorems, not\nreductions — indeed `(0 : ℤ) • x = 0` is not `rfl` for an abstract `M`. So the\nproof has to go through set extensionality and the `smul` laws: `ext x; simp`\n(which is what the port's `card_nTorsion_one` does by hand, `rw [one_nsmul]`\nbefore `AddSubgroup.card_bot`). Replace either proof term with `rfl` and it\nfails; that is the whole content of this block. ",
      "zone": "A",
      "line": 110
    },
    {
      "type": "prose",
      "md": " The one lattice where top and bottom really are \"true and false\" by `rfl` is\n`Prop` itself. ",
      "zone": "A",
      "line": 121
    },
    {
      "type": "example",
      "line": 123,
      "text": "example : (⊤ : Prop) = True := rfl",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 124,
      "text": "example : (⊥ : Prop) = False := rfl",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " The hypothesis `(n : K) ≠ 0` is `char K ∤ n` and is *not* removable: the port\nneeds it separately for `n = 2`, and in characteristic `2` the `K`-points of\n`E[2]` number `1` or `2`, not `4`. ",
      "zone": "A",
      "line": 126
    },
    {
      "type": "check",
      "line": 129,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_two",
      "zone": "A",
      "name": "FLTForHuman.Elliptic.card_nTorsion_two",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_two",
      "card": "FLTForHuman.Elliptic.card_nTorsion_two"
    },
    {
      "type": "prose",
      "md": "`#E[n] = n²` looks like it should be proved by writing `E(K)` as a disjoint union\nof fibres of `[n] : E(K) → E(K)` and computing `#E(K) = deg[n] · #E[n]`. That\nwould be circular: nothing here knows `#E(K)` is finite. The port breaks the\ncircle with facts about the map itself. ",
      "zone": "B",
      "line": 131
    },
    {
      "type": "prose",
      "md": " **`[n]` is onto** when `(n : K) ≠ 0` — separability, arithmetically: `Φ n` and\n`ΨSq n` are coprime, so a root `x₀` of `Φ n − x_Q · ΨSq n` has `ΨSq n x₀ ≠ 0`, and\nthe multiplication formula `smul_x_eq` turns `x₀` into a preimage of `Q`.\n\n(The pin's source lemma was stated for odd `n` only; the port generalised it,\nthe oddness was never used — see `logs/card-torsion-port.md` §2.) ",
      "zone": "B",
      "line": 138
    },
    {
      "type": "check",
      "line": 144,
      "raw": "#check @FLTForHuman.Elliptic.smul_surjective",
      "zone": "B",
      "name": "FLTForHuman.Elliptic.smul_surjective",
      "display": "@FLTForHuman.Elliptic.smul_surjective",
      "card": "FLTForHuman.Elliptic.smul_surjective"
    },
    {
      "type": "prose",
      "md": " **Every fibre has the cardinality of the torsion.** Pick one preimage `P₀` of\n`Q`; translating by `P₀` is a bijection from `E[n]` to the fibre over `Q`. So the\nfibre device needs a *point*, not a finite `E(K)`.\n\nThis is the covering-map picture: `[n]` is onto and every fibre is an\n`E[n]`-torsor, so all fibres have the same cardinality — in the lattice model\n`ℂ/Λ →^{×n} ℂ/Λ` the cover is infinite and each fibre is `(ℤ/n)²`, of size `n²`.\nAn infinite cover with a finite fibre is the ordinary case, and this is one; the\ninfinitude of `E(K)` is no obstruction. What the picture does not hand over is\nthe *value* of the common cardinality: that is the degree of `[n]`, the\nisogeny-degree fact `deg[n] = n²`, which the port does not import. Nor, as a\nformal matter, does `card_smul_fiber` give finiteness — it is an equation of\n`Nat.card`s, and `Nat.card` of an infinite type is `0`; the count below is what\nfirst makes `E[n]` finite here. So the next lemma supplies both the finiteness\nand the value, by polynomial degree. ",
      "zone": "B",
      "line": 146
    },
    {
      "type": "check",
      "line": 161,
      "raw": "#check @FLTForHuman.Elliptic.card_smul_fiber",
      "zone": "B",
      "name": "FLTForHuman.Elliptic.card_smul_fiber",
      "display": "@FLTForHuman.Elliptic.card_smul_fiber",
      "card": "FLTForHuman.Elliptic.card_smul_fiber"
    },
    {
      "type": "prose",
      "md": " **The circle-breaker.** Some `Q` has `2 * n²` preimages counted over both\nsigns. That number is *two fibres*, not one: `{P | n • P = Q ∨ n • P = -Q}` is\nthe union of the fibre over `Q` and the fibre over `-Q`, so it holds `2 * #E[n]`\npoints. The right-hand `2 * n²` comes from the polynomial side, and the `n²` in\nit is already the answer in disguise: `p := Φ n - C c · ΨSq n` has degree `n²`\n(below), its `n²` roots are the admissible `x`-coordinates of preimages of `±Q`,\nand each root carries exactly `2` points, the two `y`-values `y` and `negY x y`.\nSo `2 * #E[n] = 2 * n²` and the `2` cancels — it is the `P ↔ -P` pairing, not a\nfeature of `n = 2`.\n\n(The `Odd n` hypothesis on this lemma is inherited and **unused**: the only\noccurrence of `hodd` in its proof is the binder. The count is a polynomial\ndegree count and is true for every `n` with `n` invertible in `K`. Oddness is\nconsumed one step later, to exclude `Q = -Q`.) ",
      "zone": "B",
      "line": 163
    },
    {
      "type": "check",
      "line": 177,
      "raw": "#check @FLTForHuman.Elliptic.exists_double_fiber_card",
      "zone": "B",
      "name": "FLTForHuman.Elliptic.exists_double_fiber_card",
      "display": "@FLTForHuman.Elliptic.exists_double_fiber_card",
      "card": "FLTForHuman.Elliptic.exists_double_fiber_card"
    },
    {
      "type": "prose",
      "md": " The two degrees that supply the `n²`, so the `2` is visibly just the doubling\nby the `y`-sign. ",
      "zone": "B",
      "line": 179
    },
    {
      "type": "check",
      "line": 181,
      "raw": "#check @WeierstrassCurve.natDegree_Φ    -- deg (Φ n) = n²",
      "zone": "B",
      "name": "WeierstrassCurve.natDegree_Φ",
      "display": "@WeierstrassCurve.natDegree_Φ",
      "card": "WeierstrassCurve.natDegree_Φ"
    },
    {
      "type": "check",
      "line": 182,
      "raw": "#check @WeierstrassCurve.natDegree_ΨSq  -- deg (ΨSq n) = n² - 1, so p has degree n²",
      "zone": "B",
      "name": "WeierstrassCurve.natDegree_ΨSq",
      "display": "@WeierstrassCurve.natDegree_ΨSq",
      "card": "WeierstrassCurve.natDegree_ΨSq"
    },
    {
      "type": "example",
      "line": 187,
      "text": "example {c n : ℕ} (h : 2 * c = 2 * n ^ 2) : c = n ^ 2 :=\n  Nat.eq_of_mul_eq_mul_left (by norm_num) h",
      "zone": "B",
      "doc": "The end of the odd case, as pure arithmetic: two disjoint fibres of a\nsurjection, each of cardinality `c = #E[n]`, together hold `2 * n²` points, so\n`c = n²`."
    },
    {
      "type": "prose",
      "md": " The other case, `Q = -Q`, is *not* killed by arithmetic but by parity: the two\nfibres coincide, so `#E[n] = 2 * n²` is even, Cauchy's theorem\n(`exists_prime_addOrderOf_dvd_card'`) produces an element of `E[n]` of additive\norder `2`, and yet `addOrderOf_dvd_of_nsmul_eq_zero` says that order divides the\nodd `n`. ",
      "zone": "B",
      "line": 190
    },
    {
      "type": "check",
      "line": 195,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_odd_fibers",
      "zone": "B",
      "name": "FLTForHuman.Elliptic.card_nTorsion_odd_fibers",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_odd_fibers",
      "card": "FLTForHuman.Elliptic.card_nTorsion_odd_fibers"
    },
    {
      "type": "prose",
      "md": "The whole argument is one induction on `n`, with the four branches that\n`Nat.recOnPosPrimePosCoprime` demands: prime powers, `0`, `1`, and coprime\nproducts. The port supplies the first and last and lets `simp` kill the middle\ntwo. ",
      "zone": "C",
      "line": 197
    },
    {
      "type": "check",
      "line": 204,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion      -- the assembled induction",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.card_nTorsion",
      "display": "@FLTForHuman.Elliptic.card_nTorsion",
      "card": "FLTForHuman.Elliptic.card_nTorsion"
    },
    {
      "type": "check",
      "line": 205,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_prime_pow  -- p ^ k",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.card_nTorsion_prime_pow",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_prime_pow",
      "card": "FLTForHuman.Elliptic.card_nTorsion_prime_pow"
    },
    {
      "type": "check",
      "line": 206,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_prime  -- p, splitting out p = 2",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.card_nTorsion_prime",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_prime",
      "card": "FLTForHuman.Elliptic.card_nTorsion_prime"
    },
    {
      "type": "check",
      "line": 207,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_odd_fibers  -- odd n",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.card_nTorsion_odd_fibers",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_odd_fibers",
      "card": "FLTForHuman.Elliptic.card_nTorsion_odd_fibers"
    },
    {
      "type": "check",
      "line": 208,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_two  -- n = 2, needs (2 : K) ≠ 0",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.card_nTorsion_two",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_two",
      "card": "FLTForHuman.Elliptic.card_nTorsion_two"
    },
    {
      "type": "check",
      "line": 209,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_one  -- n = 1",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.card_nTorsion_one",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_one",
      "card": "FLTForHuman.Elliptic.card_nTorsion_one"
    },
    {
      "type": "check",
      "line": 210,
      "raw": "#check @FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime  -- CRT",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime",
      "display": "@FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime",
      "card": "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime"
    },
    {
      "type": "check",
      "line": 211,
      "raw": "#check @Nat.recOnPosPrimePosCoprime  -- the principle the four branches feed",
      "zone": "C",
      "name": "Nat.recOnPosPrimePosCoprime",
      "display": "@Nat.recOnPosPrimePosCoprime",
      "card": "Nat.recOnPosPrimePosCoprime"
    },
    {
      "type": "example",
      "line": 217,
      "text": "example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]\n    (W : WeierstrassCurve F) :\n    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point ((3 : ℤ) * 4)) =\n      Nat.card (Submodule.torsionBy ℤ (W⁄K).Point 3) *\n        Nat.card (Submodule.torsionBy ℤ (W⁄K).Point 4) :=\n  FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime W (m := 3) (n := 4) (by norm_num)",
      "zone": "C",
      "doc": "The CRT step on its own. Note what it does *not* assume: no `IsAlgClosed K`,\nno `W.IsElliptic`. The Bézout identity `m * gcdA m n + n * gcdB m n = 1` splits\nany `P` killed by `m * n` into its `m`- and `n`-parts, so the torsion decomposes\nas a product — pure group theory."
    },
    {
      "type": "example",
      "line": 232,
      "text": "example {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]\n    (W : WeierstrassCurve F) [W.IsElliptic] (hn : (12 : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point 12) = 144 := by\n  have h3 : (3 : K) ≠ 0 := by\n    have h := hn\n    rw [show (12 : K) = (3 : K) * 4 by norm_num] at h\n    exact (mul_ne_zero_iff.mp h).1\n  have h4 : (4 : K) ≠ 0 := by\n    have h := hn\n    rw [show (12 : K) = (3 : K) * 4 by norm_num] at h\n    exact (mul_ne_zero_iff.mp h).2\n  have hcr : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point ((3 : ℤ) * 4)) =\n      Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (3 : ℤ)) *\n        Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (4 : ℤ)) :=\n    FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime W (m := 3) (n := 4) (by norm_num)\n  have h3' : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (3 : ℤ)) = 3 ^ 2 :=\n    FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W (n := 3) h3\n  have h4' : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (4 : ℤ)) = 4 ^ 2 :=\n    FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W (n := 4) h4\n  rw [show (12 : ℤ) = (3 : ℤ) * 4 by norm_num, hcr, h3', h4']\n  norm_num",
      "zone": "C",
      "doc": "`#E[12] = 144`, assembled by hand the way `card_nTorsion`'s coprime branch\ndoes it: split `12 = 3 · 4`, count each prime-power factor, multiply.\n\nThe char-sensitive part is real: `(3 : K) ≠ 0` and `(4 : K) ≠ 0` have to come\nfrom somewhere, and here they come from `(12 : K) ≠ 0`, exactly as in the port's\n`haK`/`hbK`. The intermediate `have`s are also where the two spellings of the\npoint group bite: the goal uses `(W⁄K).Point`, but the named steps use\n`(W⁄K).toAffine.Point`, which is what `rw` can match."
    },
    {
      "type": "example",
      "line": 256,
      "text": "example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]\n    (W : WeierstrassCurve F) :\n    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point 1) = 1 :=\n  FLTForHuman.Elliptic.card_nTorsion_one W",
      "zone": "C",
      "doc": "`n = 1` with no hypotheses at all beyond the algebra structure — the `1`\nbranch of the induction."
    },
    {
      "type": "example",
      "line": 263,
      "text": "example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]\n    (W : WeierstrassCurve F) [W.IsElliptic] (h2 : (2 : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point (2 ^ 2)) = 16 := by\n  simpa using FLTForHuman.Elliptic.card_nTorsion_prime_pow W (p := 2) Nat.prime_two h2 2",
      "zone": "C",
      "doc": "A prime power: `#E[4] = 2 ^ (2 * 2) = 16`. This is the one place the\n`Σ`-fibration over the `p`-torsion is consumed."
    },
    {
      "type": "prose",
      "md": "Everything above is short; the height of the port is here. mathlib has the\ndivision polynomials `Φ`, `ΨSq`, `ψ` and their degrees, but **no** API relating\nthem to the point group. The port's `FLTForHuman/Elliptic/` supplies that missing\nbridge (re-derived from mathlib's elliptic-net theory), and it is the only\ngenuinely new mathematics in the effort (`logs/card-torsion-port.md` §1).\n\nThe polynomial side of this bridge — what `Φ`, `Ψ`, `ΨSq`, `ψ` are, the EDS\nsequence `normEDS` that generates them, the net relation underneath, and the\ncomplement/invariant/`ωe` layer — is a subject of its own and has its own\nworksheet: `play/DivisionPolynomials.lean`. This zone is the point-side reading\nof the same layer. ",
      "zone": "D",
      "line": 268
    },
    {
      "type": "prose",
      "md": " On a point, `(y − negY x y)²` is `Ψ₂Sq x` — the `2`-division polynomial\nevaluated on a point of the curve. ",
      "zone": "D",
      "line": 282
    },
    {
      "type": "check",
      "line": 284,
      "raw": "#check @FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval",
      "display": "@FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval",
      "card": "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval"
    },
    {
      "type": "prose",
      "md": " ### Q4 — what is `W.Φ`?\n\n`Φ` is mathlib's `WeierstrassCurve.Φ`, the univariate `n`-division polynomial\n`φₙ` (capital phi). It is not a primitive: it is assembled from the auxiliary\nnormalised-EDS sequence `preΨ` and the univariate `ΨSq`, which is the shadow of\n`ψ n ^ 2` on the curve:\n\n  `Φ n = X * ΨSq n - preΨ (n + 1) * preΨ (n - 1) * (if Even n then 1 else Ψ₂Sq)`\n\nThis is the univariate form of the classical bivariate\n`φₙ = X · ψₙ² - ψₙ₊₁ · ψₙ₋₁`; `ΨSq n` is congruent to `ψ n ^ 2` in the coordinate\nring and `Φ n` to `φ n`. The `preΨ`/`if Even` bookkeeping is there so that `Φ n`\nand `ΨSq n` can be defined, and their leading terms computed, without ring\ndivision and without passing to the coordinate ring.\n\nWhat it does is the `x`-coordinate of multiplication by `n`:\n`x (n • P) = Φ n (x) / ΨSq n (x)`, with `ΨSq n (x) = 0` precisely when `n • P = 0`\n(`smul_x_eq` and `smul_formula_or_zero` below). So `Φ / ΨSq` is the `x`-part of\n`[n]`, a degree-`n²`-over-degree-`(n² - 1)` rational function on the `x`-line —\n`Φ` is the degree of `[n]` made into a polynomial, and hence the source of the\n`n²` in the theorem. ",
      "zone": "D",
      "line": 286
    },
    {
      "type": "check",
      "line": 307,
      "raw": "#check @WeierstrassCurve.Φ",
      "zone": "D",
      "name": "WeierstrassCurve.Φ",
      "display": "@WeierstrassCurve.Φ",
      "card": "WeierstrassCurve.Φ"
    },
    {
      "type": "print",
      "line": 308,
      "raw": "#print WeierstrassCurve.Φ",
      "zone": "D",
      "name": "WeierstrassCurve.Φ",
      "display": "WeierstrassCurve.Φ",
      "card": "WeierstrassCurve.Φ"
    },
    {
      "type": "check",
      "line": 309,
      "raw": "#check @WeierstrassCurve.ΨSq",
      "zone": "D",
      "name": "WeierstrassCurve.ΨSq",
      "display": "@WeierstrassCurve.ΨSq",
      "card": "WeierstrassCurve.ΨSq"
    },
    {
      "type": "check",
      "line": 310,
      "raw": "#check @WeierstrassCurve.preΨ",
      "zone": "D",
      "name": "WeierstrassCurve.preΨ",
      "display": "@WeierstrassCurve.preΨ",
      "card": "WeierstrassCurve.preΨ"
    },
    {
      "type": "check",
      "line": 311,
      "raw": "#check @WeierstrassCurve.ψ",
      "zone": "D",
      "name": "WeierstrassCurve.ψ",
      "display": "@WeierstrassCurve.ψ",
      "card": "WeierstrassCurve.ψ"
    },
    {
      "type": "check",
      "line": 312,
      "raw": "#check @WeierstrassCurve.φ",
      "zone": "D",
      "name": "WeierstrassCurve.φ",
      "display": "@WeierstrassCurve.φ",
      "card": "WeierstrassCurve.φ"
    },
    {
      "type": "prose",
      "md": " The bridge: on a nonsingular point, `n • P = 0` implies `ΨSq n` vanishes there.\nThis is what turns every group-theoretic statement above into a polynomial\nstatement, and vice versa. ",
      "zone": "D",
      "line": 314
    },
    {
      "type": "check",
      "line": 317,
      "raw": "#check @FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero",
      "display": "@FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero",
      "card": "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero"
    },
    {
      "type": "prose",
      "md": " Separability of `[n]`, used twice: `Φ n` and `ΨSq n` are coprime, and\nconsecutive `ΨSq` are coprime. The engine for both is the Wronskian. ",
      "zone": "D",
      "line": 319
    },
    {
      "type": "check",
      "line": 321,
      "raw": "#check @FLTForHuman.Elliptic.isCoprime_Φ_ΨSq",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq",
      "display": "@FLTForHuman.Elliptic.isCoprime_Φ_ΨSq",
      "card": "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq"
    },
    {
      "type": "check",
      "line": 322,
      "raw": "#check @FLTForHuman.Elliptic.isCoprime_ΨSq_succ",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.isCoprime_ΨSq_succ",
      "display": "@FLTForHuman.Elliptic.isCoprime_ΨSq_succ",
      "card": "FLTForHuman.Elliptic.isCoprime_ΨSq_succ"
    },
    {
      "type": "check",
      "line": 323,
      "raw": "#check @FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero",
      "display": "@FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero",
      "card": "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero"
    },
    {
      "type": "prose",
      "md": " The multiplication formula: from `(x, y)` to the `x`-coordinate of `n • P`, and\nthe resulting condition for `n • P = 0`. ",
      "zone": "D",
      "line": 325
    },
    {
      "type": "check",
      "line": 327,
      "raw": "#check @FLTForHuman.Elliptic.smul_x_eq",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.smul_x_eq",
      "display": "@FLTForHuman.Elliptic.smul_x_eq",
      "card": "FLTForHuman.Elliptic.smul_x_eq"
    },
    {
      "type": "check",
      "line": 328,
      "raw": "#check @FLTForHuman.Elliptic.smul_formula_or_zero",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.smul_formula_or_zero",
      "display": "@FLTForHuman.Elliptic.smul_formula_or_zero",
      "card": "FLTForHuman.Elliptic.smul_formula_or_zero"
    },
    {
      "type": "prose",
      "md": " The finiteness input for the double-fibre trick: only finitely many `c` make\n`Φ n − C c · ΨSq n` non-squarefree. ",
      "zone": "D",
      "line": 330
    },
    {
      "type": "check",
      "line": 332,
      "raw": "#check @FLTForHuman.Elliptic.finite_not_squarefree_fiber",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.finite_not_squarefree_fiber",
      "display": "@FLTForHuman.Elliptic.finite_not_squarefree_fiber",
      "card": "FLTForHuman.Elliptic.finite_not_squarefree_fiber"
    },
    {
      "type": "prose",
      "md": " The 2-torsion dictionary used by the `n = 2` branch: `P` is 2-torsion iff it\nequals its own negative, i.e. iff `y = negY x y`. ",
      "zone": "D",
      "line": 334
    },
    {
      "type": "check",
      "line": 336,
      "raw": "#check @FLTForHuman.Elliptic.mem_nTorsion_two_iff",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.mem_nTorsion_two_iff",
      "display": "@FLTForHuman.Elliptic.mem_nTorsion_two_iff",
      "card": "FLTForHuman.Elliptic.mem_nTorsion_two_iff"
    },
    {
      "type": "prose",
      "md": "* In `#E[12] = 144` above, change `12` to `6`, `9`, or a prime power. The\n  coprime branch only fires when the split is actually coprime; `9 = 3 · 3` is\n  the prime-power branch instead.\n* Delete `hn : (12 : K) ≠ 0` and watch the `h3`/`h4` obligations become\n  unprovable: that is the hypothesis doing its job.\n* Delete `[IsAlgClosed K]` from `#E[12] = 144` and watch which step survives.\n  The CRT step does not need it; the count does.\n* Replace `[DecidableEq K]` by `Classical.decEq`'s `letI` and see that it is a\n  structure on the point group, not a mathematical hypothesis.\n* The next subject in this direction is the *classification*: the equivalence\n  `ZMod n × ZMod n ≃+ E[n]` (`FLTForHuman/Elliptic/TorsionZMod.lean`), which\n  descends from this theorem. It is a different subject, so a different\n  worksheet; its module now imports in ~5.5 s warm, so asking for it is cheap\n  (ground rule R1). ",
      "zone": "E",
      "line": 338
    },
    {
      "type": "prose",
      "md": "Oldest first. Each entry: question, one-line answer, and a pointer to the zone\nthat was edited.\n\n* (2026-10-14) *Worksheet created.* — no questions yet.\n* (2026-10-14) **Q1.** Are `⊤`/`⊥` special (the UI specializes them to module),\n  or are they just true and false, `rfl`? — They are plain notation for\n  `Top.top`/`Bot.bot` resolved by the expected type; their carriers *are*\n  `univ`/`{0}` by `rfl` and membership in them is definitional, but the\n  submodule-level equations are not, because `torsionBy 0` is a kernel and\n  `zero_smul`/`one_smul` are structure laws. See the Q1 block in Zone A.\n* (2026-10-14) **Q2.** With the fibre count as a covering map, isn't `2 * n²`\n  only true for `n = 2` — an even count is too low to reach `n²`? — No: `2 * n²`\n  is the size of the union of *two* fibres (over `Q` and `-Q`), i.e.\n  `2 * #E[n]`, and the `2` on the right is the `y`/`negY` pairing; `n²` is\n  already there as `deg (Φ n)`. The oddness on the lemma is unused. See the\n  circle-breaker block in Zone B.\n* (2026-10-14) **Q3.** *Correction:* a covering map can have an infinite cover\n  and a finite fibre — that is exactly the case here. — Conceded; the Zone B\n  paragraph was wrong to blame the infinitude of `E(K)`. The covering picture\n  gives constancy of the fibre (`card_smul_fiber`), while the gap is the\n  *value* (`deg[n] = n²`, isogeny degree) and, formally, finiteness. See the\n  corrected `card_smul_fiber` block in Zone B.\n* (2026-10-14) **Q4.** What is `W.Φ`? — mathlib's univariate `n`-division\n  polynomial `φₙ`, assembled from `preΨ`/`ΨSq`; it is the numerator of\n  `x (n • P)`, so its degree `n²` is the degree of `[n]` and the source of the\n  theorem's `n²`. See the Q4 block in Zone D. ",
      "zone": "Q",
      "line": 355
    },
    {
      "type": "code",
      "line": 384,
      "text": "end Play",
      "zone": "Q"
    }
  ],
  "seed_cards": ["AddSubgroup.card_bot","Bot.bot","Classical.decEq","FLTForHuman.Elliptic.card_nTorsion","FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime","FLTForHuman.Elliptic.card_nTorsion_odd_fibers","FLTForHuman.Elliptic.card_nTorsion_one","FLTForHuman.Elliptic.card_nTorsion_prime","FLTForHuman.Elliptic.card_nTorsion_prime_pow","FLTForHuman.Elliptic.card_nTorsion_two","FLTForHuman.Elliptic.card_smul_fiber","FLTForHuman.Elliptic.card_torsion_of_isAlgClosed","FLTForHuman.Elliptic.exists_double_fiber_card","FLTForHuman.Elliptic.finite_not_squarefree_fiber","FLTForHuman.Elliptic.isCoprime_Φ_ΨSq","FLTForHuman.Elliptic.isCoprime_ΨSq_succ","FLTForHuman.Elliptic.mem_nTorsion_two_iff","FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero","FLTForHuman.Elliptic.smul_formula_or_zero","FLTForHuman.Elliptic.smul_surjective","FLTForHuman.Elliptic.smul_x_eq","FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval","FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero","Module","Nat.card","Nat.recOnPosPrimePosCoprime","Set.univ","Submodule.mem_bot","Submodule.mem_top","Submodule.mem_torsionBy_iff","Top.top","True","WeierstrassCurve.Affine.negY","WeierstrassCurve.isElliptic_iff","WeierstrassCurve.natDegree_Φ","WeierstrassCurve.natDegree_ΨSq","WeierstrassCurve.preΨ","WeierstrassCurve.Φ","WeierstrassCurve.Ψ","WeierstrassCurve.ΨSq","WeierstrassCurve.φ","WeierstrassCurve.ψ","addOrderOf_dvd_of_nsmul_eq_zero","exists_prime_addOrderOf_dvd_card'","normEDS","one_smul","zero_smul"],
  "card_count": 121,
  "modules": ["FLTForHuman.Elliptic.TorsionCard","Init.Classical","Init.Core","Init.Data.Cast","Init.Data.Function","Init.Data.Int.Basic","Init.Data.Nat.Coprime","Init.Prelude","Mathlib.Algebra.Algebra.Defs","Mathlib.Algebra.Field.Defs","Mathlib.Algebra.Group.Action.Defs","Mathlib.Algebra.Group.Defs","Mathlib.Algebra.Group.Even","Mathlib.Algebra.Group.Monoid","Mathlib.Algebra.Group.Subgroup.Defs","Mathlib.Algebra.Group.Subgroup.Finite","Mathlib.Algebra.Group.Units.Defs","Mathlib.Algebra.GroupWithZero.Action.Defs","Mathlib.Algebra.GroupWithZero.Defs","Mathlib.Algebra.GroupWithZero.Hom","Mathlib.Algebra.Module.Defs","Mathlib.Algebra.Module.LinearMap.Defs","Mathlib.Algebra.Module.Submodule.Defs","Mathlib.Algebra.Module.Submodule.Lattice","Mathlib.Algebra.Module.Torsion.Basic","Mathlib.Algebra.Polynomial.Basic","Mathlib.Algebra.Polynomial.Degree.Defs","Mathlib.Algebra.Polynomial.Derivative","Mathlib.Algebra.Polynomial.Eval.Defs","Mathlib.Algebra.Ring.Defs","Mathlib.Algebra.Ring.Hom.Defs","Mathlib.Algebra.Ring.Parity","Mathlib.Algebra.Squarefree.Basic","Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula","Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree","Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","Mathlib.Basic.Finite.Defs","Mathlib.Basic.Logic.Basic","Mathlib.Basic.Nontrivial.Defs","Mathlib.Data.Nat.Factorization.Induction","Mathlib.Data.Nat.Prime.Defs","Mathlib.Data.Set.Defs","Mathlib.FieldTheory.IsAlgClosed.Basic","Mathlib.GroupTheory.OrderOfElement","Mathlib.GroupTheory.Perm.Cycle.Type","Mathlib.NumberTheory.EllipticDivisibilitySequence","Mathlib.Order.Notation","Mathlib.RingTheory.Coprime.Basic","Mathlib.SetTheory.Cardinal.Defs","Mathlib.SetTheory.Cardinal.Finite"]
};
