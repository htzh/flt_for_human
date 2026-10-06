# Pin-internal name prefixes, and the checker's prefix-strip promotion policy

**Status (snapshot, 2026-10-06; policy decided).** Records why the port's public surface
carries the pin's proof-local prefixes (`kw_`, `cw_`, `es1a10_`, …), what the statement
checker's matching rule forces, and the **decided** mechanism that lets a promoted helper
keep a prefix-free name while its statement is still diffed: a `kw_`-strip on the
pin-private index (§5). Measured against the pin
`anthropics/fermats-last-theorem@aa2d8b3`, the port's mathlib `v4.34.0`, and the checker
[`lean/spec/check_flt_statements.py`](../lean/spec/check_flt_statements.py). The policy
lands with P-SET-1 (§6).

## 1. The observation

`kw_` is the pin's, not the port's. The pin declares its proof-local helpers inside
namespaces it shares with the rest of the prelude — for instance
`private theorem _root_.PeriodPair.kw_toPoint_add` — so a leading token is what keeps
the names apart. It carries no mathematical content, and there are several of them:

| prefix | pin declarations |
|---|---:|
| `kw_` | 320 |
| `cw_` | 148 |
| `es1a10_` | 122 |
| `mp72a102_` | 84 |

(Counting leading `[A-Za-z][A-Za-z0-9]*_` tokens over the pin files the checker reads,
`private` included. The same census puts `exists_`, `ord_`, `mem_`, `coe_` at the top,
so only these worker tokens are prefixes in the intended sense; the rest are ordinary
English words in a name.)

Where the port transcribes such a helper and promotes it public, the prefix enters the
public surface: **306 `kw_*` declarations in 16 modules, 215 of them public** — 73 in
`WeierstrassCurve/IsogenyEndDatum/DualEndData.lean`, 44 in
`WeierstrassCurve/Velu/RestrictAlong.lean`, 28 in `Velu/OddOrder.lean`, 23 in
`AlgebraicCurve/Defs/PlaceCompletion.lean`, and the remaining 138 across twelve further
modules. That is the annoyance: a familiar name wearing somebody's initials.

## 2. What the playbook says

[`porting-playbook.md`](../lean/porting-playbook.md) has no rule about the prefixes.
`kw_` occurs once, in §2.4, and not as policy: it is the example showing that the
pre-port dedup test is name-anchored —
`kw_addSeam_restrictAlong_eq_placeOfEquation_charFree` is the same declaration as the
ported `es1a6_addSeam_restrictAlong_eq_placeOfEquation`. Four rules do decide the
question:

- **§4, the checker.** It diffs *statements* and ignores proofs, "matching names after
  normalising namespace qualification"; "keeping auxiliary blocks `private` is what
  keeps the list short"; and "a promotion of a pin-`private` declaration normally
  verifies through the checker's dotted-name fallback and needs no exemption".
- **§3.1, naming.** "Adopt mathlib's names where mathlib has them; keep FLT's where it
  does not, and say which is which in the header"; "a name that does not state its
  content gets a one-line gloss".
- **§2.4 and §5, promotion.** "re-privatize the pin-private name and keep local
  aliases"; "namespace policy is decided before the wave"; "rename at promotion when
  the pin name is already taken publicly"; and never rename "a frozen public name
  mid-wave".
- **§0.3, the gap rule.** "A situation this file does not cover is a gap to record,
  and to add here when it generalizes." This note is that record; the prefix rule
  itself is deliberately *not* added to the playbook yet.

## 3. Why the port keeps them: the checker matches by last name

The checker keys the pin's public declarations by **last-name component**
(`declarations`), so the port's namespacing need not match the pin's. Promotions are
handled by a second index that reads the pin's `private` declarations as well and keys
them by a two-component dotted name (`promoted_key`) and by bare last name. The main
loop tries, in order: the last-name index, then the dotted index, then reports
`MISSING` or `MISMATCH`.

Two facts decide the prefix:

1. **A promotion must keep the pin's last name.** The prefix is part of that name, so
   `kw_toPoint_add` promoted as `toPoint_add` resolves to nothing: the last-name lookup
   misses, the dotted fallback misses, and the declaration owes an `OWN_PROOFS` entry.
   That is precisely why `DualEndData.lean` says its pin-private helpers "are promoted
   public so the checker's dotted fallback verifies them" — and why it keeps the names.
2. **The port's own `private` layer is invisible.** `raw_declarations` skips `private`
   on the port side unless asked not to ("a private port helper is not part of the
   surface being verified"). A helper that stays private may be named for content,
   prefix-free, and nothing notices.

So promotion is itself a **verification device**: a pin-private helper promoted at its
pin name gets its statement diffed; kept private, it gets no statement coverage at all.
The alternative, an `OWN_PROOFS` entry, **skips the diff entirely** — an exempted
declaration is counted and never compared.

## 4. The policy

- **A helper worth another theory's import is promoted**, publicly, at the
  **prefix-stripped** pin name (`kw_G_ofTau_eq` → `G_ofTau_eq`). It keeps statement
  coverage through §5 and keeps the public surface free of the pin's collision tokens.
- **A helper local to its module stays `private`** and may be named freely; the private
  layer is not diffed.
- **A genuinely-own declaration stays on `OWN_PROOFS`**, with its reason.
- **The pin↔port name mapping goes in the module header** (playbook §3.1, §5).

The tension worth naming: a prefix-free public surface and verified promotions used to
pull against each other, because a promotion had to be written at the pin's dotted name.
§5 removes the pull.

## 5. The mechanism: a `kw_`-strip on the pin-private index

The prefix is only a name key, so the key can be relaxed while the check stays exact.
Register every pin declaration whose last name carries a `PIN_PREFIXES` token under its
**prefix-stripped last name** as well (`kw_G_ofTau_eq` → `G_ofTau_eq`); a port promotion
written at the content name then resolves through the *existing* last-name fallback, and
its statement is still diffed against the pin's original. Nothing is skipped and nothing
is exempted.

The index is not restricted to textually `private` declarations. The pin suppresses
visibility with `p2m_export` — invisible to a text checker — rather than Lean `private`:
`kw_G_ofTau_eq`, `kw_riemannZeta_six`, `kw_g₂_ofTau` and `kw_g₃_ofTau` are plain
`theorem`s (`S_PeriodPair_discriminant_ne_zero.lean` lines 255/279/309/315), so a
private-only fill would have left exactly the four promoted names `MISSING`. Indexing a
textually public `kw_*` name is harmless: `source` and the dotted lookup still run first,
so a pin public name can never be shadowed.

Why it stays honest:

- the strip is applied to the **pin** side only, so a pin *public* name is never
  shadowed — the public lookup still runs first;
- kind and normalised statement must still match exactly;
- it is a fallback, consulted after the pin-public and pin-private dotted lookups;
- each hit is reported as `renamed` (port name → pin name and source) and counted
  separately, so a public-surface change is auditable;
- `OWN_PROOFS` is consulted first, so a deliberately-own declaration is never silently
  absorbed.

Measured discrimination over the pin's 320 `kw_` private declarations: **248 distinct
stripped names**, of which only **3** carry more than one distinct statement
(`ffgc_isIntegral_adicCompletionIntegers_of_algebraic`, `point_infinite`,
`hk5f_addSumCoordSeamDataNCAt_proved`) and only **1** — `point_infinite` — is also a pin
public last name with a different statement. The candidate-list lookup already handles
the ambiguous three.

The token list is explicit and starts minimal, `PIN_PREFIXES = ("kw",)`. The other pin
tokens (`cw_`, `ffgc_`, `dcao_`, `mlc_`, `es1a*_`, `mp*a*_`, …) are added only after the
same measurement, one at a time.

The patch, in `check_flt_statements.py`: a `PIN_PREFIXES`/`strip_pin_prefix` helper after
`promoted_key`, a `stripped_source` index filled inside the pin-reading loop, one extra
lookup in the fallback chain after the dotted lookups, a `renamed` counter, and a
`renamed` field in the summary line. It relaxes the name key only: `find` still requires
the kind and the normalised statement to match.

### 5.1 Two rejected alternatives

A **statement-keyed fallback** (any pin declaration with the identical normalised
statement) is too blunt: the pin's 17,603 declarations have only 9,810 distinct statement
keys (65.4% unique), and the sharing is worst exactly where the compared "statement" is
uninformative — `def … : Prop` on 179 declarations, `def … : ModularForm 𝒮ℒ 12` on 45. It
would also stop `identical` meaning "this name resolves to a pin declaration".

An explicit **`RENAMED : {port name → pin dotted name}`** registry is exact and still
worth having for a rename that is not a prefix strip, but it is manual where the prefix
case is mechanical.

## 6. Adoption with P-SET-1

The policy lands with the first `PeriodPair` set
([`WORKORDER-P1-uniformization-core.md`](../lean/topics/velu/WORKORDER-P1-uniformization-core.md)),
because that set already contains helpers worth promoting: `riemannZeta_six`,
`G_ofTau_eq`, `g₂_ofTau`, `g₃_ofTau`, the scaling lemmas (`G_scale`, `g₂_scale`,
`g₃_scale`, `scale_lattice`, `scaleLatticeEquiv`) and the lattice-equality lemmas are
needed again by the `j`-line set, so they get a public home at the stripped names;
`mulLeftR`/`mulLeftZ`, `im_div_ne_zero`, `span_neg_fst` and the rest of the local
scaffolding stay `private`. The pin's `kw_E4cube`/`kw_E6sq`/`kw_E4cube_sub_E6sq` are
already in the port, statement-equal, as `UpperHalfPlaneAux.eCubeSubESq`
(`ModularForms/DiscPow.lean`) — import, do not re-prove and do not promote again; the
statement-level check above is what found that, and it is the reason the dedup pass is
run by statement rather than by name.

Landed with P-SET-1 (2026-10-06): the checker moved `5809 identical (311 promoted), 0
mismatched, 0 missing, 36 own` → `5853 identical (313 promoted, 4 renamed), 0 mismatched,
0 missing, 36 own`, the four `RENAMED` rows being `G_ofTau_eq`, `riemannZeta_six`,
`g₂_ofTau`, `g₃_ofTau`, each pointing at the pin's `kw_*` original. The delta is exactly
the new surface (Basic 30 + Discriminant 13 + Uniformization 1) plus the two `promoted`
scale/lattice lemmas and the four `renamed`; the fallback moved no earlier verdict.
`OWN_PROOFS` can shrink as renames it covers acquire checked mappings.

## 7. Reproduce

The census and the strip index come from the checker's own reader, so a re-measurement
needs no second parser:

```bash
cd lean/spec
python3 - <<'PY'
import collections, sys
from pathlib import Path
sys.path.insert(0, '.')
import check_flt_statements as C
flt = Path.home() / 'proj' / 'fermats-last-theorem'

pub, stripped = collections.defaultdict(list), collections.defaultdict(list)
n_kw = 0
for rel in C.SOURCES:
    p = flt / rel
    if not p.exists():
        continue
    text = p.read_text(encoding='utf-8')
    for name, (kind, stmt) in C.declarations(text).items():
        pub[name].append((kind, stmt))
    for raw, kind, stmt in C.raw_declarations(text, include_private=True):
        last = raw.rsplit('.', 1)[-1]
        if last.startswith('kw_'):
            n_kw += 1
            stripped[last[3:]].append((kind, stmt))
amb = sum(1 for v in stripped.values() if len(set(v)) > 1)
shadow = sum(1 for k, v in stripped.items()
             if k in pub and not any(c in pub[k] for c in set(v)))
print(f'{n_kw} kw_ private declarations, {len(stripped)} stripped names, '
      f'{amb} with more than one statement, {shadow} shadowed by a public name')
PY
```

A stripped name with more than one statement is what the candidate-list lookup has to
disambiguate; a shadowed one is resolved by the public-first order.
