# Play — the browser reader for `lean/play` worksheets

A static app for reading the FLT playback worksheets in a browser and looking up
the declarations they mention. It replaces the editor-only loop
(`#check` shows an elaborated type, `#print` an elaborated term, “go to
definition” opens another window) with:

- the worksheet as a document — metadata, zones, prose, code, question log;
- a **card** for every checked name: sugared source, docstring, kind, module,
  source location, and the declarations it directly uses;
- `#print` replaced by the **source** definition, not the normalized term;
- `#check` replaced by the **source** signature, with the elaborated type
  available under the Type tab;
- search, deep links and history.

This is an MVP with **one materialized layer** of references. A card that is a
worksheet seed carries its references; a pure reference card is a leaf. Chains
can therefore continue through cards that are themselves seeds, but there is no
recursive expansion beyond the data in the build. A reference without a card is
shown as a stub.

## Run

**No server is required.** The data are classic `<script>` shards, not `fetch`ed
JSON, so Chrome allows them from `file://`: double-click `play/index.html`, or
drag it into the browser. A static server works too:

```bash
# from the repository root
python3 -m http.server 8080      # http://localhost:8080/play/index.html
python3 -m http.server -d play 8080   # http://localhost:8080/index.html
```

The same files work on GitHub Pages; all URLs are relative.

On a worksheet, **Hide zones** collapses the left zone outline and gives the
worksheet (and the open card) more width. The choice is remembered across pages.
The head shows the worksheet's `Intro`; provenance and build metadata (`reads`,
`pin`, `file`, `check`, `status`, `date`) are collapsed under “source & build”.

- `index.html` — the worksheet list and a global declaration search.
- `worksheets/<Slug>.html` — one worksheet; the card panel opens on the right
  (or as a bottom sheet on narrow screens).
- `worksheets/<Slug>.html#decl=<full-name>` — deep link to a card.
- `index.html#q=<text>` — a search hint (the search box is the main entry).

## Contents

```
index.html
worksheets/CardNTorsion.html
worksheets/DivisionPolynomials.html
assets/app.js
assets/style.css
version.json                          build id, fetched no-store for cache busting
data/index.js                         manifest: worksheets, names, card_module, search
data/ws-<Slug>.js                     one worksheet: blocks + modules to prefetch
data/modules/<ModulePath>.js          one shared module: cards defined there
```

The shared unit is the **defining Lean module**, stored as a directory tree that
mirrors the module namespace:

```
data/modules/Mathlib/Algebra/Module/Torsion/Basic.js
data/modules/FLTForHuman/Elliptic/TorsionCard.js
```

A module used by both worksheets appears once; each `ws-<Slug>.js` lists only
the modules it needs, so a page loads its own slice of the graph (currently 53
of 79 modules for `CardNTorsion`). A card that is not prefetched is loaded on
demand through `index.card_module`. The tree keeps directories browsable as the
port and mathlib grow, instead of a flat directory with thousands of files.

The generated files are checked in so the app works without any tooling; they
are produced from the tracked worksheets and the Lean environment.

Each page's inline bootstrap fetches `version.json` with `cache: "no-store"` and
loads `app.js` and the data shards with `?v=<build>`. That keeps an aggressively
caching browser (Silk, GitHub Pages edge cache) from serving old JS; `file://`
falls back to a plain script tag because `fetch` is unavailable there. The build
only rewrites shards whose bytes actually changed, so a rebuild is idempotent.

## Data format

Every data file is a classic script, loaded with `<script src=…>`, not `fetch`:

```js
// data/modules/Mathlib/NumberTheory/EllipticDivisibilitySequence.js
window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["Mathlib.NumberTheory.EllipticDivisibilitySequence"] = {…};

// data/index.js
window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_INDEX = {…};
```

This is the same approach the FLT documentation site uses (`data/*.js` shards),
and it is why opening the page from disk works without a static server. There is
no LFS: the whole data set is ~0.7 MB of normal tracked files and grows by one
module shard at a time.

The shards are written line-oriented: one card per entry, one field per line, and
one worksheet block / search entry per line. A docstring edit therefore changes a
line rather than replacing a whole one-line shard, so generated data stays
reviewable in `git diff`.
