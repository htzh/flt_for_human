# GitHub Markdown math: writing rules and a debugging recipe

`base/006` (numbered `base/005` when this was written) looked perfect in the DSH GUI
and rendered error boxes on GitHub.
This note records what was learned: (1) what GitHub does to math, stated as
writing rules, and (2) the method that located the offending spans — the part
worth keeping, because this class of bug is invisible locally.

Writing conventions themselves (backtick inline form, `\\` inside `$$…$$`) live
in [../AGENTS.md](../AGENTS.md) and are not re-derived here. This note adds the
layer AGENTS.md does not mention — GitHub's HTML escaping — and the debugging
recipe. Every claim below was checked against GitHub's *served pages* and
against both engines locally; single observations are flagged as such.

## Part 1 — Best practice for GitHub Markdown math

### 1.1 Three stages between the `.md` and the glyph

1. **Markdown.** The page is parsed as Markdown before anything mathematical
   happens. A `\` before a punctuation character is consumed (`\;` → `;`,
   `\{` → `{`, `\\` → `\`); a `\` before a letter survives (`\lt`, `\Delta`,
   `\qquad`). The backtick inline form is a code span, so its content is
   literal; `$$…$$` is not a code span, which is exactly why AGENTS.md doubles
   backslashes inside displays. Verified: source `$$x \\;=\\; y$$` is served as
   `$$x \;=\; y$$`.
2. **HTML.** Every math region is wrapped in a literal
   `<math-renderer …>…</math-renderer>` element and HTML-escaped. The number of
   escaping passes depends on *where* the math sits, and this is the trap:

   | position | source | served bytes | engine receives |
   |---|---|---|---|
   | top-level `$$…$$` | `a < b` | `a &lt; b` | `a < b` (fine) |
   | top-level `$$…$$` | `a & b` | `a &amp; b` | `a & b` (fine) |
   | inline | `k < d` | `k &amp;lt; d` | `k &lt; d` (broken) |
   | inline | `a & b` | `a &amp;amp; b` | `a &amp; b` (broken) |
   | `$$…$$` in a list item | `b' < M/a` | `b' &amp;lt; M/a` | `b' &lt; M/a` (broken) |

   Inline math is nested inside a code-span element, so its text is escaped
   once for that element and once more when the whole region is embedded —
   two passes instead of one. The nesting is visible in the raw response, which
   keeps the code-span markup inside the math payload:

   ```
   $\psi(N)</code> in $<code>Y$
   ```
3. **Engine.** The browser decodes each entity exactly once and hands the
   result to MathJax, for which `&` is the *alignment tab*. So `&lt;` is not a
   less-than sign: it is a misplaced alignment character.

### 1.2 Rules

1. **Never write a literal `<` or `>` inside math.** Use `\lt` / `\gt`: they
   are letters, so Markdown leaves them alone and HTML never escapes them, and
   both MathJax and KaTeX support them. This holds everywhere, even though a
   top-level `$$…$$` currently survives a literal `<`.
2. **Never write a bare `&` inside inline math.** The failure is quiet rather
   than loud: inside an inline `pmatrix` or `aligned` the escaped `&` is still a
   legal alignment tab, so nothing errors — the leftover `amp;` simply becomes
   cell text and the matrix grows a junk column (`(aamp;bcamp;d)` is the real
   rendering of a two-column `pmatrix` written the obvious way). Outside an
   alignment environment it does raise `Misplaced &`. Inside a *top-level
   display* the alignment `&` is correct (one escaping pass, decodes back to
   `&`).
3. **No blank line inside `$$…$$`.** GitHub scans a *paragraph* for `$$…$$`;
   a blank line splits the block and nothing is rendered at all — no error
   box, the source just shows up as text. Verified.
4. **A display gets its own paragraph at column 0.** A `$$…$$` nested in a list
   item is escaped twice, i.e. it behaves like inline math: rules 1 and 2 apply
   with no exception there.
5. **No HTML-looking content inside `$$…$$`** (`<ul>…`, `<img/>`): the math scan
   then refuses the block, or Markdown turns the content into real HTML first.
6. **Keep the AGENTS.md doubling rules for displays**: the punctuation macros
   `\\,`, `\\;`, `\\{`, `\\}` and the row separator `\\\\`. A single backslash
   before a letter is typed as-is.
7. **The backtick form is literal for backslashes only.** AGENTS.md's "inside
   this form everything is literal" is true of *Markdown* escapes; `<`, `>`
   and `&` are still HTML-escaped twice. That is the one place the convention
   does not protect you.
8. **Lint and sweep before pushing** (§2.2). The failure mode is invisible in
   the DSH GUI, which renders with its own bundled KaTeX and treats the
   backtick form as literal.

### 1.3 Evidence ledger

- The revision that showed the errors is `500f7c6` ("Explain the modular
  equation."). Its served page carries 27 display and 434 inline math payloads;
  HTML-decoded once (what the browser does) and rendered with MathJax they give
  **display 0 failures, inline 4 failures** — exactly the four spans containing
  `<`: `k < d`, `0 \le b < d`, `\{(a,b) : … b < M/a …\}` and `\prod_{b<p}`.
  The `Φ₂` display that was suspected first renders cleanly.
- The quiet case, measured apart: `\begin{pmatrix} a &amp; b \\ c &amp; d
  \end{pmatrix}` raises no MathJax error at all, and KaTeX's visible text for it
  is `(aamp;bcamp;d)`. A bare `x &amp; y` outside an alignment does error
  (`Misplaced &`).
- A lint over `base/` and `math/` (§2.2) currently finds **78 math spans
  containing a raw `<`, `>` or `&`**, mostly inline `pmatrix`. Triage matters:
  the inline hits are live defects — a red box for `<`/`>` outside an alignment
  environment, silent junk for `&` inside one — while the top-level display hits
  render correctly today and are only the uniform rule's outstanding debt.
- Message vocabulary identifies the engine. MathJax reports `Misplaced &` for
  every position tested (bare `&`, inside a subscript group, inside a
  literal-brace group, `&lt;`, `&amp;lt;`). KaTeX 0.18.7 reports
  `KaTeX parse error: Expected 'EOF', got '&' at position 3: …` and does *not*
  contain the string "Extra open brace or missing close brace".
- **GitHub uses MathJax**, the DSH GUI uses KaTeX: GitHub's docs mention MathJax
  27 times and KaTeX zero times, while the GUI bundles KaTeX and renders
  failures as a red `<span class="katex-error">` whose `title` holds the
  message. Local and remote rendering therefore disagree by construction.
- `tools/check_math_delimiters.py`'s docstring says "GitHub renders math
  client-side (KaTeX)". That sentence is wrong for GitHub (it describes the
  GUI); the checker itself is about delimiters and is unaffected.

## Part 2 — How to debug a rendering problem

### 2.1 The recipe

1. **Reproduce at the consumer's boundary.** Do not re-test your own copy of
   the text — fetch the bytes the browser actually received. For GitHub this is
   `https://github.com/<org>/<repo>/blob/<sha>/<path>`; the *per-commit* form
   makes an old revision reproducible long after it was fixed (that is how
   `500f7c6` was re-examined). Then extract the math payloads and HTML-decode
   **once** — twice is a different experiment.
2. **Identify the engine from the message.** MathJax and KaTeX have disjoint
   message shapes (`Misplaced &` vs `KaTeX parse error: …`), and the engine
   tells you which layer to suspect. A message you cannot produce locally is
   *not* explained; say so instead of substituting a plausible story.
3. **Bisect the input, one variable at a time.** Keep the original and change a
   single feature per variant (original / `<` replaced by `\lt` / the `\ \)`
   runs replaced by `\quad`). If every variant passes, the model is wrong —
   that result is information, not failure.
4. **Test candidate mechanisms against the engine directly**, with minimal
   inputs (`x &lt; y`, `\sum_{i&lt;j}`, `{i&j}`, `x & < y`). The message
   vocabulary then pins the mechanism instead of your intuition.
5. **Read the consumer's code when behaviour is surprising.** The served page
   lists its scripts; `element-registry-*.js` maps the `math-renderer` custom
   element to lazily loaded chunks, and grepping those for a marker string
   tells you whether the renderer reads `textContent` (entities decoded once)
   or `innerHTML`.
6. **Distrust convenience proxies.** GitHub's `POST /markdown` API is handy and
   correct about some things (it confirmed the backslash stage and the inline
   double escape) but it is *not* the page pipeline: it single-escapes display
   math where the page sometimes double-escapes, and it mangles the backtick
   form into payloads that still carry code-span markup (§1.1) where the page
   serves the same source as one clean payload. Verify on a real page before
   believing an API.
7. **Sweep and count.** Zero failures over every span of the file is the
   acceptance test; a single hand-checked example is not.
8. **Treat counter-evidence from the user as data.** "The other notes are fine"
   refuted a global claim and localised the bug to inline math. The corrected
   model is what is written above.
9. **Clean up the harness.** Scratch files belong in `.tmp/` (untracked, and
   removed when done) — the user commits, and a stray `node_modules` in the
   workspace is noise in `git status`.

### 2.2 Toolbox (copy-paste)

Fetch a served page and extract what the engine will see:

```bash
mkdir -p .tmp; SHA=500f7c6; F=base/006-the-modular-equation.md
python3 - <<PY
import urllib.request, re, html, json
url = f"https://github.com/htzh/flt_for_human/blob/$SHA/$F"
page = urllib.request.urlopen(urllib.request.Request(
    url, headers={'User-Agent': 'Mozilla/5.0'}), timeout=120).read().decode()
blocks = re.findall(r'<math-renderer([^>]*)>(.*?)</math-renderer>', page, re.S)
items = [{"display": 'js-display-math' in a, "content": html.unescape(b)}
         for a, b in blocks]     # exactly one decode = the browser's
json.dump(items, open('.tmp/page.json', 'w'))
print(len(items), "payloads")
PY
```

Render them with MathJax locally (the sandbox cannot write `~/.npm`, hence
`--prefix` / `--cache`; `/tmp` does not survive between shell calls, `.tmp/`
does):

```bash
mkdir -p .tmp && npm install --prefix .tmp/mjx --cache .tmp/npmcache mathjax-full
```

```js
// .tmp/mjx/check.js — report every payload MathJax refuses
const fs = require('fs');
const {mathjax} = require('mathjax-full/js/mathjax.js');
const {TeX} = require('mathjax-full/js/input/tex.js');
const {SVG} = require('mathjax-full/js/output/svg.js');
const {liteAdaptor} = require('mathjax-full/js/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler} = require('mathjax-full/js/handlers/html.js');
const {AllPackages} = require('mathjax-full/js/input/tex/AllPackages.js');
const adaptor = liteAdaptor(); RegisterHTMLHandler(adaptor);
const doc = mathjax.document('', {InputJax: new TeX({packages: AllPackages}),
                                  OutputJax: new SVG({fontCache: 'none'})});
const items = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
let bad = 0;
for (const it of items) {
  const c = it.content.replace(/^\$\$/, '').replace(/\$\$$/, '')
                      .replace(/^\$/, '').replace(/\$$/, '');
  const out = adaptor.outerHTML(doc.convert(c, {display: it.display,
                                                em: 16, ex: 8, containerWidth: 1000}));
  const m = /data-mjx-error="([^"]*)"/.exec(out);
  if (m) { bad++; console.log(m[1] + '  <- ' + JSON.stringify(c).slice(0, 110)); }
}
console.log('failures:', bad, 'of', items.length);
```

Probe the API pipeline directly (fast, unfaithful — see 2.1.6):

```bash
python3 - <<'PY'
import json, urllib.request
doc = "inline $k < d$ and display\n\n$$a < b$$\n"
req = urllib.request.Request("https://api.github.com/markdown",
    data=json.dumps({"text": doc, "mode": "gfm"}).encode(),
    headers={"Content-Type": "application/json", "User-Agent": "note-check"})
print(urllib.request.urlopen(req, timeout=60).read().decode())
PY
```

Lint the sources for the three dangerous characters inside math (it ignores
fenced blocks and syntax examples inside code spans, so it is safe to run on
this note too):

```bash
python3 - <<'PY'
import re, glob
FENCE = re.compile(r'```.*?```', re.S)

def spans(s):
    for kind, pat in (('display', r'\$\$[\s\S]*?\$\$'),
                      ('inline',  r'\$`([\s\S]*?)`\$')):
        for m in re.finditer(pat, s):
            line = s[s.rfind('\n', 0, m.start()) + 1:m.start()]
            if line.count('`') % 2:      # a syntax example inside a code span
                continue
            yield kind, m.group(0)

for f in sorted(glob.glob('base/*.md') + glob.glob('math/*.md')):
    s = FENCE.sub('', open(f, encoding='utf-8').read())
    for kind, body in spans(s):
        if any(c in body for c in '<>&'):
            print(f, kind, body[:60].replace('\n', ' '))
PY
```

and the delimiter checker (`python3 tools/check_math_delimiters.py <file>`,
which skips fenced code blocks and so can be run on this note).

### 2.3 Wrong turns taken here (don't repeat)

- **Generalising from one observation**: "GitHub escapes `<` inside math" was
  turned into "every `<` in math on GitHub is broken", which the other notes
  contradict. The true statement is narrower: it breaks in inline math and in
  list-nested displays.
- **Trusting the API as a stand-in for the page** (2.1.6), which produced both
  a false positive (a display that the page serves correctly) and false detail
  (mangled backtick payloads).
- **Explaining a message that was never reproduced.** The user's
  "Extra open brace or missing close brace" was never produced here; matching
  it to a plausible cause is how the wrong explanation got published in the
  first place.
- **Assuming the quoted display was the failing one.** It rendered correctly on
  every test; the actual failures were four inline spans elsewhere.

### 2.4 Unresolved

- The exact error string the browser showed for those four spans (GitHub's
  MathJax build may word a misplaced `&` inside a braced group differently from
  the `mathjax-full` build used here, which says `Misplaced &`).
- Why a list-nested display is escaped twice — one observation (`math/010`),
  consistent with the code-span mechanism, but not proved.
- The final pixels were never inspected: the served bytes and both engines'
  behaviour are measured, but whether the junk column is what a reader sees on
  GitHub today (rather than something GitHub's client script repairs) needs a
  browser.
