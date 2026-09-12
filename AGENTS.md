# FLT for human

We will be developing math notes and tools to comprehend the Lean proof of FLT.

## git

This project is separately tracked on its own with a public repository.
Only user should commit and push to origin.

Git tracked files will be published on the internet.
Don't cross ref an untracked local file.
If needed directly quote content or cross ref a public repo.
 
tools/ subdirs will have their git repo for now until proper licenses and attributions are settled and they can be merged with the public top repo.

## FLT urls

Anthropic's FLT is both available on github and cloned locally.
Work with the local copy but reference the public copy in public (git tracked) files.
Because Github limit 1000 files per directory not all files in the local clone are rendered by Github.

* For Lean files we should use the raw addresses: e.g. `Definitions/Def_FLTPrelim_FreyPackage.lean` -> `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean`
* When citing line numbers, pin the source to a git version — `/main` is not stable. Use the commit sha (full or short) instead of `refs/heads/main`, e.g. `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean` and `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/html/route/s1.html`. The current pin is `aa2d8b3` (see the workflow note for how to re-pin).
* Most of html files can be reached as normal, with the top url `https://github.com/anthropics/fermats-last-theorem/blob/main/html/index.html`. 
However there are 1450 definition modules, htmls in the `def/` can only be reached through the raw urls.
Github serves all htmls as texts.
The main author is hosting a static website so for user convenience we could point there: `https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_XHDRModelAtP.html`.

### Line anchors

Github renders `/blob/` pages and supports line fragments: `#L66` highlights line 66 and `#L66-L69` highlights that range. Prefer them over a line number in the link label, so that mathlib and FLT citations are clickable:

* Rendered: `https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Galois/Basic.lean#L54-L59`
* Rendered: `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L74-L77`
* Not rendered: `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean` — `#L66` would do nothing here.

`raw.githubusercontent.com` stays correct when the content must be quoted verbatim or fetched by a tool; it just cannot carry an anchor. Only a *directory listing* is truncated at 1000 files, so a file page under `Definitions/` is fine even though the directory cannot be browsed.

## Github issues

Inline math must use the backtick form: open with a `$` immediately followed by a backtick, close with a backtick immediately followed by `$`. Inside this form everything is literal — no double backslash is needed, so `\#` and `\,` are enough.

Display math `$$...$$` is the one place where `\\` is still needed to produce a single `\` (e.g. `$$\mathrm{card}\\,E[n]$$`). In particular a matrix row separator is typed `\\\\`, and the punctuation macros `\{`, `\}`, `\;`, `\,` are typed `\\{`, `\\}`, `\\;`, `\\,`; a single backslash before a letter (`\Delta`, `\mathrm`, …) is left alone. A `pmatrix` written with `\\` collapses to one row.

Never use bare `$...$` inline math: its escaping rules differ from the backtick form and are easy to get wrong. `tools/check_math_delimiters.py` flags any bare `$`.

`\operatorname{...}` is not supported in equations — use `\mathrm{...}` instead (e.g. `\mathrm{card}\,M`, `\mathrm{GL}_2`).
