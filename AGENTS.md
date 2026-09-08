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

## Github issues

Github math processer needs `\\,` in the equation for thin space.
It is also very finicky about \$ touching alpha-numeric symbols (including punctuation marks) when used as the inline math delimiter.
Either leave spaces around the delimiters or use \$\` and \`\$ (with the backslash) as inline math delimiters.
A second breaker: math containing `]()` (e.g. `$E_P[p](K)$`) gets parsed as a markdown link before math processing — always backtick those.
`\operatorname{...}` is not supported in equations — use `\mathrm{...}` instead (e.g. `$\mathrm{card}\\,M$`, `$\mathrm{GL}_2$`).
