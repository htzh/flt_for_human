## FLT for human

### Quote directly

This file is constantly changing to reflect the current tasks.
Don't xref this file.
Quote the content directly instead.
Marking completion is okay.
No need to put explanatory note here, unless there is qualification that needs to be noted or more steps needed.
In general successful results belong in docs.

### Context

We will continue to produce math enrichment content around the FLT project files.
We will also improve the work flow.

### Current Goal

For the next math note, demonstrate the modularity theorem through a js app and trace the algorithm used to the proof.
We will assume the full modularity theorem so we will not check semistability.

Note 7 can be named with the themes "modularity" and "compute".

[done] Note 7 is `math/007-modularity-and-computation.md`; app is
`apps/modular/index.html` + `apps/modular/ec.js` (minimal model, Δ, conductor,
point counts / a_p, Hecke-recursion table n = 1..20, level-11 eta-product check,
trace-to-Lean table). Top-level `index.html` is now a landing page with the app
entry.

### Immediate Next Steps Needed

**1. Read AGENTS.md and notes/research-workflow-math-notes.md. [done]

**2. Go through Definitions/Def_FLTPrelim_Modularity.lean [done]

**3. Our App should do the following: [done]
- Start by letting the user input Weierstrass coefficeints
- Find the minimal model, show it in the output
- Compute the discriminant, show it in the output
- Compute conductor level, show it in the output
- At a prime p, reduce mod p, count points and calculate trace a_p
- Use recurrence to calculate the coefficients at n, tabulated for n from 1 to 20,
also show recurrence relations that applied

**4. Show the procedures used in the above steps and connect them to the FLT proof. [done]

### Known Challenges

- The file structure is flat so there are many files in directories like Theorems/.

- js app can not directly run from the github.com content page, so the math/ md note should link to htzh.github.io/flt_for_human/
instead. App should reside under apps/modular/index.html. Link directly to it from the md note. Also add an entry in
top level index.html.
