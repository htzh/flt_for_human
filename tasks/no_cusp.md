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

A base/ note on the proof of no level 2 weight 2 cusp forms.

[done] Note is `base/003-no-level-2-weight-2-cusp-forms.md`; entry added to
`base/README.md` and to the base-note list in the top-level `index.html`.

### Immediate Next Steps Needed

**1. [done] Read AGENTS.md and notes/research-workflow-math-notes.md.
Base note does not require the same level of citation rigor, esp. if it breaks narrative.
Base note should focus more on the flow of narratives.

**2. [done] Section 5 of math note 8 give a good summary over of the proof.
We don't need to repeat the content (esp. w.r.t. Lean mechanisms) there.

**3. [done] The index is 3: Gamma0_two_index_eq_three is derived locally within `/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean`.
You can trace the Lean mechanism in relative detail.
Show the corresponding argument in matrix terms for the reader.

**4. [done] The norm multiplies the weight by the index and no weight-6 cusp forms at level 1:
Deemphasize explaining Lean code.
Instead use Lean code as a guide to organize the proof in narrative.
Follow the Lean logic route, even though it may be dictated by Lean internal mechanics.
State the math logic, using Lean only as a route map.
Go into the proof of the Mathlib theorem as well, until the argument is fairly obvious college calculus leve math.

### Known Challenges

- The file structure is flat so there are many files in directories like Theorems/.
