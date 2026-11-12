## Instructions for Refactoring

Agents don't edit this unless directed to do so.

### Good/Bad API design

A good API design expose the main idea of the math as conveniently for the reader as possible.
That means if the argument can be made in one place don't split it.
Meanwhile basic, obvious, technicalities like type adaptations should be factored out to reduce noise in the main line.
Math content can also be a good candidate if it is focus on a narrow subject and/or can be generalized to not carry the main line's special context.

Many bad APIs are written like goto statements.
The main context has to be threaded through the layers.
Lemmas are hard to understand because they are actually proof steps and carry many premises.
 
When a bad API design is encountered, the first thing to do is to inline the layers of helpers until the math is clearlystated in the headline theorem.
After that the princples stated earlier for a good API design can be applied to refactor for readability.

### Public API

During refactor public API is fair game especially for theorems that are masquerading as APIs that are actually proof steps.
If API is used outside of the theory being refactored due respect should be paid to outside consumers and a facade can be used to preserve the signature.
A word on the checkers and the FLT clone: they are useful as guideposts during the initial port, but during refactor math clarity is what matters the most.

### Proof Practice

Use calc in the main line to explain unreadable rw stack.
No small step premises on the main stack.
For example: if hzeta is about a primitive root and you need to show its n-th power is 1 the correct thing to do is to have a helper that gives you that and use it at the site where it is needed.
Proof steps in the main line should be shown with haves instead of helpers.

### Hygiene

No inline comments.
Code speaks for itself.
Docstrings are good.
Do not cross reference in a source file unless absolutely necessary: an external change should not cause a comment to berewritten and a gratuitous rebuild to cascade.
Do not use Lean files as documents.
Minimize the number of edits by batching up -- so no editing the docstrings unless the code changes.
No tree build.
Assume other refactors could follow.
Follow general build hygiene.
[General guideline](instructions.md) should still be followed when practicable.
