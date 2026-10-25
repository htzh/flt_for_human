# Instructions on Running Porting Waves

** AGENTS: do NOT edit without permission! **

## Target Scoping

Use `frontier --ds` to see outstanding nodes for D-S. Use targets to fine tune. Use `rg` for fast grepping.

## Porting Structure

Math and clarity are top priority. Home subjects naturally. Refactor existing modules if necessary. Dedup real math content. `port_advise` and `port_plan` before porting; `dedup` and `move_dead` afterwards. No random tokens in names. Write a topic file math is substantial or multiple waves are anticipated. Manager must do defs and refactor. Write a workorder whe using a subagent to port proof bodies: clearly scope the work with instructions on build discipline and early feedback for blockers. Don't poll the subagent.

## Build Discipline

No tree build. Bound build time. Log output in `lean/tmp`. Address build time promptly (one can use a subagent but first review `porting-playbook.md` so you can give clear instructions). Fix warnings.

## Legacy Modules

When a legacy module is touched it needs to be brought up to standards, meaning: `spec_pin`, deletion from old checker, silent build, no build time blow up, no random tokens in names, `dedup.py`, `move_dead.py`.