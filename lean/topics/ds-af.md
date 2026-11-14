Let's continue porting AF modules in the DS cone following [general instructions]((instructions.md).
Scope the next ready set per TOPIC-scoping-a-ds-set.md, --include-leaves.
You should do the ground work. Have agents port the proof bodies.
For new modules, it works well to write the scaffolding with sorries in the bodies yourself and let agent finish the porting.
You can write a topic file for planning, but leave workorders in lean/tmp/
No silencing linters. Have agents report problems early but no busy work. Wait on agents output.
No tokens in names.
As there is no tree build occasionally builds will take time and even run into minor problems.
This is to be expected and you should just fix what is broken.
