# SET W0 — the factoring scout (no Lean edits)

**Status: stopped without a manifest.** First set of the
[WeightOne rectification](TOPIC-weightone-rectify.md). It authorized **zero** Lean edits;
its deliverable was to be
`TOPIC-weightone-factoring-scout.md`. The scout ran long without producing the file and was
stopped, so **no scout manifest exists**. The closure work it was to do is instead done
per home by SET-W1's executor with the tool added for the purpose
(`tools/deps/port_graph.py --closure MODULE "name1,name2,..."`), which reports the same-file
declarations a block reaches, with spans. This set is kept in the record only so the
schedule reads in order.

## The brief given

Read [TOPIC-weightone-rectify.md](TOPIC-weightone-rectify.md) §0–§2 and
[porting-playbook.md](../../porting-playbook.md) §7.1, §8, §9, then:

1. Reconcile the two redundancy views — `tools/deps/port_graph.py --blocks` (module-level)
   and the statement-level grouping (identical normalized statements across files, which
   finds 245 duplicate declarations in 36 exact-file-set groups).
2. Propose the home modules (paths + subject), the exact declaration list per home, the
   canonical copy to lift, and each home's **dependency closure**.
3. Identify the near-duplicates that need generalisation rather than lifting, the
   adapter/trivia that must stay `private`, and the risk list.

## Why this exists

The route-C′ port transcribed FLT `S_` files package-by-package, so the same private
prelude was re-proved in each consumer. `TOPIC-weightone-rectify.md` §0 measures it at
**7,242 removable lines** across 12 modules. Before any code moves, the homes must be
settled, because a home's closure is what decides whether it can be lifted at all — a
lifted block that references a consumer-private helper is not liftable, and a block whose
closure drags another block means the two homes must merge.

## What the scout found

Nothing — it was stopped before writing. SET-W1's executor computes each home's closure with
`python3 tools/deps/port_graph.py --closure <module> "<names>"` (a command added to the tool
for this effort) before creating the home.

## Definition of done

- The scout file exists and contains: home paths, per-home declaration lists, closures,
  near-duplicate/generalisation list, adapter list, risk list, rebuild-order note.
- No `.lean` file changed, no commit.
