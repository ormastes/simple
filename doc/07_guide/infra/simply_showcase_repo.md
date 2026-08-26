# simply showcase repo (ormastes/simply)

Created 2026-08-25. `simply` is the whole-earth-software showcase and
capability-registry repo — Wave 0 of
`doc/01_research/domain/whole_world_software_implementation_map_2026-08-25.md`.

- Repo: https://github.com/ormastes/simply
- Site: https://ormastes.github.io/simply/ (GitHub Pages, main branch `/docs`)

## What lives there

| Path | Content |
|---|---|
| `data/registry.sdn` | 69 capability rows (I01–I38 infra, A01–A31 domains): `id\|group\|name\|F\|U\|P\|done\|status\|sspec` |
| `scripts/update_site.sh` | POSIX generator: registry → glass dashboard; daily CI cron |
| `docs/` | Generated site; `glass.css` mirrors SimpleOS glass tokens (`src/lib/common/ui/glass/`) — keep the two in sync |
| `examples/` | The example corpus, copied from this repo's `examples/` |
| `doc/plan/` | Implementation map + repo design |

## Rules for this (simple) repo

- **Never vendor simply here.** `.gitignore` blocks `examples/simply/` and
  `simply/`; simply's generator fails on any nested `.git` — the two guards
  together prevent recursive checkouts.
- **`examples/` here is frozen.** New example work goes to ormastes/simply.
  Deleting the 2,613 files here is deferred until a deliberate
  `--expect-files` landing through the tree-size push guards.
## Producing the dashboard data (native, 2026-08-26)

```bash
bin/simple test --json test/01_unit | grep '^{' | tail -1 > <simply>/data/test_results.json
sh <simply>/scripts/update_site.sh    # renders the test panel + registry
```

The JSON (`spec.total_passed/failed/skipped/pending`, `spec.groups[]` with
`done_pct`, per-file rows) is emitted by all three `test` lanes: the main
runner (`test_runner_main.spl`, directory sweeps), the light-daemon client
(`test_runner_client.spl`, explicit files — rows come from real `SPEC FILE
VERDICT` lines, matched by basename because spipe rewrites specs to
`.spipe_matchers_*` temp names), and the Rust repair-only runner. `planned()`
specs count as pending, never failed.

Completion criteria and per-row test lists live in simply
(`doc/plan/completion_criteria.md`, `data/tests.sdn`); statuses are earned
from test evidence, not hand-edited.

**Host hazard seen 2026-08-26:** a deployed seed built inside another worktree
resolves `src/lib` from that tree (baked `CARGO_MANIFEST_DIR`; the precedence
fix of 2026-08-21 only helps binaries built after it). Symptom: stdlib edits
have no effect, `--json` prints the old shape. Check with
`strace -e openat bin/simple run x.spl | grep worktrees/`, and redeploy a seed
built from origin/main. See
`doc/08_tracking/bug/deployed_seed_resolves_stdlib_from_foreign_worktree_2026-08-20.md`.
