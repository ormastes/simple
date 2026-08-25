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
- Registry `status` is hand-audited until three Simple features land (tracked
  in simply `doc/plan/design.md`): future-impl SSpec tests, `simple test
  --json` export, and runner-emitted feature grouping/done-%. Once available,
  the daily job flips statuses from real SSpec results.
