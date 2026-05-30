# Doc Refactor Plan — 2026-05-30

## Scope
Professionally reorganize `doc/` and doc wiki. Move files to proper locations,
merge/split as needed, fix generated-file source paths (not the generated files).

## Phase 1: Fold orphan dirs into numbered scheme
| Source | Target | Files | Action |
|--------|--------|-------|--------|
| `doc/plan/` | `doc/03_plan/security/` | 2 | Move, update ~3 refs |
| `doc/test/` | DELETE (stale dup of `doc/08_tracking/test/`) | 4 | Reconcile live 4.7MB vs stale 1.2KB test_result.md first |
| `doc/todo/` | `doc/08_tracking/todo/` | 2 | Move DB files, update todo-scan path |
| `doc/09_bugs/` | `doc/08_tracking/bug/` | 8 | Move, update ~10 refs |

## Phase 2: Reorganize `doc/09_report/misc/` (355 .md files)
Create subdirectories and move by classification:

| Category | Count | Target |
|----------|-------|--------|
| compiler | 60 | `doc/09_report/misc/compiler/` |
| test | 51 | `doc/09_report/misc/test/` |
| session | 49 | `doc/11_archive/session/` (archive) |
| migration | 43 | `doc/11_archive/migration/` (archive) |
| ui | 30 | `doc/09_report/misc/ui/` |
| stdlib | 28 | `doc/09_report/misc/stdlib/` |
| lang | 27 | `doc/09_report/misc/lang/` |
| runtime | 23 | `doc/09_report/misc/runtime/` |
| platform | 19 | `doc/09_report/misc/platform/` |
| archive | 15 | `doc/11_archive/reports/` |
| bootstrap | 11 | `doc/09_report/misc/bootstrap/` |

Session snapshots (49) and migration reports (43) → `doc/11_archive/`
because they're historical status, not ongoing reference.

## Phase 3: Merge duplicates + split oversized
- Reconcile `doc/test/test_result.md` (4.7MB) with `doc/08_tracking/test/test_result.md` (1.2KB)
- Check for content-duplicate reports within misc/ categories (e.g. BOOTSTRAP_* variants)

## Phase 4: Fix generators + update indexes
- Fix `structure.md` auto-generated docs table (feature.md path wrong)
- Remove `recent_build.md` from structure.md (doesn't exist, no generator)
- Update `config/sdoctest.sdn` legacy path exclusions
- Update `dashboard_collectors.spl` `doc/test` → `doc/08_tracking/test/`
- Add READMEs to new subdirectories

## Constraints
- Generated files: change the generator source, not the file
- Commit each phase before starting the next
- Reference graph: update all referrers in same commit as moves
- No dedup across pipeline stages (01→02→05→06→09 is intentional)
- `doc/08_tracking/`, `doc/02_requirements/`, `doc/06_spec/` stay in place (high-breakage paths)
