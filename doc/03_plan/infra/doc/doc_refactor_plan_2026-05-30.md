# Doc Refactor Plan — 2026-05-30

**Status: COMPLETED**

## Scope
Professionally reorganize `doc/` and doc wiki. Move files to proper locations,
merge/split as needed, fix generated-file source paths (not the generated files).

## Phase 1: Fold orphan dirs into numbered scheme ✓
| Source | Target | Files | Status |
|--------|--------|-------|--------|
| `doc/plan/` | `doc/03_plan/security/` | 2 | Done |
| `doc/test/` | symlink → `doc/08_tracking/test/` | 4 | Done (live 4.8MB reconciled) |
| `doc/todo/` | `doc/08_tracking/todo/` | 2 | Done |
| `doc/09_bugs/` | `doc/08_tracking/bug/` | 8 | Done (15 refs updated) |

## Phase 2: Reorganize `doc/09_report/misc/` (793 files) ✓

| Category | Count | Target | Status |
|----------|-------|--------|--------|
| compiler | 60 | `doc/09_report/misc/compiler/` | Done |
| test | 51 | `doc/09_report/misc/test/` | Done |
| session | 49 | `doc/11_archive/session/` | Done (archived) |
| migration | 43 | `doc/09_report/misc/migration/` | Done |
| ui | 30 | `doc/09_report/misc/ui/` | Done |
| stdlib | 27 | `doc/09_report/misc/stdlib/` | Done |
| lang | 27 | `doc/09_report/misc/lang/` | Done |
| runtime | 23 | `doc/09_report/misc/runtime/` | Done |
| platform | 19 | `doc/09_report/misc/platform/` | Done |
| archive | 15 | `doc/11_archive/reports/` | Done (archived) |
| bootstrap | 11 | `doc/09_report/misc/bootstrap/` | Done |
| t32_cmm_validation | 438 | `doc/09_report/misc/t32_cmm_validation/` | Done (.txt files) |

## Phase 3: Merge duplicates + split oversized ✓
- test_result.md reconciled via symlink (Rust seed writes to `doc/test/`)
- Within-category "duplicates" are different-phase reports, not content dupes

## Phase 4: Fix generators + update indexes ✓
- Fixed `structure.md` auto-generated docs table (feature.md path corrected)
- Removed nonexistent `recent_build.md` from structure.md
- Updated `config/sdoctest.sdn` legacy path exclusions to numbered scheme
- Updated `config/traceability.sdn` legacy paths to numbered scheme

## Reference notes
- `doc/test/` is a symlink to `doc/08_tracking/test/` — Rust seed writes here
- `doc/08_tracking/test/` is the canonical numbered-scheme location
- 389 "duplicate filenames" are intentional pipeline stages (01→02→05→06→09)
