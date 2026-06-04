---
alwaysApply: false
---
# Project Structure

```
src/
  app/              # Applications (cli, build, mcp, mcp_jj, io, test_runner_new, desugar)
  lib/              # Standard library — `use std.X` resolves here
    common/         # Pure functions (text, math, json, crypto, encoding, ui model/layout/style)
    nogc_sync_mut/  # Sync mutable (ffi, fs, net, http, database, mcp, spec, ui session/theme I/O)
    nogc_async_mut/ # Async mutable (actors, async, threads, generators)
    gc_async_mut/   # GC + async (gpu, cuda, torch, ML)
    nogc_async_mut_noalloc/  # Baremetal, execution, memory, qemu
  runtime/          # Native runtime and support libraries
  compiler/         # Unified compiler — numbered layers (00-99)
  i18n/             # Internationalization
test/               # Test files
doc/                # Documentation — each phase organized by feature domain
  01_research/<domain>/<topic>/  # Research by feature domain, grouped by topic
  02_requirements/<domain>/<topic>/ # Requirements by domain/topic (+nfr/, +feature/ auto-gen)
  03_plan/<domain>/<topic>/     # Plans by domain/topic
  04_architecture/<domain>/<topic>/ # Architecture by domain/topic (+adr/, +format/, +rule/)
  05_design/<domain>/<topic>/   # Design by domain/topic
  06_spec/                # Specs — generated from sspec, mirrors test/ paths (DO NOT refactor)
  07_guide/<domain>/<topic>/    # Guides by domain/topic (+quick_reference/)
  08_tracking/            # Bugs, tests, todos — auto-generated (DO NOT refactor)
  09_report/              # Reports — temporal (DO NOT refactor)
  10_metrics/             # Metrics — auto-generated (DO NOT refactor)
  11_archive/             # Archived docs (DO NOT refactor)
  # Domains: language, compiler, lib, app, os, hardware, platform, runtime, ui, ml, infra
  # Topics: semantic grouping within domain (e.g., type_system/, parser/, networking/)
  # Rule: ≤10 files per directory; max depth 4 (doc/phase/domain/topic)
bin/                # Binaries (bin/simple → release/<triple>/simple symlink)
.claude/            # Agents, skills, templates, rules
```

- **Import namespace:** `use std.X` preferred (resolves from `src/lib/`)
- **FILE.md manifests:** Each directory can have a `FILE.md` declaring allowed entries.
  Root FILE.md links to child manifests via `## Child Manifests`. Enforced by
  `scripts/check-workspace-root-guard.shs` (lint + pre-commit hook).
  See `doc/07_guide/workspace/file_manifest.md`.
- **Detailed:** `doc/04_architecture/compiler/file_class_structure.md` (2,649 files, 623K lines)
- **Glossary:** `doc/glossary.md`

## Auto-Generated Docs
| What | Where | When |
|------|-------|------|
| Features | `doc/02_requirements/feature/feature.md` | Every test run |
| Pending features | `doc/02_requirements/feature/pending_feature.md` | Every test run |
| Test results | `doc/08_tracking/test/test_result.md` | Every test run |
| Test DB | `doc/08_tracking/test/test_db.sdn` | Every test run |
| TODOs | `doc/TODO.md` | `bin/simple todo-scan` |
| Todo DB | `doc/08_tracking/todo/todo_db.sdn` | `bin/simple todo-scan` |
