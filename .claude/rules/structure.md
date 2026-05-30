---
alwaysApply: false
---
# Project Structure

```
src/
  app/              # Applications (cli, build, mcp, mcp_jj, io, test_runner_new, desugar)
  lib/              # Standard library — `use std.X` resolves here
    common/         # Pure functions (text, math, json, crypto, encoding)
    nogc_sync_mut/  # Sync mutable (ffi, fs, net, http, database, mcp, spec)
    nogc_async_mut/ # Async mutable (actors, async, threads, generators)
    gc_async_mut/   # GC + async (gpu, cuda, torch, ML)
    nogc_async_mut_noalloc/  # Baremetal, execution, memory, qemu
  runtime/          # Native runtime and support libraries
  compiler/         # Unified compiler — numbered layers (00-99)
  i18n/             # Internationalization
test/               # Test files
doc/                # Documentation (01_research through 10_metrics)
bin/                # Binaries (bin/simple → release/<triple>/simple symlink)
.claude/            # Agents, skills, templates, rules
```

- **Import namespace:** `use std.X` preferred (resolves from `src/lib/`)
- **Detailed:** `doc/04_architecture/file_class_structure.md` (2,649 files, 623K lines)
- **Glossary:** `doc/04_architecture/glossary.md`

## Auto-Generated Docs
| What | Where | When |
|------|-------|------|
| Features | `doc/06_spec/generated/feature.md` | Every test run |
| Test results | `doc/08_tracking/test/test_result.md` | Every test run |
| Build status | `doc/08_tracking/build/recent_build.md` | Every build |
| TODOs | `doc/TODO.md` | `bin/simple todo-scan` |
