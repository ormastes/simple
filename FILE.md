# Simple Language Compiler - Root Directory

**Version:** 0.6.1
**Purpose:** Top-level project organization and entry points
**Quick Start:** See [CLAUDE.md](CLAUDE.md) for development guide

---

## Quick Reference

| File/Directory | Purpose | When to Use |
|----------------|---------|-------------|
| **CLAUDE.md** | Development guide | Start here for development |
| **FILE.md** | Canonical structure definition | Check where files belong |
| **README.md** | Project overview | Learn what Simple is |
| **AGENTS.md** | Agent definitions | Using Task tool subagents |
| **.sstack/** | Session state tracking | Local workflow state and phase handoff notes |
| **bin/** | Executables & CLI | Running Simple commands |
| **src/** | Source code | Core implementation |
| **test/** | Test suites | Testing & verification |
| **examples/** | Example programs (submodules) | Learning Simple |
| **doc/** | Documentation (numbered 00-11 only) | Guides, specs, reports |
| **config/** | Project configuration | Runtime, packaging, theme, MCP, t32 |
| **scripts/** | Automation scripts | Build, test, bootstrap |
| **tools/** | Development tools | Electron, Tauri, MCP registry, TLS test |
| **build/** | Generated build artifacts | Compiled output (gitignored) |
| **tmp/** | Local transient cache | Runtime scratch (gitignored) |
| **target/** | Cargo/Rust build output | Rust compilation (gitignored) |
| **bootstrap/** | Bootstrap artifacts | Bootstrap stages (gitignored) |

---

## Root Files (Tracked)

| File | Purpose |
|------|---------|
| `CLAUDE.md` | Development guide and project instructions |
| `FILE.md` | This file — canonical structure definition |
| `README.md` | Project overview for GitHub |
| `AGENTS.md` | Agent definitions (symlink to CLAUDE.md) |
| `GEMINI.md` | Gemini instructions |
| `MCP.md` | MCP documentation |
| `CHANGELOG.md` | Version history |
| `VERSION` | Semantic version string |
| `LICENSE` | Apache 2.0 |
| `THIRD_PARTY_NOTICES.md` | Third-party attributions |
| `.gitignore` | Git ignore rules |
| `.jjignore` | Jujutsu ignore rules |
| `.gitmodules` | Submodule definitions |
| `.gitattributes` | Git attributes |
| `.envrc` | direnv configuration |
| `.mcp.json` | MCP server definitions |
| `.jscpd.json` | Copy-paste detector config |
| `.dockerignore` | Docker build excludes |

**No other files at root.** Temp files, build artifacts, compiler intermediates,
and test outputs must go to `build/`, `tmp/`, or `target/`.

---

## src/ (Source Code)

All code in `.spl` (Simple) or `.shs` (shell) files.

| Path | Purpose |
|------|---------|
| `src/app/` | Applications (cli, build, mcp, dashboard, test_runner, desugar, io) |
| `src/compiler/` | Self-hosted compiler — numbered layers 00-99 |
| `src/compiler_rust/` | Rust seed bootstrap compiler (vendor/ is third-party) |
| `src/lib/` | Standard library — `use std.X` resolves here |
| `src/std/` | Symlink to `src/lib/` |
| `src/os/` | SimpleOS (kernel, drivers, desktop, apps, compositor, crypto, game, gui) |
| `src/runtime/` | Native C runtime (vendor/ is third-party) |
| `src/i18n/` | Internationalization |
| `src/tooling/` | Build and dev tooling |
| `src/type/` | Named primitive type facade modules |
| `src/unit/` | Unit/measurement types |
| `src/verification/` | Formal verification (Lean4 models and proofs) |

### src/lib/ (Standard Library Tiers)

| Tier | Path | Description |
|------|------|-------------|
| Pure | `common/` | Pure functions (text, math, json, crypto, encoding) |
| Sync | `nogc_sync_mut/` | Sync mutable (ffi, fs, net, http, database, mcp, spec) |
| Sync Immutable | `nogc_sync_immut/` | Sync immutable data |
| Async | `nogc_async_mut/` | Async mutable (actors, async, threads, generators) |
| Async Immutable | `nogc_async_immut/` | Async immutable data |
| GC Async | `gc_async_mut/` | GC + async (gpu, cuda, torch, ML) |
| GC Sync | `gc_sync_mut/`, `gc_sync_immut/` | GC sync tiers |
| Baremetal | `nogc_async_mut_noalloc/` | Baremetal, execution, memory, qemu |
| Browser | `blink/`, `cc/`, `content/`, `skia/`, `viz/`, `web/`, `js/` | Chromium-mirrored browser engine |
| Domain | `crypto/`, `encoding/`, `editor/`, `gui/`, `hardware/`, `log/`, `lint/`, `sdn/`, `sffi/`, `scipy/`, `scv/`, `lib/` | Domain-specific libraries |

---

## doc/ (Documentation — Numbered Only)

**All doc subdirectories must be numbered.** No unnumbered directories allowed.

| Path | Purpose |
|------|---------|
| `doc/00_llm_process/` | LLM-assisted development process |
| `doc/01_research/` | Research notes |
| `doc/02_requirements/` | Requirements and feature definitions |
| `doc/03_plan/` | Plans (including agent_tasks/) |
| `doc/04_architecture/` | Architecture docs (file_class_structure.md, glossary.md) |
| `doc/05_design/` | Design documents |
| `doc/06_spec/` | Specifications, generated features, screenshot images |
| `doc/07_guide/` | Guides, tutorials, quick references |
| `doc/08_tracking/` | Tracking: bug/, test/, todo/, build/, perf/, baselines/, lint/ |
| `doc/09_report/` | Reports |
| `doc/10_metrics/` | Metrics and dashboards |
| `doc/11_archive/` | Archived docs |

### Correct Locations for Common Content

| Content | Correct Location | NOT |
|---------|-----------------|-----|
| Bug reports | `doc/08_tracking/bug/` | ~~doc/bugs/~~ |
| Plans | `doc/03_plan/` | ~~doc/plans/~~ |
| Test results/DB | `doc/08_tracking/test/` | ~~doc/test/~~ |
| TODO database | `doc/08_tracking/todo/` | ~~doc/todo/~~ |
| Spec images | `doc/06_spec/image/` | ~~doc/spec/~~ |
| Build status | `doc/08_tracking/build/` | |
| Feature DB | `doc/06_spec/` or `doc/02_requirements/feature/` | |
| Guides | `doc/07_guide/` | ~~doc/guide/~~ |
| Architecture | `doc/04_architecture/` | ~~doc/architecture/~~ |

### Auto-Generated Docs

| What | Where | When |
|------|-------|------|
| Features | `doc/06_spec/generated/feature.md` | Every test run |
| Test results | `doc/08_tracking/test/test_result.md` | Every test run |
| Build status | `doc/08_tracking/build/recent_build.md` | Every build |
| TODOs | `doc/TODO.md` | `bin/simple todo-scan` |

---

## test/ (Test Suites)

Tests named `*_spec.spl`. Structure mirrors src/ plus topic-based groupings.

| Path | Purpose |
|------|---------|
| `test/app/` | App tests |
| `test/app_complete/` | Extended app tests |
| `test/app_extended/` | More app tests |
| `test/compiler/` | Compiler tests |
| `test/compiler_complete/` | Extended compiler tests |
| `test/compiler_deep/` | Deep compiler tests |
| `test/core_complete/` | Core complete tests |
| `test/core_integration/` | Core integration tests |
| `test/core_system/` | Core system tests |
| `test/browser_engine/` | Browser engine tests |
| `test/bug/` | Bug regression tests |
| `test/cli/` | CLI tests |
| `test/code_quality/` | Quality checks |
| `test/fixtures/data/` | Data fixtures |
| `test/baselines/` | Baseline snapshots |

**Run tests:** `bin/simple test` or `bin/simple test path/to/spec.spl`

---

## config/

| Path | Purpose |
|------|---------|
| `config/mcp/` | MCP startup and installation helpers |
| `config/packaging/` | Package specs (Debian, Homebrew, RPM, Windows) |
| `config/resources/` | Runtime resources |
| `config/t32/` | TRACE32 container and target configuration |
| `config/themes/` | UI theme definitions |

---

## tools/

| Path | Purpose |
|------|---------|
| `tools/electron-shell/` | Electron desktop shell |
| `tools/tauri-shell/` | Tauri desktop shell |
| `tools/mcp-registry/` | MCP server registry and native builds |
| `tools/tls_test_server/` | TLS test certificate server |

---

## scripts/

| Path | Purpose |
|------|---------|
| `scripts/check-workspace-root-guard.shs` | Workspace root and immediate-child write guard |
| `scripts/bootstrap/` | Bootstrap scripts (3 allowed shell scripts) |
| `scripts/audit/` | Code auditing scripts |
| `scripts/hooks/` | Shared local VCS hook wrappers (Git hook names may omit extension) |

All scripts in `.spl` or `.shs` format except 3 bootstrap scripts and
extensionless VCS hook entrypoints under `scripts/hooks/`.

---

## .claude/ (Claude Code Integration)

| Path | Purpose |
|------|---------|
| `.claude/agents/` | Agent definitions (code, test, debug, explore, docs, vcs, infra, build, ml) |
| `.claude/skills/` | Skills (/sstack, /dev, /coding, /test, /debug, etc.) |
| `.claude/templates/` | Code templates |
| `.claude/rules/` | Project rules (language, testing, bootstrap, commands, structure, code-style, vcs) |
| `.claude/memory/` | Persistent memory (auto-managed) |

---

## Vendor / Third-Party (Excluded from Code Counts)

- `src/compiler_rust/vendor/**`
- `src/runtime/vendor/**`
- `src/runtime/miniaudio.h`
- `src/runtime/stb_image.h`
- `src/runtime/stb_truetype.h`

---

## File Naming Conventions

| Extension | Purpose |
|-----------|---------|
| `.spl` | Simple source code |
| `.shs` | Simple shell script |
| `.smf` | Simple module format (compiled, gitignored) |
| `.sdn` | Simple Data Notation (config/data) |
| `.md` | Markdown documentation |

---

## Version Control

Use **jj** (Jujutsu), NOT git. Work directly on `main`, never create branches.

```bash
jj status                              # See changes
jj commit -m "message"                 # Commit
jj bookmark set main -r @-             # Set bookmark
jj git push --bookmark main            # Push
jj git fetch && jj rebase -d main@origin  # Pull
```

---

**Last Updated:** 2026-05-19
**Maintained By:** Simple Language Team
