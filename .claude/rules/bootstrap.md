---
paths:
  - "src/compiler_rust/**"
  - "scripts/bootstrap/**"
  - "build/bootstrap/**"
alwaysApply: false
---
# Bootstrap & Binary Architecture

## Default tooling runs on pure-Simple, NOT the Rust seed
**Policy:** every tool — `test`, `lint`, `fmt`, `check`, `build`, `run`, `-c`,
the MCP/LSP servers, doc-coverage, etc. — must run on the **pure-Simple
self-hosted binary** (`bin/release/<triple>/simple`, built + deployed via
bootstrap). The Rust seed (`src/compiler_rust/target/bootstrap/simple`) is
**bootstrap-only** and must not be the day-to-day `bin/simple`.
- If the self-hosted binary has a **perf or robustness problem** (slow startup,
  high RSS, a crash, a wrong result), **fix it in pure-Simple** (`src/compiler`,
  `src/lib`, `src/app`) and re-deploy — do **not** fall back to the seed as the
  default. File a bug/feature request for anything that can't be fixed in place.
- Verify bug fixes with the **deployed pure-Simple test runner**, not the seed.
- Reverting `bin/simple` to the seed is an emergency stopgap only, never the
  resting state; record a bug when you do it.

| Binary | Path | Role |
|--------|------|------|
| **Real binary** | `bin/release/simple` (`.exe` on Windows) | Self-hosted production compiler — **default for all tools** |
| **Platform binaries** | `bin/release/<triple>/simple` | Per-platform release (this is what `bin/simple` should point at) |
| **Rust seed** | `src/compiler_rust/target/bootstrap/simple` | Bootstrap-only seed (NOT for day-to-day tooling) |

- **NEVER copy Rust bootstrap binary to `bin/release/simple`** — that's the self-hosted binary
- **Bootstrap entry points**: `src/app/cli/main.spl` (full CLI), `src/app/cli/bootstrap_main.spl` (minimal)
- **`bin/release/simple` is fully self-sufficient** — in-process compilation, no subprocess calls
- External tool calls: `clang`/`clang++`/`cl.exe`, `gcc`, `mold`/`lld`/`link.exe`, `llc`, `uname`/`cmd`, `which`/`where`

## Incremental: rebuild ONLY pure-Simple
Normal bootstrap is pure-Simple-only. It reuses the existing Rust seed/runtime
and does not run cargo, even when Rust source hashes changed:
```bash
scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload
```
- Reuses the existing `src/compiler_rust/target/bootstrap/simple` seed + runtime
  lib; **never runs cargo** unless `--full-bootstrap` is passed. Errors out if
  no seed exists yet.
- "If the Rust seed can build the changed pure-Simple" is enforced by Stage 2: the
  seed recompiles the changed `.spl`. If Stage 2 fails, the new pure-Simple needs
  a Rust feature the seed lacks — rerun with `--full-bootstrap`.
- Combine with `--deploy` to swap `bin/release/<triple>/simple` (same smoke gate).
- Pure-Simple build modes:
  - `dynload` (default): reuse `.simple/native_cache` unless compiler/AOP/loader
    inputs changed; native-build emits native plus SMF cache where supported.
  - `one-binary`: clear native cache and build the monolithic native executable.

## Bootstrap Commands
```bash
# Normal pure-Simple bootstrap:
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# Full Rust + pure-Simple bootstrap:
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy

# Windows:
scripts/bootstrap/bootstrap-windows.sh --deploy
# Manual stages:
cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry src/app/cli/bootstrap_main.spl -o build/bootstrap/stage2/<triple>/simple
```

See `.claude/memory/ref_architecture.md` for detailed architecture.
