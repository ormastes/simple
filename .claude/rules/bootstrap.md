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

## Incremental: Rebuild Only Pure-Simple
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
  - `dynload` (default): reuse `build/bootstrap/native_cache` unless compiler/AOP/loader
    inputs changed; native-build emits native plus SMF cache where supported.
  - `one-binary`: clear native cache and build the monolithic native executable.
- Dependency tracing intentionally over-invalidates around AOP/MDSOC weaving,
  loader ABI, interpreter adapters, execution mode, library path, and
  native-build environment knobs. Do not narrow this to import edges until the
  AOP and loader contracts expose stable cache keys.
- Direct Rust seed execution prints a `WARNING`; suppress it only for bootstrap
  automation (`SIMPLE_BOOTSTRAP=1`), explicit seed maintenance
  (`SIMPLE_RUST_SEED_WARNING=0`), or an acknowledged seed command
  (`--seed-ok` / `--rust-seed-ok`).
- Every bootstrap route that reaches the full server-producing stage must build
  the fresh MCP/LSP pair with `SIMPLE_NO_STUB_FALLBACK=1` and run the exact
  `initialize` -> `notifications/initialized` -> `tools/list` handshake plus
  `simple_status` and `lsp_symbols` before deploy. Earlier stages run their
  native fixture sanity; the separate Stage 2 MCP system spec covers its single
  cached MCP artifact but does not substitute for the Stage 5 pair gate.
- The bootstrap wrapper itself runs the shared compiler sanity before using
  Stage 2 and before accepting Stage 3: exact bootstrap version, unsupported
  `run` rejection, and strict native build/execute of `p2_add.spl`.
- Multiplatform bootstrap CI uses Cranelift for stages 2–3 (LLVM stage-2 link blocked by 62 undefined symbols; see doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md). Uploads only the resulting pure-Simple Stage 2/Stage 3 binaries, never the Rust seed as a platform artifact.
- The Linux Stage 3 artifact owns the strict x86_64/AArch64/RISC-V LLVM
  execution gate through `check-llvm-simd-row-native-arch.shs`; Rust cross-build
  success alone is not pure-Simple architecture evidence.

## Bootstrap Commands
```bash
# Normal pure-Simple bootstrap:
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# Full Rust + pure-Simple bootstrap:
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy

# Windows:
scripts/bootstrap/bootstrap-windows.sh --deploy
# Manual full-bootstrap seed/runtime rebuild:
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap

# Internal stage replay after a full-bootstrap seed exists:
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry src/app/cli/bootstrap_main.spl -o build/bootstrap/stage2/<triple>/simple
```

## Redeploy #79 Key Findings (2026-07-11)

**Parse-Error Gate False Positives:** The phase-2 parse-error gate (checking
`par_had_error` flag) is structurally correct but currently false-positives on
speculative/fragment re-lex errors. Known open bug; fix in flight. Gate behavior
is sound for deployed binaries but may cause spurious bootstrap failures during
stage2 diagnosis.

**Driver Import Pattern:** `use lazy` dynload for the compiler driver was never
implemented. Bootstrap now imports `compiler.driver.driver` directly in
`bootstrap_main.spl`. If changing driver initialization, verify direct imports
still resolve.

**Native-Build Closure Discovery:** The native-build recursive dependency
tracer follows plain `use` imports but does NOT traverse `export use` shims.
Only direct imports trigger cascading closure collection. Plan closure manually
for re-exports if needed.

**Runtime Path Requirement:** `SIMPLE_RUNTIME_PATH` env var MUST point at the
seed target directory for hosted linking. The `--runtime-path` CLI flag alone
does not set it. Ensure the wrapper sets both when invoking native-build in
hosted mode (e.g., `SIMPLE_RUNTIME_PATH="$seed_target" bin/simple native-build`).

See `.claude/memory/ref_architecture.md` for detailed architecture.
