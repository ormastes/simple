---
paths:
  - "src/compiler_rust/**"
  - "scripts/bootstrap/**"
  - "build/bootstrap/**"
alwaysApply: false
---
# Bootstrap & Binary Architecture

| Binary | Path | Role |
|--------|------|------|
| **Real binary** | `bin/release/simple` (`.exe` on Windows) | Self-hosted production compiler |
| **Platform binaries** | `bin/release/<triple>/simple` | Per-platform release |
| **Rust seed** | `src/compiler_rust/target/bootstrap/simple` | Bootstrap-only seed |

- **NEVER copy Rust bootstrap binary to `bin/release/simple`** — that's the self-hosted binary
- **Bootstrap entry points**: `src/app/cli/main.spl` (full CLI), `src/app/cli/bootstrap_main.spl` (minimal)
- **`bin/release/simple` is fully self-sufficient** — in-process compilation, no subprocess calls
- External tool calls: `clang`/`clang++`/`cl.exe`, `gcc`, `mold`/`lld`/`link.exe`, `llc`, `uname`/`cmd`, `which`/`where`

## Bootstrap Commands
```bash
# Full bootstrap (recommended):
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
# WARNING: --deploy replaces bin/release/<triple>/simple with the STAGE4 CLI
# without any smoke gate. Verified broken 2026-06-11 (lint coredumps, test
# silent no-op, -c exit 1). After --deploy, ALWAYS smoke-test:
#   setsid timeout 30 bin/simple -c "print(1+1)"   # expect 2
#   bin/simple lint <any .spl>                      # must not core dump
# If broken, restore the working seed:
#   cp src/compiler_rust/target/release/simple bin/release/<triple>/simple.new \
#     && mv bin/release/<triple>/simple.new bin/release/<triple>/simple
# Windows:
scripts/bootstrap/bootstrap-windows.sh --deploy
# Manual stages:
cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry src/app/cli/bootstrap_main.spl -o build/bootstrap/stage2/<triple>/simple
```

See `.claude/memory/ref_architecture.md` for detailed architecture.
