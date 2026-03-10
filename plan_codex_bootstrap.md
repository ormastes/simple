# Codex Bootstrap Plan

Updated: 2026-03-10

## Goal

Make bootstrap work in three explicit levels across the target host matrix:

1. Rust-base Simple
2. Pure Simple with LLVM backend via `llvm-lib`
3. Full pure Simple self-host

Execution priority:

1. Linux native
2. FreeBSD in QEMU from Linux host
3. macOS prepared
4. Windows prepared for both MinGW and MSVC

This document is now the root execution plan. Historical notes remain in `doc/build/` and platform-specific docs.

## Required Outcome Matrix

| Platform | Stage 1 Rust-base Simple | Stage 2 Pure Simple `llvm-lib` | Stage 3 Full pure Simple | Mode |
|----------|--------------------------|--------------------------------|--------------------------|------|
| Linux x86_64 | Do now | Do now | Do now | Native host |
| FreeBSD x86_64 | Do now | Do now | Do now | QEMU guest from Linux |
| macOS arm64/x86_64 | Prepare now | Prepare now | Prepare now | Native CI/host later |
| Windows x86_64 MinGW | Prepare now | Prepare now | Prepare now | Native or cross later |
| Windows x86_64 MSVC | Prepare now | Prepare now | Prepare now | Native CI/host later |

Definition of done per stage:

- Stage 1: Rust seed produces a working Simple CLI binary from `src/app/cli/main.spl`.
- Stage 2: Stage 1 binary can compile with `--backend llvm-lib` and produce a working Simple binary.
- Stage 3: Stage 2 binary rebuilds the full CLI again with matching behavior and reproducible hash policy.

## Canonical Commands

### Stage 1: Rust-base Simple

```bash
cargo build --profile bootstrap -p simple-driver

src/compiler_rust/target/bootstrap/simple \
  native-build \
  --source src/compiler \
  --source src/lib \
  --source src/app \
  --entry src/app/cli/main.spl \
  -o build/bootstrap/stage1/simple \
  --strip
```

### Stage 2: Pure Simple via `llvm-lib`

```bash
build/bootstrap/stage1/simple \
  native-build \
  --source src/compiler \
  --source src/lib \
  --source src/app \
  --entry src/app/cli/main.spl \
  --backend llvm-lib \
  -o build/bootstrap/stage2/simple \
  --strip
```

### Stage 3: Full pure Simple self-host

```bash
build/bootstrap/stage2/simple \
  native-build \
  --source src/compiler \
  --source src/lib \
  --source src/app \
  --entry src/app/cli/main.spl \
  --backend llvm-lib \
  --clean \
  -o build/bootstrap/stage3/simple \
  --strip
```

### Minimum smoke suite after each successful stage

```bash
<binary> --version
<binary> --help
<binary> compile examples/01_getting_started/hello_native.spl -o /tmp/simple_hello
/tmp/simple_hello
```

Additional Stage 2/3 checks:

```bash
<binary> compile examples/01_getting_started/hello_native.spl --format=smf -o /tmp/simple_hello.smf
<binary> /tmp/simple_hello.smf
sha256sum build/bootstrap/stage2/simple build/bootstrap/stage3/simple
```

## Current Reality

### Known good base

- Linux bootstrap scripts exist:
  - `scripts/bootstrap/bootstrap-from-scratch.sh`
- FreeBSD QEMU wrapper exists:
  - `scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh`
- Windows bootstrap entry exists:
  - `scripts/bootstrap/bootstrap-from-scratch.bat`
- `llvm-lib` backend exists in-tree:
  - `src/compiler/70.backend/backend/llvm_lib_backend.spl`
- Windows linker support exists in-tree for both MinGW-style and MSVC-style flows:
  - `src/compiler/80.driver/build/cross_compile.spl`
  - `src/compiler/70.backend/linker/msvc.spl`

### Current blockers already observed

- Rust-seeded binaries can reach full CLI startup but still miss runtime symbols in pure-Simple compile/interpreter paths.
- `llvm-lib` is the required backend for pure-Simple stages, but runtime completeness is not yet proven for Stage 2.
- Existing `bin/simple` and `bin/release/simple` behavior is not a reliable cross-platform proof point because artifacts may be host-specific.

## Execution Plan

## Phase A: Linux first

Objective: make the entire 1 -> 2 -> 3 chain work on Linux before expanding.

Tasks:

1. Re-run Stage 1 from Rust seed using the explicit full CLI entry.
2. Verify Stage 1 contains the driver/runtime symbols needed by:
   - `compile`
   - interpreter execution
   - SMF loading
3. Fix missing symbol/runtime registration problems until Stage 2 succeeds with `--backend llvm-lib`.
4. Use Stage 2 to rebuild Stage 3 with the same backend and compare hashes.
5. Promote the verified Linux artifact into the canonical release/bootstrap path.

Linux success criteria:

- `build/bootstrap/stage1/simple` works.
- `build/bootstrap/stage2/simple` builds from Stage 1 with `llvm-lib`.
- `build/bootstrap/stage3/simple` builds from Stage 2 with `llvm-lib`.
- Stage 2 and Stage 3 pass `--help`, `--version`, native compile/run, and SMF compile/run.
- Stage 2 and Stage 3 hashes are identical or any mismatch is explained and documented with a reproducibility bug.

## Phase B: FreeBSD via QEMU from Linux host

Objective: prove the same chain on FreeBSD without requiring a physical FreeBSD machine.

Execution path:

```bash
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --deploy
```

Tasks:

1. Standardize the FreeBSD guest image and SSH assumptions used by the wrapper.
2. Make the wrapper run the same staged commands as Linux, but inside the guest.
3. Copy out stage artifacts and logs to the host workspace after each major step.
4. Run the same smoke suite in the FreeBSD guest.
5. Record the FreeBSD artifact naming and deployment path.

FreeBSD success criteria:

- Stage 1 Rust-base Simple works in guest.
- Stage 2 `llvm-lib` build works in guest.
- Stage 3 full pure-Simple rebuild works in guest.
- Guest-produced binary passes smoke checks on FreeBSD.
- Host retrieves final artifact and logs cleanly.

Notes:

- FreeBSD is an execution target, not just a cross-link target.
- QEMU wrapper is the canonical path for now; no separate manual VM recipe should be treated as primary.

## Phase C: Prepare macOS

Objective: remove ambiguity so a macOS host or CI runner can execute the same three-stage chain when scheduled.

Preparation tasks:

1. Define artifact paths for:
   - `macos-arm64`
   - `macos-x86_64`
2. Confirm Stage 1 invocation is identical apart from host toolchain assumptions.
3. Confirm `llvm-lib` link path expectations on macOS:
   - clang/LLVM presence
   - ld64/lld usage
   - dynamic library search rules
4. Document required environment variables for runtime execution.
5. Add explicit smoke commands and expected output contract.

Prepared means:

- Commands are documented and consistent.
- Required host tools are listed.
- Known blockers are reduced to code/runtime issues, not process ambiguity.

## Phase D: Prepare Windows MinGW and MSVC

Objective: define two supported Windows bootstrap lanes without mixing their linker/runtime assumptions.

### Windows MinGW lane

Tasks:

1. Keep bootstrap entry at `scripts/bootstrap/bootstrap-from-scratch.bat`.
2. Treat MinGW as the GNU/PE path for early Windows bring-up.
3. Align Stage 2/3 `llvm-lib` expectations with MinGW import libraries and executable naming.
4. Document required tools:
   - MSYS2/MinGW-w64
   - LLVM/LLD if used by `llvm-lib`
5. Define smoke commands for `simple.exe`.

### Windows MSVC lane

Tasks:

1. Use existing linker support in `src/compiler/70.backend/linker/msvc.spl`.
2. Document environment discovery assumptions:
   - `link.exe`
   - `lld-link.exe`
   - Visual Studio toolchain paths
3. Keep MSVC separate from MinGW in both docs and artifact naming.
4. Define the same Stage 1/2/3 commands, with Windows path and linker expectations clarified.

Prepared means:

- MinGW and MSVC are described as separate targets.
- Toolchain detection/linker policy is explicit.
- The repo has a single Windows bootstrap plan instead of mixed notes.

## Deliverables

### Immediate deliverable

- This root plan becomes the canonical bootstrap tracker.

### Next implementation deliverables

1. Linux stage logs and verified artifact paths.
2. FreeBSD QEMU stage logs and verified artifact paths.
3. macOS preparation doc updates in `doc/build/`.
4. Windows preparation doc updates for MinGW and MSVC in `doc/build/`.

## Concrete work order

1. Stabilize Linux Stage 1 runtime completeness.
2. Get Linux Stage 2 `llvm-lib` working.
3. Get Linux Stage 3 reproducible.
4. Port the same exact staged flow into FreeBSD QEMU wrapper execution.
5. Once Linux and FreeBSD are green, update `doc/build/bootstrap_multi_platform.md`.
6. Then split Windows documentation into explicit MinGW and MSVC lanes.
7. Then add macOS host execution notes.

## Non-goals for this pass

- No claim yet that macOS or Windows are working end-to-end.
- No release packaging changes until Linux and FreeBSD Stage 3 are proven.
- No new bootstrap variant beyond the three required levels.

## Progress tracker

| Item | Status |
|------|--------|
| Root plan rewritten around 3-stage matrix | Done |
| Linux Stage 1 runtime completeness | Pending |
| Linux Stage 2 `llvm-lib` | Pending |
| Linux Stage 3 reproducibility | Pending |
| FreeBSD QEMU Stage 1-3 | Pending |
| macOS preparation | Pending |
| Windows MinGW preparation | Pending |
| Windows MSVC preparation | Pending |
