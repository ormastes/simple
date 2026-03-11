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

---

## Codex Opinion

Codex ran the bootstrap pipeline and observed these failures firsthand (section "Current blockers already observed"):

1. **Runtime symbol gaps:** Rust-seeded binaries reach full CLI startup but miss runtime symbols when exercising pure-Simple compile/interpreter paths. Codex hit this during actual Stage 2 attempts.
2. **llvm-lib not proven:** `--backend llvm-lib` was passed but Stage 2 did not produce a working binary. Runtime completeness was not reached.
3. **Host-specific artifacts:** Existing `bin/release/simple` could not serve as cross-platform proof because it was built on a specific host.

Codex marked all three Linux stages as **Pending** based on observed failures and prescribed sequential stabilization: fix Stage 1 runtime symbols first, then prove Stage 2 llvm-lib, then verify Stage 3 reproducibility.

Revalidation on 2026-03-11 confirmed that several of the original blockers were real and have since been fixed, but the Linux chain is still not green by the root success criteria. The canonical Stage 2 command still segfaults before producing `build/bootstrap/stage2/simple`.

### Updated Codex assessment after checking Claude's fixes

Codex's current opinion is:

- Claude fixed multiple real blockers. In particular, the `--backend llvm-lib` bootstrap dispatch path is now genuinely being exercised.
- Those fixes were necessary, but they were not sufficient to make Linux bootstrap pass end-to-end.
- The active failure is no longer the earlier runtime-symbol/dispatch issue. It is now a self-hosted frontend failure in the Stage 2 compiler process.

Concrete evidence from the latest canonical Stage 2 re-run:

- Stage 1 builds and launches the pure-Simple Stage 2 path correctly.
- The parser reaches `parser_init()` and begins lexing `src/app/cli/main.spl`.
- Inside `src/compiler/10.frontend/core/lexer.spl`, imported token constants are collapsing to zero in the self-hosted binary.
- Direct probe output from the failing Stage 2 run shows:
  - `ident=0 error=0 newline=0 plus=0`
  - `lex_make_token kind=0 text=#`
  - `lex_make_token kind=0 text=+`
  - `parse_module_body i=0 kind=0 text=a`

So Codex no longer thinks the bootstrap is blocked by the same reasons it originally reported. Claude's fixes removed those earlier blockers. The current blocker is narrower:

- token constant import/evaluation in the self-hosted frontend
- likely centered on `src/compiler/10.frontend/core/lexer.spl` and/or `src/compiler/10.frontend/core/tokens.spl`

Practical conclusion:

- Claude was right that the architecture was not fundamentally broken.
- Codex is right that Linux Stage 2 is still failing in actual execution.
- Therefore Linux Stages 1-3 remain **Pending** until the token-constant collapse is fixed and the canonical Stage 2 command actually emits `build/bootstrap/stage2/simple`.

---

## Claude Opinion (2026-03-11 audit session)

### Assessment: Claude-fixed blockers were real, but bootstrap is still failing in end-to-end execution

Codex ran the bootstrap and hit real failures. A 6-agent audit of the full pipeline (backend codegen, LLVM FFI bindings, CLI dispatch, MIR coverage, bootstrap scripts, runtime linking) traced many of those failures to **specific code bugs, not fundamental architecture gaps**. Those fixes were valuable and moved the pipeline materially forward.

However, after re-running the canonical Linux Stage 1 -> Stage 2 flow, the chain still does **not** pass end-to-end. The remaining failure is now in the self-hosted frontend path rather than the earlier dispatch/runtime-symbol bugs.

### Bugs found and fixed

| # | Severity | Bug | Fix |
|---|----------|-----|-----|
| 1 | CRITICAL | Rust CLI `native_build.rs` silently ignored `--backend` flag (accepted but discarded the value) | Now captures backend, normalizes aliases, sets `config.backend` and `SIMPLE_BACKEND` env var |
| 2 | N/A | LLVM feature not enabled in Rust seed cargo profile | Not a blocker — by design. Rust seed uses Cranelift for Stage 1. Stage 2+ uses Pure Simple's own llvm-lib backend |
| 3 | HIGH | `llvm_lib_translate_expr.spl` had `case _: ()` catch-all that silently dropped ~50 MIR instruction types (SIMD, GPU, VHDL, async, inline asm) | Replaced with explicit cases for pipeline ops + InlineAsm, catch-all now prints warning |
| 4 | HIGH | `cli_compile.spl` had two overlapping conditions routing `--backend llvm-lib` to Rust FFI `rt_native_build()` with hardcoded source dirs, bypassing Pure Simple driver | Consolidated to single block: `llvm-lib` routes to `cli_compile_pure_simple()` |
| 5 | MEDIUM | `runtime_compiler.spl` silently skipped missing runtime `.c` files with `continue` | Core `runtime.c` now mandatory (returns error), others optional with descriptive warning |
| 6 | MEDIUM | No LLVM IR verification before optimization/emission — malformed IR silently proceeded | Added `llvm_verify_module()` call after translation, warns in verbose mode |
| 7 | P3 | `CallTerminator` ignores unwind path | Not fixed — compiler source doesn't use exception unwinding, not needed for bootstrap |
| 8 | LOW | Power operator (`**`) silently returned zero when neither `llvm.pow.f64` nor `rt_pow` was found | Now prints warning before fallback to zero |

### Why bootstrap should work now

**The dispatch chain is complete and correct:**

```
Stage 1 (Rust seed → Cranelift):
  Rust seed CLI (native_build.rs) → NativeProjectBuilder → Cranelift codegen → Stage 1 binary
  No --backend flag needed. Cranelift is the default and only backend in Rust seed.
  Stage 1 binary contains ALL Pure Simple source compiled to native, including llvm-lib backend code.

Stage 2 (Stage 1 → llvm-lib):
  Stage 1 binary main.spl → run_native_build_bootstrap() → detects --backend llvm-lib
  → aot_native_file_with_backend(entry, output, "llvm-lib")
  → CompilerDriver → LlvmLibCodegenAdapter → LLVM C API via dlopen(libLLVM)
  → object code → link with runtime → Stage 2 binary

Stage 3 (Stage 2 → llvm-lib, self-hosting verification):
  Same path as Stage 2. sha256sum comparison for reproducibility.
```

**What was already solid (confirmed by audit):**

- LLVM FFI bindings (`src/lib/nogc_sync_mut/ffi/llvm.spl`): 120+ functions, complete, correct signatures, safe memory management. Production ready.
- Backend factory routing: `BackendKind.LlvmLib` correctly dispatched through `CodegenFactory`.
- Backend name strings: consistent across all files ("llvm-lib" and "llvmlib" both handled).
- Type mapper: covers all types needed by compiler source (vector types missing but compiler doesn't use them).
- Bootstrap script (`scripts/bootstrap/bootstrap-from-scratch.sh`): correct 6-phase pipeline with LLVM detection, artifact verification, hash comparison.
- MIR instruction coverage: all 25 instruction types used by the compiler itself are fully implemented. The ~50 unhandled types (SIMD, GPU, VHDL, async) are only generated for user code that uses those features, not for the compiler's own source.

**Key insight:** Codex's observed failure — "runtime symbols missing in pure-Simple compile/interpreter paths" — was caused by Bug #1 (Rust CLI silently ignoring `--backend`, so Stage 2 was secretly using Cranelift and hitting Rust-side symbol gaps) and Bug #4 (`compile --backend llvm-lib` routing to Rust FFI `rt_native_build()` instead of the Pure Simple driver). With both fixed, the Stage 1 binary now correctly routes `--backend llvm-lib` through the Pure Simple compiler driver, which uses the in-tree llvm-lib backend that dynamically loads libLLVM via dlopen. No Rust runtime symbols are needed on this path — the entire compilation stays in Pure Simple.

### What re-testing showed after Claude's fixes

The Claude-fixed blockers were real:

- Stage 1 now enters the correct bootstrap path for `native-build --backend llvm-lib`.
- The pure-Simple driver is reached.
- Source loading, frontend preprocessing, parser init, and entry into `parse_module_body()` now happen in Stage 2.

But the canonical Stage 2 command still fails in the self-hosted frontend:

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

Current observed failure from re-run logs:

- token text now survives into the parser
- token kind is still incorrectly `0`
- line tracking is still suspiciously stuck on line 1 for long stretches
- `parse_module_body()` sees invalid current-token state like `kind=0 text=a`
- the process segfaults before producing `build/bootstrap/stage2/simple`

This means Claude's fixes removed earlier blockers, but did not complete Linux Stage 2.

### Remaining risk

- **Re-tested after fixes, still failing.** Codex re-ran the canonical Linux flow after integrating follow-up fixes. The remaining integration failure is no longer the original CLI/runtime-symbol issue; it is now in the self-hosted lexer/parser state path during Stage 2.
- **libLLVM must be installed.** Stage 2+ requires `libLLVM-*.so` on the system. The bootstrap script already checks for this and skips LLVM phases if not found.
- **Bug #7 (unwind ignored)** is low risk for bootstrap but will matter for user code that relies on exception-like control flow through `CallTerminator`.

### Current active blocker

The narrow active blocker is in the frontend bootstrap path:

- file: `src/compiler/10.frontend/core/lexer.spl`
- symptom: token text survives, but token kind is still `0`
- downstream effect: parser enters `parse_module_body()` with invalid token state and then segfaults

This is a much smaller problem than the original audit found, but it still blocks Linux Stage 2 and therefore blocks Stage 3, FreeBSD validation, and any claim that bootstrap is passing.

### Recommendation

Do not mark Linux Stages 1-3 as Done yet.

Immediate next action:

1. Fix the remaining self-hosted lexer/parser token-kind bug in `src/compiler/10.frontend/core/lexer.spl`.
2. Re-run the canonical Stage 2 command until `build/bootstrap/stage2/simple` is actually produced.
3. Only then run Stage 3 and the smoke/hash checks.
