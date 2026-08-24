# Simple cannot be built for SimpleOS on any arch: the target simple-core archive never reaches the link line (2026-08-24)

- Status: OPEN (P1 for the SimpleOS bootstrap goal)
- Measured in `/mnt/data/worktrees/goal-lane-c-simpleos-arch` at `22615820e65`.
- Companion to `simpleos_guest_simple_cli_staged_but_never_executed_2026-08-24.md`.

## Verdict per architecture

| target | can Simple be built for SimpleOS? | blocker |
|---|---|---|
| `x86_64-unknown-simpleos` | **NO** | no sysroot producer exists at all |
| `aarch64-unknown-simpleos` | **NO** | link: 20 undefined codegen-emitted `rt_*` |
| `riscv64-unknown-simpleos` | **NO** | link: 20 undefined codegen-emitted `rt_*` |

The riscv64 receipt dated 2026-08-21 (`status=staged`) is **not** counter-evidence:
it was produced by a different compiler build on a different day, and the same
recipe re-run from source today does not link. Nothing that exists now rebuilds it.

## Evidence

Probe, before any artifacts were produced (`SEED=bin/release/x86_64-unknown-linux-gnu/simple`):

```
$ sh scripts/ci/build-simpleos-toolchain.shs --probe-only     # rc=1
  x86_64-unknown-simpleos: FAIL no valid sysroot for x86_64-unknown-simpleos (first candidate: missing build/os/sysroot-x86_64/lib/crt0.o)
  aarch64-unknown-simpleos: SKIP arch not yet buildable: no valid sysroot ...
  riscv64-unknown-simpleos: SKIP arch not yet buildable: no valid sysroot ...
RESULT: FAIL
```

Both non-x86 prerequisites then built CLEAN from source in this worktree:

- `sh scripts/os/simpleos-sysroot-riscv64.shs` rc=0 (crt0.o, libsimpleos_c.a, libsimpleos_all.a, simpleos.ld)
- `sh scripts/os/simpleos-sysroot-aarch64.shs` rc=0 — `[sysroot-aarch64] done: build/os/sysroot-aarch64`
- `sh scripts/os/simpleos-core-archive.shs --target riscv64-unknown-simpleos --backend cranelift`
  -> `archive=build/os/simple-core-simpleos-riscv64/libsimple_runtime.a parts_built=19 parts_failed=0`
- same for aarch64 -> `parts_built=19 parts_failed=0`

So sysroot and runtime-archive production are **not** the blocker on aarch64/riscv64.
With them present the CI wrapper reaches a real build and fails at LINK:

```
$ sh scripts/ci/build-simpleos-toolchain.shs --only aarch64      # rc=1
  aarch64-unknown-simpleos: FAIL native-build failed (rc=8, ...)
Build failed: link failed: ld.lld: error: undefined symbol: rt_alloc
ld.lld: error: undefined symbol: rt_string_new_literal
... 20 distinct undefined symbols, "referenced 978 more times"
```

## Root cause: the archive is resolved, reported, and then not linked

`nm --defined-only build/os/simple-core-simpleos-riscv64/libsimple_runtime.a` defines
**316** `rt_*` text symbols. Cross-checking the 20 undefined names against that archive:

- with `SIMPLE_SIMPLE_CORE_PATH=<dir>`: **19 of 20 are DEFINED in the archive**; only
  `rt_string_new_literal` is genuinely absent.
- with `SIMPLE_SIMPLE_CORE_PATH=<...>/libsimple_runtime.a`: 17 of 20 defined; absent are
  `rt_native_cmp`, `rt_string_new_literal`, `simpleos_guest_arch_id`.
- `grep -c libsimple_runtime.a` over the whole build log: **0** — the archive path never
  appears in the link invocation.

A symbol that is defined in the archive the build was *told* to use, and still undefined at
link, means the archive is not on the link line. This is a link-wiring defect, not a missing
runtime: the CI even prints `runtime_archive=build/os/simple-core-simpleos-<arch>/libsimple_runtime.a`
immediately before the build it does not pass it to. Neither env spelling (file or directory)
changes the outcome. Same shape on aarch64 (`rt_alloc` is defined in its archive and still
reported undefined).

Genuinely missing beyond the wiring bug — must also be fixed, but they are 1-3 symbols, not 20:
`rt_string_new_literal` (both arches), `rt_native_cmp`, `simpleos_guest_arch_id`.
`rt_unwrap_or_trap` appears in this undefined set, tying it to
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18` and the ADVISORY-RED
`scripts/check/check-no-unresolved-runtime-symbols.shs`.

## x86_64 is blocked one step earlier

`grep -rn "sysroot-x86_64" scripts/ src/` returns **nothing**. `scripts/os/` ships
`simpleos-sysroot-aarch64.shs` and `simpleos-sysroot-riscv64.shs` and no x86_64 sibling,
while `src/app/ci/build_simpleos_toolchain.spl:131` probes `build/os/sysroot-<arch>` for
all three and the CI header states x86_64 "must go green". The producer was never written.

## Not the cause (ruled out by measurement)

- Host C toolchain: `cc`, `clang`, `gcc`, `ar`, `llvm-ar`, `ranlib` all present;
  `sh scripts/check/check-c-runtime-compiles-push.shs` -> `PASS — 118 file(s) compiled, 0 errors
  (2 skipped for unavailable external dependencies)`, rc=0.
- The first riscv64 CI failure was `timeout (300s)` on one file under host load ~40-100.
  Re-run directly with `--timeout 1800` it compiles fine and fails at the SAME link step —
  so the timeout was environmental noise, not the blocker.
- A first archive attempt failed with `error: native backend 'llvm' is not available in this
  build; rebuild the Rust driver with --features llvm or use --backend cranelift`. That is the
  deployed seed lacking the `llvm` cargo feature (see CLAUDE.md's inkwell/LLVM pin);
  `--backend cranelift` — what the 2026-08-21 build stamp itself records — builds all 19 parts.

## Fix order

1. Pass the resolved target `simple-core` archive to the link (make `SIMPLE_SIMPLE_CORE_PATH`
   actually reach the link line, or have the CI pass it explicitly) and re-run both arches.
2. Add the 1-3 genuinely missing symbols to the target runtime.
3. Write `scripts/os/simpleos-sysroot-x86_64.shs`.
