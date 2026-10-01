# Site 15: Stage-2 link fails — the Rust runtime lane never twinned `rt_cpuid` / `rt_cpu_is_*`
- Status: **FIXED (2026-09-13)** — twins landed in `a59b81f9e1c`; closed by a full
  rebuild, see "Closed by measurement" at the end of this record.
- Area: runtime dual-implementation (`rt_*` twins) / Stage-2 native-build link
- Area: runtime dual-implementation (`rt_*` twins) / Stage-2 native-build link
- Found by: BOOT-15, `--full-bootstrap --backend=llvm --mode=dynload --jobs=10
  --stop-after-stage2 --output=build/bootstrap-boot15a`, head `6b8965cf30d`
  (= `origin/main` `2cb951036a4` + BOOT-14's four script commits + BOOT-13's
  prototype fix `4b044028210`), 15:53:52 -> 16:06:18 (**12m26s**), rc=1
- Blocks: Stage 2 entirely — no candidate binary is produced, so Stage 3 and
  Stage 4 cannot be reached at all. This is a HARD regression against BOOT-13,
  which admitted a Stage 2 at 14:11 today.
- Seed used for all specs/probes: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
  50093192 B, sha256 `3d120a6f9ab5704b2225…`

## Symptom (verbatim, `scratchpad/boot15/bootstrap.log:35-39`)

```
    | Build failed: link failed: mold: error: undefined symbol: rt_cpuid
    | mold: error: undefined symbol: rt_cpu_is_riscv64
    | mold: error: undefined symbol: rt_cpu_is_x86_64
    | mold: error: undefined symbol: rt_cpu_is_aarch64
    | clang++: error: linker command failed with exit code 1 (use -v to see invocation)
PASS — 1 check(s), stage stage2 failed (exit 1) and said why
  warning: stage2 native-build failed (exit 1); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

`rt_xgetbv`, declared and called from the same Simple module, is NOT in the list.
That asymmetry is the whole bug.

## Measured cause: the two runtime lanes disagree, and Stage 2 links the Rust one

`src/compiler/30.types/simd_capabilities.spl:23,56` declares five externs
(`rt_cpuid`, `rt_xgetbv`, `rt_cpu_is_x86_64`, `rt_cpu_is_aarch64`,
`rt_cpu_is_riscv64`). Measured with `nm -g --defined-only`, not inferred:

| archive (from this run) | `rt_cpuid` | `rt_cpu_is_aarch64` | `rt_xgetbv` |
|---|---|---|---|
| `stage2-runtime-authority/deps/libsimple_runtime.a` (**Rust lane, what Stage 2 links**) | **0** | **0** | 1 |
| `stage2-runtime-authority/libsimple_native_all.a` (Rust lane) | **0** | **0** | 1 |
| `stage2-runtime-authority/libsimple_compiler_backfill.a` | 0 | 0 | 0 |
| `native-objects-*/bootstrap_mutex_core_c_runtime/libsimple_runtime.a` (**C lane**) | 1 | 1 | 1 |

Source side, same asymmetry:
- C lane defines all five unconditionally, `src/runtime/runtime_native.c:15033`
  (`RtCpuidResult rt_cpuid`), `:15066` (`rt_cpu_is_x86_64`), `:15075`
  (`rt_cpu_is_aarch64`), `:15082` (`rt_cpu_is_riscv64`), with the `#if
  defined(__x86_64__)` guard INSIDE each body, so every symbol exists on aarch64.
- Rust lane defines **only** `rt_xgetbv`
  (`src/compiler_rust/runtime/src/value/sffi/env_process.rs:1482`,
  `#[no_mangle] pub extern "C"`). The other four have no `extern "C"` definition
  anywhere under `src/compiler_rust/runtime/`.
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:2340-2363` DOES back
  all five — but as `pub fn rt_cpuid(args: &[Value])`, an interpreter extern in
  the *compiler* crate, not a linkable `extern "C"` symbol in the *runtime* crate.
  That is why the seed interpreter runs this code happily and only the native
  link fails, and why a repo-wide `grep rt_cpuid src/compiler_rust` false-greens.

The gap was already known and frozen: `scripts/check/rt_dual_implementation_baseline.txt:491-494`
carries exactly these four as `c-only`, and only these four of the five.

## Why it appeared now and not in BOOT-13's admitted run

`34b96e29837` "fix(simd): make auto-vectorization actually reach AVX-512 and
enforce the SIMD tags" (2026-09-13 13:51:56 +0900) created
`src/compiler/60.mir_opt/mir_opt/auto_vectorize_target.spl:15`, which imports
`detect_capabilities` from `simd_capabilities`. That is the first edge pulling
these four externs into the **Stage-2 compiler closure**.

```
git show 8b2516a6477:src/compiler/60.mir_opt/mir_opt/auto_vectorize_target.spl | grep -c simd_capabilities  -> 0   (BOOT-13's admitted tree)
grep -c simd_capabilities src/compiler/60.mir_opt/mir_opt/auto_vectorize_target.spl                          -> 1   (this tree / main)
```

BOOT-13 admitted at 14:11 from base `0e2aebed9d0`, which predates that commit.
So this is not a regression introduced by anything BOOT-15 adopted — every lane
building from today's `main` will hit it, the macOS session included.

## Fix direction

Add the four missing `#[no_mangle] pub extern "C"` twins to
`src/compiler_rust/runtime/src/value/sffi/env_process.rs` beside `rt_xgetbv`,
mirroring the C bodies exactly (`cfg!(target_arch = …)` for the three predicates;
`#[repr(C)] struct RtCpuidResult { a, b, c, d: i32 }` + `__cpuid_count` under
`cfg(target_arch = "x86_64")`, zeros elsewhere, for `rt_cpuid`). This is the
mirror image of `core_c_bootstrap_runtime_lane_missing_rt_utf8_math_array_symbols_2026-09-13.md`,
which closed the same class of gap in the other direction.

**Baseline rows 491-494 of `scripts/check/rt_dual_implementation_baseline.txt`
must be deleted with the fix** — once twinned, a `c-only` row is stale and
`check-rt-dual-implementation-ratchet.shs` fails on stale rows by design. That
file is FENCED for this lane (`grep -Fx` hit in `egl_offlimits_v2.txt`), so the
four-line deletion is left for the fence owner and the stale FAIL is reported
rather than papered over.

## Closed by measurement (run B, `build/bootstrap-boot15b`, head `a59b81f9e1c`)

Same canonical command, fresh output root, 16:17:30 -> 16:31:10 (13m40s).

| item | verbatim |
|---|---|
| undefined symbols | `grep -c 'undefined symbol' bootstrap_b.log` = **0** (run A: 4) |
| Stage 2 native build | **`Build complete: 889 compiled, 0 cached, 0 failed`**, `Time: 422.7s compile + 36.0s link = 458.7s total` |
| candidate produced | `build/bootstrap-boot15b/stage2/aarch64-unknown-linux-gnu/simple.rejected`, 152416216 B, sha256 `c371050573bcbf03f9b2…` (pinned exec copy `scratchpad/boot15/pin/cand.boot15b.stage2`) |
| `simple-bootstrap --version` on it | `simple-bootstrap 1.0.1-beta.1`, `version_match_status=0` |

Artifact-level check on the archive Stage 2 actually links, the evidence a source
scan cannot give — `nm -g --defined-only .../stage2-runtime-authority/deps/libsimple_runtime.a`:

| symbol | run A | run B |
|---|---|---|
| `rt_cpuid` | 0 | **1** |
| `rt_cpu_is_x86_64` | 0 | **1** |
| `rt_cpu_is_aarch64` | 0 | **1** |
| `rt_cpu_is_riscv64` | 0 | **1** |
| `rt_xgetbv` | 1 | 1 |

Run B then fails FURTHER ON, at Stage-2 sanity rather than at link — filed
separately as site 16
(`stage2_sanity_positional_route_k1_composition_admission_failed_2026-09-13.md`).

**Still open with this fix, and deliberately not done here:** the four `c-only`
rows at `scripts/check/rt_dual_implementation_baseline.txt:491-494` are now stale
and `check-rt-dual-implementation-ratchet.shs` reports
`FAIL — 2506 symbol(s) checked against 2510 baselined, 0 new, 4 stale`. That file
is FENCED for this lane. Deleting those four lines is the whole remaining fix.

**Not proved here:** that `rt_cpuid`'s 16-byte struct return survives the
pure-Simple emitter's `(i32, i32, i32, i32)` tuple lowering at run time. The link
resolves and the Rust `#[repr(C)]` layout matches the C twin field-for-field; no
Stage-2 execution has exercised the call.
