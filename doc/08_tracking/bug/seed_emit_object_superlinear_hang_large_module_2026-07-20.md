# Seed interp: `native-build --emit-object` never completes IR emission on a large module (superlinear, single-threaded)

- **Date:** 2026-07-20
- **Status:** open — BLOCKS the rv32 NVMe firmware QEMU gate (no ELF is produced)
- **Severity:** high (a 479-function module cannot be built at all; three runs
  killed at 1h, 3h, and 6h ceilings with zero object output)
- **Area:** seed interpreter execution of
  `src/compiler/70.backend/backend/_MirToLlvm/*` (`translate_module` /
  `translate_function`)

## Symptom

`bin/simple native-build --target riscv32 ... --emit-object` on the SMP NVMe
firmware (`NVME_RV32_SMP=1`, 479 MIR functions) reaches the emission phase and
never leaves it. The build wrapper kills it at whatever ceiling is configured;
no `/tmp/simple_llvm_<pid>.ll` is ever written, so the failure is strictly
BEFORE llc — inside `.spl` MIR→LLVM text translation.

## Measurements (three independent runs, pristine worktree at origin tip)

| Run | Ceiling | Parse→`aot:format:done` | Time in emission | `.ll` written | Result |
|-----|---------|------------------------|------------------|---------------|--------|
| 2   | 3600s   | +596s                  | ~50 min          | no            | rc=124 |
| 3   | 10800s  | +646s                  | ~2.8 h           | no            | rc=124 |
| 4   | 21600s  | +591s                  | >2.25 h (killed) | no            | rc=124 |

Everything up to and including `aot:format:done` is reproducibly ~10 minutes.
All remaining time is emission. If emission were linear this would be ~21
seconds **per function** of pure text generation — implausible for an
interpreter; the shape is superlinear.

## It is NOT a deadlock (thread evidence)

`/proc/<pid>/task/*/stat` sampled twice, 12s apart, on the live run-4 process:

- 5 threads total; **1 thread (`R`) accrued 1201 ticks = 12.01s CPU in 12.0s
  wall (100% of one core); the other 4 accrued exactly 0.**

So: single-threaded, compute-bound, making no observable output. A whole-process
sample had shown `state=S` + `futex_wait_queue`, which reads as "blocked on a
lock" — that is the *sampled* (idle) thread and is misleading. **Always sample
per-thread utime deltas, never the process-level state letter.**

## Corroborating signal: flat RSS

RSS is byte-flat at ~1,507,200 KB for the entire multi-hour run. Emission
accumulates the whole module's IR in an in-memory string builder, so genuine
linear progress through functions would grow RSS by tens of MB. Flat RSS +
pegged CPU = spinning over bounded data, not producing output.

## What has been ruled out

- **Module-lifetime array/string quadratics.** The `LlvmIRBuilder.instructions`
  O(M²) accumulator was found and fixed (RtStringBuilder externs, `de6c12922b64`).
  A follow-up grep of the whole emission path found no other module-lifetime
  `self.f = self.f.push(...)` or `s = s + ...` accumulator; the remaining hits
  are per-call/per-switch/per-scope (small N) or off-path (C/VHDL/WASM builders).
- **That the builder fix caused this.** Run 2 (pre-fix) was already ~50 min into
  emission when killed. The fix did not materially change emission wall time —
  which is itself the tell that the dominant cost is elsewhere.
- **Missing externs.** `rt_string_builder_*` resolve fine (a missing
  EXTERN_DISPATCH entry would fail in minutes, not hours).

## Prime remaining hypothesis (untested)

A **function-local** quadratic — an accumulator or re-scan whose N is one
function's own instruction count — inside `translate_function` or its
per-instruction helpers. This was explicitly deprioritized during the scan as
"tolerable", which is wrong: the SMP firmware plausibly contains a very large
generated/unrolled function (4-hart tables), and a per-instruction re-scan
quadratic in a single multi-thousand-instruction function reproduces every
observation here (one thread, superlinear, flat module-level output, no `.ll`).

**Next step for whoever picks this up:** rank the SMP module's functions by MIR
instruction count and check whether `translate_function` re-scans any list that
grows per emitted instruction.

## Instrumentation landmine

Do **not** diagnose this with `print`: under `native-build` stdout is redirected
to a file and therefore **block-buffered (~8 KB)**, so per-function progress
lines never flush before the kill — a 2-hour instrumented run produced zero
lines. `eprint` is separately lost on the native-build path
(`reference_native_build_eprint_lost`). Use **file-append** instrumentation
(open/append/close per record) for any progress probe on this path.

## Impact

The rv32 NVMe firmware SMP QEMU gate (`boot.shs --smp`, marker
`ALL RV32 4CORE IPC CHECKS PASS`) cannot run: there is no
`build/nvme_fw_rv32_smp.elf` to boot. The firmware source fixes and the two
landed emit-object fixes (`19d868da3ace`, `de6c12922b64`) are unaffected and
remain correct — this is a throughput/termination defect in interpreted
emission, not a correctness defect in the emitted code.
