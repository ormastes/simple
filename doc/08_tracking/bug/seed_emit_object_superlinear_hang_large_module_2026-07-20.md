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

## Leading suspect: O(N²) parallel-array "maps" in the SSA prep pass

**Location (NOT in the backend — this is why a backend-only scan missed it):**
`src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl:32-93`
(`local_count_index` / `local_count_increment` / `local_alias_root` /
`local_alias_set`) and `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:106-126,
913-940` (`ssa_local_map_get` / `ssa_local_map_set` and the instruction-rewrite
loop in `ssa_var_transform_blocks`).

These implement associative maps as **parallel `[i64]` arrays**: a linear scan
to look up, then a full array rebuild via `.push()` on every write.

**Why that is quadratic here — the load-bearing seed fact:** `.push()` in this
interpreter is *unconditionally* `arr.to_vec()`, a full clone
(`src/compiler_rust/compiler/src/interpreter_method/collections.rs:67-72`).
There is **no unique-ownership fast path** for method-call rebuilds — unlike
direct index-assignment `arr[i] = v`, which *does* have an Arc-uniqueness fast
path (`interpreter/node_exec.rs:1140-1184`, benchmarked near-linear to
N=160,000). So the idiomatic-looking `arr = arr.push(v)` is O(N) per write.

**Measured** (standalone reproduction of the `local_count_increment` pattern
under the seed): N=8,000 → 0.44s; N=16,000 → 2.02s (4.6×); N=32,000 → 8.69s
(4.3×). Clean O(N²).

**Reached from the hang site:** `llvm_bootstrap_ssa_function`
(`_MirToLlvm/core_codegen.spl:23-61`) calls `ssa_var_transform_blocks(fn_.blocks)`
per function during emission — matching exactly where all the wall time goes.

### Honest caveat — not yet proven sufficient

A source survey of the SMP-only files found **no giant function** (max 180
lines; ~12 lines/fn across ~265 added functions), and SMP's function count
(479) is only ~2.24× the single-hart baseline (~214). A per-function quadratic
over modestly-sized functions does not obviously extrapolate to the observed
**24×+** wall-clock ratio. So the original "one huge generated function"
hypothesis is **disproven**, and this suspect explains the mechanism but not yet
the full magnitude. Settling it requires a per-function emission trace — note
that `print`-based probes do NOT work here (see the instrumentation landmine
below); use file-append.

### Recommended fix

Replace the parallel-array maps in `var_reassign_analysis.spl` /
`var_reassign_ssa.spl` with genuine `Dict<i64,i64>` (real hash lookup, no
rebuild-per-write). Routing note: that file lives under `60.mir_opt`, owned
separately from the backend.

## Secondary (real, smaller): module-lifetime string accumulator

`add_string_global` (`_MirToLlvm/asm_constraints_helpers.spl:319-334`) keeps two
never-reset module-lifetime accumulators — `self.string_globals.push(decl)` and
`self.string_global_text = "{prev}\n{decl}"` — both O(S) per call over S total
string constants; same class as the already-fixed `LlvmIRBuilder.instructions`
bug. SMP-only files carry ~3× the string-literal density (~118 vs ~55).

The `string_globals` array specifically is **dead**: its only consumer is an
`elif self.string_globals.len() > 0` branch that can never fire, because
`string_global_text` is populated in the same call and is tested first in the
same `elif` chain. Removing the array is a zero-risk constant-factor win.
Converting `string_global_text` itself to `rt_string_builder_*` is NOT
drop-in: `test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl:30-31`
reads it directly as a `text` field with no finish step.

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
