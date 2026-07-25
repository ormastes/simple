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

## RESULT (2026-07-20): the quadratic fix is REAL but does NOT cure the hang

The suspect fix below was landed (`6e20fe04e80`) as a proven-safe hot-path
improvement, but a clean SMP build **with the fix applied still hangs**. Decisive
evidence, quiet host (98 GB free, 0 OOM):

- ~23 min past `aot:format:done`, **no `.ll` written**, then killed at 34 min.
- RSS **byte-flat** (1,534,888 → 1,534,896 kB over 60s) while one thread held
  **exactly one core** (1201 ticks / 12s). Same signature as before the fix.

Interpretation: the parallel-array O(N²) maps were genuinely quadratic, but they
are **not the dominant cost** of SMP emission. This confirms the honest caveat
recorded when the suspect was first proposed (mechanism, not magnitude). **The
dominant cost is still unidentified.**

### Next investigation (do NOT just re-run)

The live process cannot be introspected here: `ptrace_scope=1` blocks gdb on a
non-descendant, `/proc/PID/stack` needs ptrace, `eu-stack` isn't installed. Find
the real cost with **file-append instrumentation** (NOT `print` — block-buffered,
lost on kill; NOT `eprint` — dropped on the native-build path). Concretely:
open-append-close a record per function inside `translate_function`
(`_MirToLlvm/core_codegen.spl`) AND per phase inside it, so the log survives the
kill and localizes which function (or which inner loop) spins. Then look there
for another `.push()`-rebuild, a per-instruction linear scan over a growing list,
or an O(blocks²) phi/predecessor walk.

## Candidate fix (LANDED 6e20fe04e80) — necessary but not sufficient

**Change** (3 sites, no signature or call-site changes):
`var_reassign_analysis.spl` `local_count_increment` + `local_alias_set`, and
`var_reassign_ssa.spl` `ssa_local_map_set` each replaced a *rebuild loop*

```simple
var updated: [i64] = []
while i < values.len():
    updated = updated.push(if i == idx: new_value else: values[i])
```

with an index assignment:

```simple
var updated = values
updated[idx] = new_value
```

This matters more than it looks: the rebuild loop calls `.push()` N times and
each push clones the whole array, so **one update was O(N²) by itself** — and it
runs per instruction. Index assignment has the uniqueness fast path.

**Validation (why it was safe to land):**
- Both related specs match pristine-origin baselines EXACTLY:
  `var_reassign_analysis_spec.spl` 18/4, `runtime_array_assignment_ssa_spec.spl`
  7/1, identical with and without the change (baseline captured by stashing).
  Those failures are pre-existing on origin.
- A full single-hart rv32 firmware build + **10/10 QEMU boot gate** passed with
  this change in a clean tree — proves it does not alter codegen.
- It does **not** cure the SMP hang (see RESULT above) — landed on its own
  merits as an O(N²)→O(N) hot-path fix, not as the SMP fix.

## Environment blocker: builds cannot complete on this host

Eleven build attempts; **not one failed for a reason connected to the fix**:

| cause | attempts |
|---|---|
| `unknown extern function: rt_heap_registry_count` (see the phase-profile bug doc) | 3 |
| **killed by `earlyoom` (SIGTERM, rc=143)** | 4 |
| emission hang (the original defect) | 3 |
| link failures (ABI/libgcc, since fixed) | 1 |

The OOM kills are host contention, not this workload: `earlyoom` logged
4 kills in 10 minutes with **swap fully exhausted (0 of 8191 MiB)**, available
memory swinging 47 GB → 12 GB in ~13 minutes, driven by another session's
repeated `./bin/simple replay` jobs (3 concurrent, ~1.4 GB each, respawning).
`earlyoom` selected this build at badness ~973 (VmRSS ~1.4 GB). Even a
~15-minute single-hart build was killed. Disk was also at 99%.

**Resume recipe** (needs a quiet host, or `oom_score_adj` arranged with whoever
owns the competing jobs):

```sh
# in a worktree at a seed-compatible base, with the fix from scratchpad/fix_emit/MIROPT/
NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple NVME_RV32_SMP=1 \
  NVME_RV32_BUILD_TIMEOUT_SECS=10800 \
  sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
```

Note the build scripts force `SIMPLE_COMPILER_PHASE_PROFILE=1`, so on pristine
sources this fails immediately until the seed is rebuilt — see
`phase_profile_flag_unusable_seed_missing_rt_heap_registry_count_2026-07-20.md`.
Validate with the single-hart gate FIRST (cheaper, same SSA path), then SMP.

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
