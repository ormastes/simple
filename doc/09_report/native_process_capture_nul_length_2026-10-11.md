# Native process capture: NUL length repair and evidence limits

Status: locally applied; Windows provider and production value/tuple correctness
passed. **End-to-end performance is NOT admitted.** POSIX execution, Simple SSpec,
the reusable recipe as a whole, and Phase3 qualification remain UNRUN. No remote
landing or compiler rebuild was performed for this repair.

## Repair and ownership

`runtime_process.c` passed captured buffers through `strlen`, losing the first
NUL and every following byte. Result construction now takes explicit lengths;
timeout-marker concatenation preserves the entire stderr prefix and guards size
overflow. Null buffers normalize their lengths to zero. Error literals use
`sizeof(literal)-1`; only known C diagnostic/timeout strings use `strlen`.

Windows already records both lengths. POSIX now exposes additive length getters
in `runtime_fork.c/.h`, stores the lengths after truncation/incomplete markers,
and resets them with the owned buffers. Pointer lifetime and existing APIs are
unchanged. The Simple `process_run_bounded` facade and native tuple adapter forward
the captured values without trimming or conversion; neither needs a source edit.

Unrelated dirty `runtime.c` was excluded. The production-ABI probe used real
`runtime_native.c`, `runtime_process.c`, `runtime_legacy_core.c`, memory/thread/
memtrack/SIMD owners and `runtime_process_owned.c`, with canonical standalone
flags. No fake value functions, unresolved-symbol suppression or duplicate-owner
suppression were used in that probe. Initial narrow links exposed missing hosted
owners; a broad `runtime.c` link was rejected for duplicate definitions. The final
link uses the canonical owners instead.

## Correctness evidence

All raw evidence is under
`build/native_probe/process-capture-bytes-20261011/`.

| Check | Result | Retained evidence |
|---|---|---|
| Original provider, byte adapter | RED: 6 failures / 11 cases, exit 1 | `baseline/red2/compile/retained.log` |
| Candidate provider, byte adapter | GREEN: 0 failures / 11 cases, exit 0 | `candidate/green/compile/retained.log` |
| Targeted NUL → empty → text reset | 2 cases passed, exit 0 | `candidate/reset/compile/retained.log` |
| Real production values and tuple decoding | 5 cases passed, exit 0 | `abi/integration/compile/retained.log` |

Each executable run closed its Windows Job tree quiescently under a 30-second,
1-GiB RSS bound and 16-MiB retained-log bound. The original launcher preparation
errors (missing output parent and required TMPDIR) remain recorded; neither
launched the provider test. The six RED predicates covered Git NUL records with
rename names/spaces, NULs on both streams at the exact bound, the timeout API,
over-bound head/tail output at limits 8 and 1, and NUL-bearing timeout stderr.
Passing controls cover empty/text output, exit 7, zero bound and rejected inputs.
The additional reset check was run separately without rerunning the green set.

The production check exercises real `rt_string_new`, `rt_array_push/get`, string
length/data accessors and `rt_process_run_bounded_tuple`, including unboxed exit
7. It is a native C ABI integration check, not a compiled Simple program or a
complete runtime ownership/lifetime audit.

Persistent checks:

- `src/runtime/test/rt_process_capture_bytes_selfcheck.c`
- `src/runtime/test/rt_process_capture_value_selfcheck.c`
- `test/02_integration/runtime/process_capture_nul_spec.spl` (five authored cases;
  executable UNRUN, requires Python and the repaired native runtime)
- `scripts/check/check-process-capture-bytes.ps1` (PowerShell syntax checked;
  complete recipe execution UNRUN). Example invocation:
  `pwsh -File scripts/check/check-process-capture-bytes.ps1 -OutputDirectory C:/dev/simple/build/process-capture-check-fresh`

The recipe requires a fresh output path, captures real owners and headers, pins
inputs, bounds compilation/execution, verifies exit/sentinel/Job receipts and
fails closed on missing fixtures or mismatches. It never reads `runtime.c`.

## Failed end-to-end performance admission

Seven paired samples per workload, alternating baseline/candidate order; each
sample performs 20 child captures, with 64 KiB on each stream. Identical pinned
harness/compiler/flags differ only by provider source. NUL fixtures place their
first NUL near the end so restored output volume is visible and nearly matched.
These samples are whole capture invocations, including child startup and polling.
RSS is the containment Job peak; CPU time was not recorded by that collector.
Nearest-rank p95 with seven samples is the maximum, not a precise tail estimate.

| Workload/lane | p50 s | p95 s | Max Job RSS KiB |
|---|---:|---:|---:|
| Text baseline | 1.9847982 | 3.7267281 | 27,528 |
| Text candidate | 1.4391774 | 6.4936333 | 25,812 |
| NUL baseline | 1.4220106 | 3.1060426 | 25,888 |
| NUL candidate | 1.4703130 | 4.0325218 | 26,332 |

Text p95 regressed; NUL p50, p95 and peak RSS regressed. These rows do not satisfy
the user's no-regression acceptance criterion. The cohort was not rerun to select
a better result. Large individual swings and another build lane are possible
confounds, but no retained CPU/stage observations establish their cause.
Raw chronology, receipts and binary hashes: `cohort-rows.json`, `cohort-pins.json`
and each `bench-text-N` / `bench-nul-N` directory.

Both lanes made 80 adapter string allocations per sample. Text copied bytes were
identical (2,621,780); candidate NUL output restored 80 bytes (2,621,680 →
2,621,760). This correction does not introduce another capture buffer or copy,
but the returned string now owns bytes previously lost after NUL. Early-NUL
payloads can therefore retain materially more valid output, bounded by the
existing stream limit and marker allowance; that necessary cost is not concealed
as a memory improvement.

## Separate constructor attribution

A new component probe includes the exact provider constructor with the same
test value adapter, excluding spawn/poll and production registry behavior. Five
paired samples per workload construct and free 20,000 results with two 65,535-byte
streams. QPC measures wall time; GetProcessTimes measures process CPU; Windows
reports the process's own peak working set. This is separate evidence and does
not replace the failed end-to-end cohort.

| Workload/lane | Wall p50 s | Wall p95 s | CPU p50 s | Max own RSS KiB |
|---|---:|---:|---:|---:|
| Text baseline | 0.4722845 | 0.5052427 | 0.468750 | 4,476 |
| Text candidate | 0.2501926 | 0.2593506 | 0.250000 | 4,476 |
| NUL baseline | 0.4751969 | 0.5332368 | 0.484375 | 3,968 |
| NUL candidate | 0.2452672 | 0.2537268 | 0.250000 | 3,968 |

Both lanes made 40,000 string allocations/sample. Text bytes were identical
(2,621,400,000); NUL candidate restored 80,000 bytes/sample. The component improved
wall/CPU with unchanged observed peak RSS. It supports the removal of repeated
length scanning as a local improvement, but cannot attribute the earlier p95
spikes to OS startup/polling or establish production end-to-end performance.
Evidence: `constructor-bench.c`, `constructor-pins.json`, `constructor-rows.json`.

## Identity and outstanding gates

- Baseline provider SHA-256:
  `29073abc140864cc58656f9820ad413d6662d5e00cf6845f85e533961177728d`
- Reviewed provider, matching current working source and ABI/cohort capture:
  `7ddaa7247d966e6d71042a010eb4b09801a87fda17cda3dad94db9e99c18f088`
- Production-ABI executable:
  `b9b9501e3ea39dcd6b97039510328d5ebf0b1d4f5b3fc3f63ef804b2db783951`
- Additional owner/binary captures: `tested-identities.json`.

POSIX getters were source-reviewed only. WSL availability was queried, but no
POSIX build/test or WSL configuration change was made; that lane remains UNRUN.
Next admission needs a coordinated low-contention whole-provider cohort with
parent/child CPU and separate startup/poll/result timing, production ownership
observations, the native Simple SSpec/Git-store integration, and Phase3 PASS.
The component result cannot waive those gates. This repair is independent of the
scanner allocation guard and is not claimed to fix the Phase3 HIR/MIR failure.
