# HIR worker V4 launch: remaining-budget gate expires before any worker claims a module (2026-11-13)

**Status:** OPEN (observed 2026-11-13 ~04:30 KST, aarch64 Linux, s3j/J2 lane, stage2-compiler-tests `compiler_cli_build` row)
**Area:** `src/app/cli/worker_hir_owner_v1.spl` (V4 process-observation launch path)
**Previous gate:** `profile_hir_workers_linux_pin_rejects_dynamic_elf_2026-11-12.md` (FIXED — the
`[rt-pin] dynamic ELF admitted (system-loader class, Darwin parity)` lines prove both pin fixes
bef1d69a6c2 + 34886d22cc2 now work and workers launch)

## Symptom

With the pin fixed, the HIR shard owners fail one gate later, both shards identically,
`claimed=0 sealed=0` (no child ever started):

```
[hir-shard] owner=0/2@0 status=CRASH exit=-1 claimed=0 sealed=0 finished=false
[hir-shard] owner=0/2@0 reason: HIR worker deadline expired or exceeds V4 bound
```

`worker_hir_owner_start_v1` (worker_hir_owner_v1.spl:234) computes
`remaining_ms = worker_hir_remaining_budget_v1(profile.deadline_ms, time_now_monotonic_ms())`
after the full admission sequence (capabilities probe, executable pin + digest verify of the
~45 MB dynamic binary, cwd pin, V4 reservation) and refuses to spawn when `remaining_ms <= 0`.
Row elapsed at failure: 548 s; both workers tripped the gate at the same point in the sequence.

## Leading hypotheses

1. **Clock-domain mismatch**: `profile.deadline_ms` may be computed on a different clock basis
   than `time_now_monotonic_ms()` (e.g. wall/epoch ms vs CLOCK_MONOTONIC), making `remaining`
   hugely negative at first use. Deterministic, matches the identical dual-worker failure with
   claimed=0, and matches this path never having executed on Linux before (the pin gate always
   fired first -- the doc above says verification was pending).
2. **Admission cost accounting**: if the deadline is set before the pin/digest sequence starts
   and the admission sequence is slow (sha256 of 45 MB under the pinned-memfd path, run twice),
   minutes-scale budgets could genuinely expire. Less likely to zero out both workers at the
   same pre-spawn point.

## Why this does not block stage3

The stage2 admission receipt, parent receipts, and runtime capsule are published BEFORE the
test matrix runs; the matrix rows are test-harness gates, not compiler-correctness evidence
(no module ever ran). The s3gen lane precedent: its stage2 test phase also died (log ends
"Terminated"), admission still stood, and the stage3 self-build resumed from the admitted
receipts. The stage3 native-build path does not use the V4 HIR-shard launch at all (MIR
shards spawn via plain `process_spawn_async`, native_build_main.spl:1213).

## Repro / evidence

- J2 lane logs: build/bootstrap-jgen/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log (`reason: HIR worker deadline expired or exceeds V4 bound`).
- Fix verification for the pin: same log's `[rt-pin] dynamic ELF admitted` lines.

## Next

1. In `worker_hir_owner_v1.spl`, log `profile.deadline_ms`, `time_now_monotonic_ms()`, and the
   deadline's origin clock when `remaining_ms <= 0` (one-line diagnostic).
2. Check the deadline producer (row scheduler) for the clock basis; align to monotonic.
3. Re-run the slim stage-2 matrix row compiler_cli_build on a quiet box.

## Fix landed (2026-11-13 ~04:45): clamp to the V4 maximum instead of refusing

`worker_hir_remaining_budget_v1` returned -1 whenever the remaining budget
exceeded PROCESS_OBSERVATION_MAX_DEADLINE_MS (1 h). The parent deadline
defaults to 6 h (DEFAULT_TIMEOUT_MS = 21600000), so every default-timeout HIR
worker launch failed pre-spawn with "deadline expired or exceeds V4 bound" —
deterministic, dual-worker, claimed=0. The clock domains were never mismatched
(deadline and check both use time_now_monotonic_ms); the budget was simply
over the V4 wall-clock cap by construction. Fix: clamp the over-long budget to
3600000 ms. Spec: worker_hir_profile_v1_spec.spl pins the clamp and the
expired-deadline -1 cases.
