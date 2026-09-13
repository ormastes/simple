# `child died by signal` in the compiler/app reruns: confirmed host-load artifact, not a defect

- Status: INVESTIGATED — root cause confirmed for this session's occurrences; not a code fix (there is nothing to fix)
- Binary: `/home/yoon/cargo-unitp1/release/simple`, sha256 `d4c0779cef6cf0cc4054`
- Base: `work/unit-p1-2026-09-13` at `809eb76bfc7`

## What was measured

Re-running `test/01_unit/{os,compiler,app}` on the rebuilt seed to measure the
JavaNew fix's blast radius (see the receipt), all three directories were run
concurrently (host had 20 cores, load was ~2-4 at kickoff). `test/01_unit/os`
finished first (hit its own 3600s cap). `compiler` and `app` ran alongside
each other for their full 3600s too. Host `uptime` load average peaked at
**21.63** while all three were active together — self-inflicted by this
session's own concurrency, not external.

Final `died by signal` counts in that run:
`test/01_unit/compiler` postfix log: **52** unique spec files.
`test/01_unit/app` postfix log: **43** unique spec files (not fully
enumerated; sampled).

## Root cause, confirmed by direct test

Once all three background sweeps had finished (load dropped back to ~2.6),
5 of the crashed spec files were rerun individually, no other heavy process
active:

| spec | during 3-way concurrent sweep | rerun alone, quiet host |
|---|---|---|
| `test/01_unit/compiler/backend/asm_clobbers_spec.spl` | `died by signal` | **3 examples, 0 failures** — clean pass |
| `test/01_unit/compiler/backend/asm_raw_block_escape_spec.spl` | `died by signal` | **6 examples, 0 failures** — clean pass |
| `test/01_unit/compiler/backend/c_backend_export_spec.spl` | `died by signal` | 4 examples, 4 failures — a REAL, different, reproducible failure (not a crash); worth its own triage, not investigated further here |
| `test/01_unit/app/build/build_targets_spec.spl` | `died by signal` | 34 examples, 33 passed, 1 failed — a REAL, different, reproducible failure (not a crash) |
| `test/01_unit/app/build/change_classifier_spec.spl` | `died by signal` | **8 examples, 0 failures** — clean pass |

3 of 5 sampled crashes disappear entirely on an isolated rerun; the other 2
turn into ordinary, unrelated test failures — neither crashes. None of the 5
reproduces the crash when the host is not under this session's own 3-way
concurrent load. This matches the runner's own honest phrasing for this
outcome: `TERMINATED: child died by signal with no crash sentinel and no
fault diagnostic (unverified -- an external killer such as earlyoom cannot be
ruled out)`.

## Conclusion

The bulk of the 95 combined `died by signal` reports across
`compiler_postfix`/`app_postfix` are very likely a **resource-contention
artifact of running three `timeout 3600` full-directory sweeps
concurrently in this session**, not compiler or runtime defects. This is a
process lesson, not a code fix: running heavy sweeps one at a time (as the
original guide specified, and as this session should have kept doing once
`uptime` load crossed a sane threshold) avoids manufacturing this entire
false-crash bucket. No code change follows from this finding.

## Caveat — do not over-generalize

This does NOT establish that every `child died by signal` report anywhere in
this lane's receipts is a load artifact. The FIRST session's `hir` sweep
(`test/01_unit/compiler/hir/hir_import_registration_per_symbol_cost_spec.spl`,
`module_surface_semantic_projection_spec.spl`) crashed running ALONE, not
concurrently with two other sweeps, so that occurrence is not explained by
this finding and stays open/untriaged. Each new report should still be
sampled for individual reproduction before being written off as load noise.
