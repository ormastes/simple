# rt dual-implementation ratchet red at origin/main: four symbols landed single-lane without a baseline row

**Date:** 2026-09-06 · **Status:** RECORDED (debt baselined, twins still owed) · **Gate:** `scripts/check/check-rt-dual-implementation-ratchet.shs` (push tier, blocking)

## What was found

Pushing the SOSIX lane (which adds only the dual-lane pair `rt_fd_pread` /
`rt_fd_pwrite`) was blocked by the ratchet with `4 new, 0 stale`. All four
symbols exist on `origin/main` byte-identically to the local tree, so the gate
is red at origin itself and every push from a host with a working pre-push hook
is blocked, regardless of content. They were pushed after the 2026-09-01 baseline
without a baseline row, which is only possible with `--no-verify` or from a host
whose hook did not run.

| Symbol | Lane | Upstream commit | Owner lane |
|---|---|---|---|
| `rt_phase_profile_record` | rust-only | `5e09b3ef2fd` 2026-09-02 fix(runtime): unify duplicated rt_mem_snapshot_* Rust providers | runtime |
| `rt_to_int_dynamic` | c-only (`src/runtime/runtime_native.c`) | `b4a7f10ca46` 2026-09-03 fix(codegen): two silent miscompiles | codegen |
| `rt_vulkan_copy_u32_slots` | rust-only | `320e6d99e4b` 2026-09-05 perf(bench): C Vulkan 2D reference vs Simple Engine2D (#346) | graphics bench |
| `rt_vulkan_readback_u32_checksum` | rust-only | `320e6d99e4b` 2026-09-05 (#346) | graphics bench |

## What was done

The four rows were added to `scripts/check/rt_dual_implementation_baseline.txt`
by hand with a dated review note (the prior note was kept; `--generate-baseline`
would have discarded it). This records existing debt so the gate describes the
tree again; it does not accept them as new single-lane symbols. The directive
still applies: each owner lane owes the missing twin (C for the three Rust-only,
Rust for `rt_to_int_dynamic`), after which the row becomes STALE and is removed.

## Why not twins here

The Vulkan readback pair and the phase profiler need real graphics/profiling
context that the SOSIX lane does not own; adding stub twins would satisfy the
ratchet while diverging behaviour, which is the failure the gate exists to catch.

## Second gate, same shape: `check-runtime-source-list-parity`

Audited every tree-scoped blocking push gate on a pristine `origin/main`
checkout. Two are red there, independent of any lane: the rt-dual ratchet above
and `check-runtime-source-list-parity` (`FAIL — 131 file(s) checked, 4
offender(s) (3 changed, 1 new)`). Everything else passes.

The parity gate exists to catch a build-list entry being DROPPED, which turns a
symbol into a NULL GOT slot and a segfault at first call. None of the four
offenders is that:

| File | Baseline | Now | Reading |
|---|---|---|---|
| `runtime_coverage_core.c` | simple | seed,simple | GAINED a list |
| `runtime_memory.c` | simple,rust | seed,simple,rust | GAINED a list |
| `runtime_process_owned.c` | simple,rust | seed,simple,rust | GAINED a list |
| `slang_ggml_shim.c` | (absent) | none | new; belongs to no static list by design |

The three membership changes are all additions, the safe direction.
`slang_ggml_shim.c` defines `slang_ggml_*` (one Simple caller each) and its own
header states it is the int64-only ABI for the **dynamic** SFFI, dlopen-ed from
a separately built shared library — so membership `none` is correct, not a
missing-symbol risk.

Rows updated by hand with a dated note (not `--generate-baseline`, which
reorders the file and discards prior review notes). Owners of the three files
should confirm the seed-list addition was intended.
