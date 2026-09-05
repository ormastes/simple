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
