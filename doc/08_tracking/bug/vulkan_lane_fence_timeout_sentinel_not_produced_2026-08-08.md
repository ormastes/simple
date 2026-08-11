# BUG: Vulkan lane fence-timeout sentinel is structurally unreachable

**Status:** Confirmed defect — NOT a flake. 5/5 identical failures in isolation with an otherwise idle GPU.
**Date filed:** 2026-08-08
**Severity:** MEDIUM — one GMB-1 timeout path cannot be exercised; the rest of the Vulkan lane works.

## Affected test

`test/02_integration/gpu_lane/vulkan_lane_session_spec.spl`
Example: "should force the GMB-1 timeout sentinel under a genuinely tight fence
timeout, without hanging".
Verdict, 5 consecutive isolated runs: `Results: 2 total, 1 passed, 1 failed` (all five).

Failure text: `expected subject to be truthy, got ` — the dispatch never reports
the timeout outcome, so the sentinel assertion sees an empty value.

This was initially suspected to be a flake caused by GPU contention (several GPU
specs were running concurrently when it first appeared). That hypothesis was
tested and **disproved**: isolated, serialized, idle-GPU runs fail identically
every time.

## Root cause (verified in-tree, not inferred)

`src/compiler_rust/runtime/src/vulkan/device.rs:1047`
`pub fn submit_compute_command_with_fence(...)` — its own doc comment reads
"Submit a compute command buffer with a real fence **and wait for completion**".

At `src/compiler_rust/runtime/src/vulkan/device.rs:1070` it calls:

```rust
if let Err(e) = fence.wait(u64::MAX) {
    return Err(FencedSubmitError::CompletionUnknown(e));
}
```

The wait is unconditional and infinite, and happens *before* control returns to
Simple. By the time the lane's own bounded wait inspects the fence, the fence is
already signalled — so no finite `timeout_ms` (the spec uses `timeout_ms = 1`)
can ever be observed as a timeout. The timeout branch in
`VulkanLaneSession.dispatch_once` is therefore structurally unreachable, not
merely hard to hit.

The spec drives this with `test/fixtures/gpu_lane/vulkan_bounded_long_loop.spv`,
a shader that provably runs for tens of milliseconds — the fixture is doing its
job; the blocking submit defeats it.

**Correction to an earlier draft of this record:** it named an extern
`rt_vulkan_submit_and_wait_fence`. **No such symbol exists in the tree.** The
real site is `submit_compute_command_with_fence` as cited above. The mechanism
described was correct; the symbol name was not.

## Unblock condition

Provide a non-blocking compute submit so the fence stays observable, e.g. either:

1. a submit entry point that returns as soon as the work is submitted, leaving
   the fence unsignalled for the caller to wait on with a finite budget; or
2. a variant of `submit_compute_command_with_fence` that takes the timeout and
   surfaces "not yet complete" instead of waiting `u64::MAX`.

Note this is a **Rust runtime** gap: the pure-Simple side already implements the
non-completion branch correctly, it simply cannot be reached through the current
native call. Per the repo's pure-Simple-first rule this is one of the legitimate
Rust-only cases (native submit primitive), but confirm no pure-Simple path exists
before changing Rust.

Per `.claude/rules/testing.md` the spec is correct and **must stay RED** until
this is fixed. Do not weaken the assertion, mark it pending, or delete the
fixture.
