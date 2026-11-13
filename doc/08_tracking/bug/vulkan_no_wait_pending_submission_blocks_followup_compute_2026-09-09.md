# Vulkan no-wait submission blocks the next compute command
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN
**Found:** 2026-09-09
**Component:** Vulkan runtime compute ownership

## Defect

`rt_vulkan_submit_no_wait` returns after queue acceptance and retains the
command, fence, pipeline, descriptor set, and buffers in
`VulkanState.quarantined_compute` with a caller-visible `wait_handle`. However,
`rt_vulkan_begin_compute` refuses whenever that vector is non-empty, without
distinguishing a waitable pending submission from the zero-handle
completion-unknown quarantine.

Consequently, a pure-Simple resident renderer cannot enqueue a bounded ring of
recyclable frame slots: the first no-wait submit succeeds and a later
`begin_compute` fails. Several commands can be pre-recorded before the first
submit and then submitted as a finite batch, because `submit_no_wait` does not
apply the quarantine gate. That is not a sustained ring: waiting and destroying
a fence does not remove its native quarantine entry;
`rt_vulkan_destroy_fence` only revokes its public handle. A device-idle reap is
then required before a replacement command can begin, which defeats continued
CPU/GPU overlap.

The representation also conflates states: completion-unknown submissions are
created with `wait_handle = 0`, while
`release_quarantined_wait_handle` assigns the same zero value when a caller
revokes an ordinary waitable handle. A future ring must add an explicit state
tag and must not orphan a pending submission by destroying its only token.

## Current honest behavior

`vulkan_resident_2d.spl` continues to use
`vulkan_sffi_submit_and_wait_fence`, increments
`blocking_queue_submit_calls` for every attempt, and leaves
`device_scene_nonblocking_submits` at zero. It does not claim asynchronous
submission.

## Required runtime fix and evidence

The runtime owner must distinguish waitable pending work from genuinely unknown
completion, allow new command allocation while only waitable submissions are
pending, and release a signaled quarantined command plus all retained owners
when its fence is retired. Descriptor updates must remain forbidden while a
submission using that descriptor may still execute.

Acceptance requires a Vulkan device test that enqueues at least three commands
before any host wait, proves all three caller fence handles remain resolvable,
retires one, recycles its generation, and submits a fourth without device idle,
then verifies no command/fence/resource owner remains. A ring-full case must
apply bounded backpressure. A stale token, timeout, or unknown-completion
negative control must block unsafe reuse and preserve every resource until
completion proof or explicit recovery.

This is a Rust runtime change and was not made by the pure-Simple optimization
review.

## Pure-Simple ownership review (2026-09-09)

The available Simple sequence was traced through
`src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl` and
`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`. A zero-timeout
`vulkan_sffi_wait_fence` is only an observation. A subsequent
`vulkan_sffi_destroy_fence` revokes the public handle but leaves the runtime
quarantine entry alive. `vulkan_sffi_reap_dependency_quarantine` can make the
next `begin_compute` succeed only by proving device idle, which serializes the
queue and is not an async ring.

The Simple-side arrays in `VulkanLaneSession` and the engine backend are not
authority: they contain copied integer handles and cannot inspect
`VulkanState.quarantined_compute` or release `ComputeCommandOwners`. Therefore
no safe Simple-only ring implementation exists against the current API. No
Rust/C/device change was made in this review.

Requirement options and the selected-capability design are recorded in:

- `doc/02_requirements/feature/vulkan_async_compute_submission_ring.md`
- `doc/02_requirements/nfr/vulkan_async_compute_submission_ring.md`
- `doc/05_design/runtime/vulkan_async_compute_submission_ring.md`
- `doc/03_plan/sys_test/vulkan_async_compute_submission_ring.md`


## 2026-11-12 lane triage (vulkan-mac lane, work/fix-vulkan-mac-20261112)

Re-read against current source. The required runtime fix is in the Rust
runtime owner (`VulkanState.quarantined_compute` / `rt_vulkan_begin_compute`
gate / `rt_vulkan_destroy_fence` handle-only revocation), i.e.
`src/compiler_rust` + `src/runtime` — outside this lane's file scope
(src/lib gpu/vulkan/sffi/compositor + scripts/check only). The pure-Simple
side was re-confirmed non-authoritative: `VulkanLaneSession` and the engine
backend hold copied integer handles and cannot inspect or release the native
quarantine entries, so no safe Simple-only ring exists against the current
API, matching the 2026-09-09 ownership review. No source change made. The
acceptance design documents under
doc/02_requirements/feature|nfr/vulkan_async_compute_submission_ring.md and
doc/05_design/runtime/vulkan_async_compute_submission_ring.md remain the
specification for the runtime owner. Status: open.


---

## 2026-11-13 addendum — P3 gpu lane p3-gpu-20261113 (work/p3-gpu-20261113, base 6f4cb189867)

**Verdict: OPEN, unchanged — Rust-runtime-owned; no change possible or
verifiable in a no-cargo Windows lane.** The defect surface
(`VulkanState.quarantined_compute` gating in `rt_vulkan_begin_compute`, fence
retirement not releasing the quarantine entry) lives in the seed Rust runtime,
and the acceptance evidence is a Vulkan-device test (3 commands in flight,
retire-one-recycle-one, no device idle) that cannot run on this host. The
pure-Simple review's conclusion stands: no safe Simple-only ring exists against
the current API, and `vulkan_resident_2d.spl` honestly stays on
`vulkan_sffi_submit_and_wait_fence` with `device_scene_nonblocking_submits=0`.
Grant unchanged: runtime owner implements the state-tagged quarantine +
retirement release, then runs the device acceptance test.

## Triage 2026-11-13 (Linux aarch64, lane uia) — row stays OPEN

On release/1.0.0 c8c3e7bc4f1, Linux aarch64 (DGX Spark GB10), Rust seed af717f53d6bce3e5: vulkan_async_submission_contract_spec 3/3; vulkan_async_session_lifecycle_contract_spec 4/5 (red: keeps every async forward visible to the dual-lane ABI audit, a source-text contract). The runtime session ring exists (rt_vulkan_async_session_*), but its only tests use an injected device and vulkan_resident_2d.spl still submits with vulkan_counted_submit_and_wait_fence. Acceptance (live-device ring test: three enqueued before any wait, retire one, fourth without device idle) is unmet and was not written here.

## 2026-11-13 lane uia2 — acceptance spec written; one seed defect fixed; row stays OPEN

Host: Linux aarch64, DGX Spark. Device selected by ordinal 0 and printed by the
spec: `NVIDIA GB10|vendor=000010de|device=00002e12|driver=912b4080|api=00404138`
(real GPU, not llvmpipe). Base release/1.0.0 `dc14e46a737`.

**Written:** `test/02_integration/gpu_lane/vulkan_async_ring_live_device_spec.spl`
drives `VulkanAsyncSubmissionSession` on a real device. Acceptance clause to
spec step:

| clause | step |
|---|---|
| three commands enqueued before any host wait | "Enqueue three commands before any host wait", `in_flight == 3` |
| all three caller fence handles resolvable | three distinct fences > 0; `poll` of each is PENDING or RETIRED |
| ring-full applies bounded backpressure | fourth `acquire` is `WOULD_BLOCK`, `in_flight` stays 3 |
| retire one | poll own fence to RETIRED, `retire == 1`, `published_sequence == 1` |
| stale token blocks reuse | `poll`/`retire`/`command`/`submit` of the retired token are INVALID |
| recycle, submit a fourth without device idle | new token, new fence, no reap/wait-idle call anywhere in the spec |
| pending work is not released early | `retire` of the never-polled fourth is PENDING, `in_flight == 3` |
| no command/fence/resource owner remains | `close == 1`; a direct `begin_compute` succeeds (it refuses while any quarantine entry exists); descriptors and the lane session release cleanly |
| unknown-completion negative control | NOT covered: cannot be provoked on a healthy device; stays with the injected-device Rust tests |

**It is red, and stays red on Linux.** Two independent causes, both measured:

1. *Fixed here.* The interpreter has no handler for `rt_vulkan_async_session_*`;
   it resolves them with `dlsym(RTLD_DEFAULT)` (`interpreter_extern/vulkan.rs`).
   `src/compiler_rust/.cargo/config.toml` linked the x86_64 Linux and macOS
   seeds with `--export-dynamic` but not aarch64 Linux. Same commit, config
   file before/after: `nm -D` `rt_vulkan_*` 0 -> 132 (all symbols 0 -> 20527);
   `test/01_unit/gpu/vulkan_async_session_backed_spec.spl` 2 examples, 2
   failures (`... is not linked into this binary`) -> 2 examples, 0 failures.
   Size 53.6 MB -> 65.8 MB; 20x `--version` 226-255 ms vs 247-251 ms (same
   commit, two rounds each). A strict-JIT program that really JITs (70-76 ms
   against 3772 ms interpreted; array push, text concat, join, upper, recursion)
   prints the same output on both seeds with no fallback line. The sanctioned
   bootstrap sets no RUSTFLAGS on Linux, so the config reaches its seed; it
   fingerprints this file, so the next bootstrap rebuilds the seed. A caller
   that exports RUSTFLAGS replaces the config flags and is unaffected.
   `draw_ir_adv_spec` 69/70, `vulkan_lane_session_spec` 2/2,
   `gui_content_renderer_spec` 5/5, `vulkan_async_submission_contract_spec` 3/3
   are identical with and without the flag.
2. *Not fixed; this is the blocker.* On Linux the interpreter runs Vulkan
   compute on the dlopen bridge in `interpreter_extern/gpu.rs` (`VK_STATE`):
   `rt_vulkan_init`, `begin_compute`, `bind_*`, `dispatch`, `submit_*` all have
   bridge handlers and `EXTERN_DISPATCH` is consulted first. The ring exists
   only in the runtime crate (`STATE`, `ASYNC_SESSIONS`), behind the crate's
   `vulkan` feature, which `driver/Cargo.toml` enables for macOS only.
   - default Linux seed: `rt_vulkan_async_session_supported() == 0`, `open`
     returns handle 0.
   - seed built with `--features vulkan`: `supported == 1`, `open` still
     returns 0, because the device was initialised in the bridge and the
     runtime `STATE` has none. Bridge handles (pipeline, descriptor, buffer)
     and runtime ring commands are different handle spaces in any case.

So the defect in this record is unchanged for the interpreter lane: there is no
ring it can reach. Closing it needs one Vulkan owner for both lanes on Linux —
either the bridge grows the ring, or the compute family is routed to the
runtime crate when its `vulkan` feature is on. Both are owner decisions in
`src/compiler_rust`, next to the compiled-runtime init work, and neither was
attempted here.

The spec is tagged `@tag:in-development` with this record as its tracker: it
was written ahead of the implementation and has never been green. Running it by
path reports the honest red verdict. `vulkan_resident_2d.spl` is untouched and
still submits with the blocking call.

Not verified: riscv64 Linux has the same missing flag in the same config file.
