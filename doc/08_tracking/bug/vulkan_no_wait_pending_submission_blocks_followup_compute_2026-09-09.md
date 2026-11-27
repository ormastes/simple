# Vulkan no-wait submission blocks the next compute command
## Fixed 2026-11-13 — live-device acceptance met on the interpreter lane

The acceptance test below passes on a real device (NVIDIA GB10) since the
interpreter's Vulkan bridge gained its own submission ring. Evidence, design and
what is still not covered are in the last section, "2026-11-13 lane vk-ring".

**Status:** FIXED (interpreter lane; residuals listed in the last section)
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

## 2026-11-13 lane vk-ring — bridge ring implemented; acceptance spec green on GB10

Host: Linux aarch64, DGX Spark, `NVIDIA GB10|vendor=000010de|device=00002e12|
driver=912b4080|api=00404138`. Base release/1.0.0 `9100f50e680`. Both seeds
were built from that commit with `env -u RUSTFLAGS cargo build --release --bin
simple` (an exported `RUSTFLAGS` drops `--export-dynamic`; the first build here
had 0 exported `rt_vulkan_*` symbols for that reason and was discarded).

| seed | sha256 (first 16) | size |
|---|---|---|
| base, unmodified tree | `a01a6e3df5426709` | 66,617,744 |
| with the bridge ring | `35aec8193c70d864` | 66,639,000 |

### What changed

Blocker 2 of the previous section is closed by giving the bridge its own ring
rather than routing the interpreter to the runtime crate:
`src/compiler_rust/compiler/src/interpreter_extern/gpu_vulkan_async_ring.rs`.

- **Shared protocol.** `runtime/src/vulkan_async_protocol.rs` (slot state
  machine, admission window, contiguous receipt publication, status values) is
  now a public module of the runtime crate and is used by both owners. The
  runtime's own ring is otherwise untouched; its injected-device harness still
  passes (23 tests).
- **Ownership.** A submitted command buffer and its `VkFence` sit in the ring's
  own table until `retire` sees the fence signaled (`vkGetFenceStatus`, added
  to the bridge's function table) or `recover` sees device idle. They are never
  in `quarantined_commands` or `live_fences`, so neither `wait_idle` nor the
  caller-fence API can free them underneath the ring. Session, token and
  caller-visible fence identities come from one monotonic counter and are never
  reused; a raw `VkFence` value can be recycled by the driver.
- **Retention.** The pipeline, descriptor sets and buffers recorded into a
  submission are refused for `destroy_pipeline`, `destroy_descriptor_set`,
  `bind_buffer` (descriptor rewrite) and `free_buffer` until that submission is
  released.
- **Admission.** While a session is open the bridge refuses `begin_compute`,
  `discard_command`, `submit_and_wait`, `submit_and_wait_fence`,
  `submit_no_wait`, `wait_idle`, `select_device` and `shutdown`: the set
  the runtime gates on `async_compute_session_active`, plus `submit_and_wait`.
- **Fail-closed close.** `close` answers 1 only with nothing in flight and with
  created == released for both command buffers and fences.
- **`rt_vulkan_discard_command`** was a constant-0 stub in the bridge. It now
  frees a recorded, unsubmitted command.

The compute path submits with a fence only. It uses no semaphores, so there is
no semaphore lifetime to report.

### Evidence (all serial, one spec per process, exit code read directly)

| spec | base seed | ring seed, 10 runs |
|---|---|---|
| `vulkan_async_ring_live_device_spec` | 1 example, 1 failure | 10/10: 1 example, 0 failures; then 10/10: 2 examples, 0 failures with the release-path example below |
| `vulkan_async_session_backed_spec` | 2 examples, 0 failures | 10/10: 3 examples, 0 failures (one example added) |
| `vulkan_async_session_lifecycle_contract_spec` | 5 examples, 1 failure | 10/10: 5 examples, 1 failure (unchanged) |
| `vulkan_async_submission_contract_spec` | 3 examples, 0 failures | 10/10: 3 examples, 0 failures |
| `vulkan_lane_session_spec` | 2 examples, 0 failures | 10/10: 2 examples, 0 failures |

Flakes: 0 in 60 invocations. The lifecycle failure is the same example on both
seeds, "keeps every async forward visible to the dual-lane ABI audit"; it reads
`src/runtime/runtime_dynload.c` and is not touched by this change.

The live-device spec lost its `@tag:in-development` tag and gained one step:
with the ring open, a direct `begin_compute` answers 0 and `bind_buffer` on the
descriptor set of an unretired submission answers false.

It also gained a second example for the release paths that are not `retire`,
none of which the first example reaches: `close` with a command that was
acquired but never submitted answers 1; with two submissions unretired and a
third recording, `cancel` answers 1 and `acquire` then answers CLOSED, `close`
drops the recording slot and answers 0 with `in_flight` 2, `recover` answers 1
with `in_flight` 0 and `published_sequence` still 0 (no receipt is
manufactured), and the following `close` answers 1 (accounting balanced), after
which a direct `begin_compute` and `discard_command` succeed.

No `bin/simple` is deployed in the main clone on this host, so the untagged
spec was not run against a deployed binary. A seed built before this commit
answers `supported == 0` and the spec is red there; whole-suite runs on a GPU
host need a seed from this commit or later.

Ten neighbouring Vulkan specs, one run per seed, same verdict and same failing
set on both: `vulkan_resident_2d_spec` 3/3, `vulkan_submit_no_wait_backed_spec`
2/2, `vulkan_sffi_completion_recovery_contract_spec` 4/4,
`vulkan_debug_session_conformance_spec` 1/1,
`vulkan_vm_executor_conformance_spec` 2/2, `gpu_resident_vulkan_slice_spec`
1/1, `gui_content_renderer_spec` 5/5, `draw_ir_adv_spec` 69/70,
`backend_vulkan_font_spec` 17/22, `vulkan_sffi_provider_parity_spec` 0/4.

Rust: `cargo test --release -p simple-runtime --lib vulkan_async_protocol` 14
passed; `-p simple-compiler --lib interpreter_extern` 460 passed.

### Leak check, 30,000 cycles on the device

One process, capacity-3 ring, 30,000 x (acquire, record, submit, poll to
completion, retire) against a control of 30,000 x (`begin_compute`,
`submit_and_wait_fence`, `destroy_fence`) on the same seed:

| iteration | ring VmRSS kB | direct VmRSS kB |
|---|---|---|
| 3,000 | 333,956 | 333,948 |
| 15,000 | 328,016 | 325,964 |
| 18,000 | 330,116 | 328,064 |
| 30,000 | 330,116 | 328,064 |

Ring: 0 failures, `published_sequence` 30,000, `close` 1 (so 30,000 fences and
30,000 command buffers created and released), descriptor destroy and device
shutdown clean. RSS does not grow over the last 12,000 cycles in either lane.
The dips are host reclaim on a shared box, present in the control too. RSS
cannot see a leaked driver object by itself; the `close` accounting is the
ownership evidence, RSS is the supporting one.

### Not covered

- The **compiled runtime's** ring has still not run on a live device. The Linux
  seed is built without the runtime crate's `vulkan` feature, so JIT or natively
  compiled code has no Vulkan device there at all.
- Unknown-completion (`VK_ERROR_DEVICE_LOST` class) on real hardware. The
  bridge keeps the command and fence owned and closes admission on that path,
  but it was not provoked. It stays with the injected-device tests, which
  exercise the runtime owner, not the bridge.
- `snapshot`, `snapshot_word` and `abandon_device` are not served by the bridge
  ring. They reach the runtime crate, which answers -1 for a bridge session, so
  `telemetry()` is empty for an interpreter-lane ring.
- The bounded wait in `acquire` holds the bridge mutex (at most the session
  timeout, 1 s ceiling). The runtime owner waits outside its registry lock.
- `vulkan_resident_2d.spl` still submits with the blocking call. Adopting the
  ring there is a separate change.
- riscv64 Linux: the `--export-dynamic` gap noted above is unverified.
