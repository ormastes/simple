# HostCompositor aggregate GPU scheduler package

Status: **FAIL for production integration; Astra removed the candidate.**
The provider boundary is structurally incomplete, not merely awaiting runtime
evidence. The sections below retain the Sol review as historical evidence;
their candidate source, test, and manual paths were removed in the Astra pass.

## Boundary delivered

`src/os/compositor/host_compositor_gpu_scheduler.spl` is a candidate aggregate
scheduler owned by `HostCompositor`. It can open a B/N2
`VulkanAsyncSubmissionSession` only after a provider-owned
`window-swapchain` receipt proves a real device, swapchain, no-readback
presentation, and known completion. Software, headless, compute-only, and
readback receipts remain detached.

Its candidate API can return `HostGpuRecordingLease` values from one session.
Every command, submit, poll, and retire call validates scheduler identity,
surface id/epoch, physical device generation, slot generation, and opaque
provider token. The host receives `HostGpuProgress` from those calls; it does
not infer progress from counters or fabricate receipts.

Resize, surface close, binding replacement, and scheduler close require exact
idleness. Resize is surface-local, so a child cannot drain another child. A
completion-unknown result closes admission and retains ownership in the
provider session. The normal path has no `wait_idle`, readback, or fabricated
present/release operation.

`HostCompositor` owns the scheduler and exposes lease/progress forwarders, but
no production child, DrawIR operation, event loop, or presenter calls them.
The scheduler opens a new async provider session after observing only a
completed synchronous `VulkanFrameReceipt`; that receipt does not prove the
new session shares the exact DrawIR device/session. Its recording path also
does not bind DrawIR buffers, descriptors, immutable slot resources, or output
images. The existing synchronous O1 owner therefore remains the only live
path, and this package is a dead facade rather than package-2 integration.

## Sol review cycle 2 verdict

The cycle-1 blocker persists and cannot be repaired inside these five files:

- no provider-issued non-owning shared-session/device lease exists for the
  compositor and child surfaces;
- session and binding generations are not present in the child lease, and the
  local constant scheduler id is not opaque provider authority;
- provider-authoritative resource binding, command recording, compute
  dependency, and exact presenter-release receipts are absent;
- the boolean synchronous frame path cannot represent accepted, pending,
  rejected, completion-unknown, or presenter-release outcomes;
- event dirty-state acknowledgement occurs only after synchronous present and
  cannot be moved to async publication without the missing typed receipt path;
- resize, replacement, loss, and close have only local idle counters and no
  end-to-end recovery/presenter ownership proof.

Opening the candidate session from the current frame path would collide with
legacy/direct compute ownership and risk disabling subsequent rendering. Lazy
attachment from an already-completed receipt would only disguise that defect.
Per the two-cycle review rule, this requires Astra/provider-interface
escalation; no third Sol patch cycle is appropriate.

## Evidence

- `test/02_integration/lib/gpu/host_compositor_gpu_scheduler_spec.spl`
  covers only receipt-shape rejection/admission, 3–16 capacity and timeout
  policy, and rejection before a session is opened. It does not cover the
  production lifecycle or any REQ-SURFACE requirement end to end; misleading
  `@cover 80%` and requirement-acceptance annotations were removed.
- `bin/simple check --syntax-only ...` was attempted but the clean worktree
  has no admitted cached self-hosted check worker; the bootstrap seed refused
  to provide semantic check evidence. This is an environment/toolchain WARN,
  not a source PASS.
- `bin/simple run src/app/optimize/main.spl
  src/os/compositor/host_compositor_gpu_scheduler.spl --full --level=O3`
  completed in review cycle 2 with 88 low/medium MIR advisories and no general
  source-pattern findings. The command explicitly reported that `bin/simple`
  is a Rust bootstrap seed, so this is advisory optimizer output, not admitted
  Pure Simple semantic or performance evidence.
- The one targeted spec execution was attempted with
  `SIMPLE_LIB=src bin/simple test ... --mode=interpreter`; the test runner
  timed out under the bootstrap/daemon guard before executing a scenario, so
  no runtime PASS is claimed.

## Explicit non-claims

This package does not claim live Vulkan execution, capacity recycling,
production scheduler integration, presenter release, event acknowledgement,
Chrome parity, or C/Simple performance parity. Those gates require provider
integration and hardware evidence described in
`doc/09_report/b_n2_o1_provider_bridge_astra_review_2026-09-09.md`.

## Astra decision and recoverability

The exact five-file candidate was archived locally at
`build/bridge-review/b_n2_o1_rejected_host_scheduler.patch` before removal.
`host_compositor_core.spl` is restored to its committed content; the untracked
scheduler, candidate-only test, and manual are removed. No Rust/C file changed.
The existing synchronous O1 production owner and standalone B/N2 APIs remain.

The decisive provider inspection is
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_async_offer.rs`:
`rt_vulkan_async_session_create_with_wait` receives only capacity and timeout,
selects the runtime's current global device, and excludes existing direct
compute commands. Its returned handle cannot attest a caller's specific
VulkanSession, framebuffer, swapchain, or surface binding. The opaque slot
token does protect the provider's slot generation; the rejected scheduler's
locally assigned generation is neither required nor sufficient evidence of it.
`vulkan_async_submission.spl` exposes no bound-session admission or
presenter-release operation. Adding fields with positive numbers would not
create those provider guarantees.

The candidate's `command` method only retrieved the command handle. It never
recorded DrawIR work, bound a descriptor/output image, or established a
write/read dependency. Its `acquire` also rejected locally when full, skipping
the provider's selected N2 pressure observation, while its retired lease and
closed surface arrays grew without bound. These defects reinforce that the
candidate is not an implementation of the selected production owner.

The actual final acknowledgement is one layer farther out than the proposed
facade: `src/os/hosted/hosted_entry.spl` advances `presented_event_id` and
`presented_mutation_revision` after boolean `render_frame_engine2d` success.
That caller, the compositor's dirty state, and external content consumption
must all move to the same validated present-release prefix. Returning true
for pending work at the old boolean boundary would falsely acknowledge input;
returning false would invoke compatibility rendering or stop evidence mode.

The concrete shared-session port, receipt identities, owner chain, and
production acceptance cases are frozen in the architecture document's
**Provider port required before production connection** section. This is a
design contract, not an implemented capability or a new alternative selection.
The next implementation must include that real port and its consumers in the
same admitted chain; another receipt-to-session wrapper is not a valid retry.

Removal verification compares the tracked host file with Git HEAD and checks
that candidate source/test/manual imports are absent. No semantic, GPU, or
performance PASS follows from this removal. The unavailable self-hosted worker
and already-recorded optimizer attempt are not rerun: no optimized `.spl`
change remains.

Recommended commit set: this report, the linked architecture refinement, and
the linked agent task-plan update only. Do not commit the local recovery patch.
