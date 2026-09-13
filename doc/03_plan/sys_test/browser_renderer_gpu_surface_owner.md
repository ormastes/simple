<!-- codex-architecture: selected acceptance, not executed evidence -->
# Browser GPU owner migration and test plan

Status: selected O1 + B/N2; blocked only on implementation/provider admission.
This plan preserves REQ-GPUUI-002/003/004/005/006/008 and NFR-GPUUI-004/005/006.
No synthetic provider result can admit a device row.

## Deterministic owner tests

Extend the existing `render_surface_contract_spec.spl`,
`render_surface_state_spec.spl` and `render_surface_event_damage_spec.spl`
under `test/01_unit/lib/{common,gc_async_mut}/gpu/` after API selection:

- Two equal-size surfaces on one device: closing or resizing A never releases
  B's engine, resources, pending event or submitted lease; shared session stays
  alive until its actual last owner releases it.
- Reject wrong-device/session/surface/slot-generation receipts before mutation;
  positive scalar fields alone never admit a receipt.
- Submit three frames, return bounded backpressure for frame four, physically
  retire a slot after compute completion and presenter release, then submit
  frame four without device idle. Force
  out-of-order completion and verify only the contiguous present prefix is
  acknowledged. No accepted/submitted/presented cursor is conflated.
- Submit failure before acceptance returns the recording reservation and
  restores its pending damage; ambiguous acceptance retains its exact owner.
- A compute fence cannot release an image still read by present/capture. Ring
  wrap preserves correct content revision and local damage on every image.
- Pointer, resource-completion and timer events use the same coalescer. No-damage
  events allocate/submit nothing; newer wakeups remain effective after resize.
- Interleave two producers' independent document/event counters on one display
  surface. The output owner assigns ordered frame sequence; one producer's
  numerically larger counter cannot stale-reject another producer's new event.
- Resize closes admission; identical completed resize is stable. Device loss
  with in-flight frames invalidates publication immediately without requiring
  a fence that may never signal, and holds resources until recovery evidence.
- Duplicate close/loss/retirement cannot double-release or create a new generation.

Device-free provider fixtures test owner control flow only. They must be labeled
as injected test data and cannot enter `gpu_present_receipt_admitted` production
evidence or timing collection.

The production host's owner-issued epoch/count damage-prefix prerequisite now
has focused source specs:
`test/01_unit/os/compositor/dirty_rect_checkpoint_spec.spl` covers later
overlapping damage, replay, clear/readd, malformed checkpoints, and epoch
exhaustion;
`test/01_unit/os/compositor/host_compositor_pending_damage_spec.spl` enters the
real software Engine2D render/evidence/acknowledge path. The latter injects only
presenter sequence observations and cannot establish physical presentation.
Both remain `TEST_BLOCKED` until an admitted general Pure Simple test runner is
available. They do not satisfy the bounded async GPU ring or live release gates.

SPipe owner checks must preserve semantic damage identity: rectangle count,
bounding-box equality, and spatial subtraction cannot prove which input
revision a present consumed. Hold an older frame, add identical or overlapping
new damage, then acknowledge the old frame and inspect the pending successor.
Also clear and re-add at the same count to test stale-checkpoint rejection.

## Production call-path coverage

Extend `test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl`
and `browser_session_event_retention_spec.spl` to exercise the selected real
display adapter. Tests must invoke the same host/compositor entry that performs
resource consumption and dirty acknowledgement in production.

Add `test/03_system/app/browser/feature/gpu_surface_owner_spec.spl` after the
provider is available. The selected O1 owner is the host compositor; reserve
manual helpers `step("Open two browser surfaces")`,
`step("Submit pointer resource and timer damage")`,
`step("Retire and present a bounded frame ring")`,
`step("Resize and recover device loss")`, and
`step("Close only the owning surface")`. Setup helper:
`open_browser_surface_pair`; checker helper: `assert_surface_owner_receipts`.
Unimplemented setup/provider branches use `fail(...)`, never placeholder PASS.

Each step checks real owner identities, token chronology and resource counters.
For loss injection, the provider reports an actual controlled loss/recovery
outcome; manually setting model fields is not production loss coverage.
Generate its manual in `doc/06_spec/03_system/app/browser/feature/` with the
admitted SPipe generator. Do not hand-author a generated PASS manual.

## Hardware and compatibility gates

After canonical runtime admission, the three-frame test must observe bounded
nonblocking polls, exact command retirement, presenter image release and a
fourth accepted frame with zero steady CPU waits/device-idle/readbacks. Verify
allocation stabilization, no cross-surface release, and one exact post-timing
capture against the existing pixel API, including embedded image/iframe content.

Keep `BrowserRenderer` and `BeRenderResult` signatures and pixel results pinned
by existing browser renderer specifications. A completed capture cannot satisfy
a display receipt assertion. No Chrome/C comparison is admitted by this plan.

Run every criterion once on the final changed implementation, at most two
focused repair cycles in this escalation. Static documentation checks do not
replace production, device or SPipe execution.

## Canonical Vulkan lifetime acceptance, 2026-09-14

**Planned / TEST_BLOCKED**, not executed evidence. The
[driver-owner migration](../../05_design/vulkan_canonical_driver_owner_migration.md)
must implement the complete production cut before these cases can pass.
The framebuffer-only candidate and its new test were removed. Existing
`vulkan_session_release_identity_spec.spl` and
`vulkan_session_release_teardown_spec.spl` construct positive fields and call
`retain`; replace those fabricated-authority expectations with issued references
or explicit rejection as part of the code migration.

Implement focused lifecycle specs under `test/01_unit/lib/gpu/engine2d/` and
production cases under `test/02_integration/rendering/`. A device-free adapter
supplies controlled native outcomes to the same private owner transitions.
Production must not export that adapter or caller-selected identity admission.

| Case | Sequence and decisive assertion |
|---|---|
| Forgery | Set every public scalar positive without an issued record; validity/retain/allocation/command/release reject with zero native calls |
| Retained copies | Init A, retain into B, copy A into C, release A; C is revoked, B operates, and pipelines remain until B and its resources release |
| Duplicate release | Release the same reference/surface/command through copied values; at most one native release and unrelated references stay valid |
| Exact framebuffer | Vary handle, width, height, bytes, usage including `0x10`, kind, owner epoch and reference/surface generations individually; reject before mutation |
| ABA | Reuse the same native handle and slot after release; old lease cannot submit/free, while the new generation remains live |
| Exhaustion | Fill each reference/surface/dependency table and exhaust generations/nonces; reject before allocation, never wrap or reuse an exhausted slot |
| Partial init | Fail each shader/pipeline acquisition and cleanup result; release only acquired resources and retain every unresolved handle |
| Failed release | Fail buffer/descriptor/pipeline release; dependent session remains pinned, its slot cannot recycle, and teardown success is not published |
| Copy before record | Copy A to B with local command zero, record through A, close B; canonical pending work is observed and resources stay pinned |
| Copy after record | Copy after recording, retire through A, flush/close B; no second native end/submit/discard or descriptor release |
| All producers | Repeat both copy cases for primitive, image, packed font and unpacked font paths; the same canonical owner receives actual producer calls |
| Pooled dependencies | Replace an atlas/image/parameter allocation while a recording reads it; old storage stays pinned and stale copies cannot free the replacement |
| Two surfaces | Interleave A/B acquisitions and recording, close A, continue B; B retains its exact pools, pipelines, session and pending work |
| Owner thread | Foreign-thread entry rejects before registry/native mutation; creating-thread handles remain usable |
| Mutex failure | Failed lock performs no native action; failed unlock quarantines ownership and publishes no success |
| Admission remains off | Exact managed framebuffer membership still leaves context/async false until the native port exists; no full DrawIR serialization on the unavailable path |

The injected trace must distinguish allocation, recording, submit, compute
completion, destruction and presenter release. Assert actual adapter calls and
exact resource identities, not counters set by tests after no-op operations.
Injection proves transitions only; it cannot admit a live Vulkan row.

Reserve `step("Retain two managed Vulkan surfaces")`,
`step("Copy a backend before and after recording")`,
`step("Reject stale framebuffer and recording leases")`, and
`step("Close only the canonical surface owner")`, with helpers
`open_managed_vulkan_surface_pair`, `assert_managed_vulkan_lifetimes`, and
`assert_vulkan_native_call_counts`. Unimplemented setup/provider branches must
`fail(...)`. Generate a mirrored manual only through admitted SPipe execution.

After device-free execution, run the same production paths on admitted Pure
Simple and capture controlled output with binary/source identity. Native
context, presenter and performance gates remain separate. Run each changed
criterion once, at most three fix/check cycles for this unit. Source matching
does not establish copy semantics, mutex behavior or native lifetime execution.
