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
