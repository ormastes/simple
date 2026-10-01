# Hosted event acknowledgement lifecycle — 2026-09-10

Status: **WARN — Pure Simple synchronous boundary is implemented and statically
reviewed; asynchronous provider polling and unavailable runtime execution remain
open evidence gates**.

## Change

`src/os/compositor/host_frame_ack.spl` defines typed `Presented`, `Pending`,
`Rejected`, `Skipped`, and `Unknown` evidence. It binds scene revision, extent,
surface epoch, device generation, provider generation, raw provider identities,
and the exact owned external-window content revisions read by the attempt.

`HostCompositor.render_frame_engine2d_evidence()` wraps the existing O1 owner.
It accepts a synchronous Vulkan frame only when the owner advances its frame
generation and reports the exact `synchronous-present-receipt` boundary. That
receipt can acknowledge the synchronous path without falsely setting the
stronger `presenter_released` fact. Future asynchronous receipts must carry a
real presenter-release observation. The legacy boolean
`render_frame_engine2d()` remains for existing callers, but it now routes
through the same typed evidence and commit checks rather than clearing state
inside an untyped render attempt.

The CPU retained lane is two-phase: raster completion yields `Pending` host
buffer evidence; only an exact `present_count = prior + 1` bound to the same
winit window identity and target extent converts it to `Presented`. External
revision markers are fully
validated before any marker changes, then dirty state is cleared in the same
commit. A resize, frame replacement, surface-epoch change, device-generation
change, provider replacement, stale content revision, failed present, or
unknown receipt therefore cannot partially acknowledge the frame. A fallback
compatibility render has no provider receipt, so it restores full damage and
does not acknowledge input.

Each capture is single-use. While it is pending, repeat render requests return
the same CPU/GPU snapshot rather than entering the producer again; resize,
provider replacement, the compatibility boolean entry, and surface close fail
closed. A successful commit consumes the capture token before another dirty
generation can be acknowledged. The captured dirty-rectangle count must remain
exact, and direct compatibility rendering cannot clear a pending capture. These
single-use checks prevent receipt replay or intervening mutations from clearing
newer damage.

The hosted input receipt is committed before `presented_event_id` and
`presented_mutation_revision` advance. Vulkan supplies its exact provider frame
generation; the host-buffer lane supplies the exact winit present generation.
If `host_wm_input_record_presented` rejects either chronology, neither presented
cursor advances.

## Async handoff

`Pending` is intentionally non-acknowledging and carries the owner identities,
external revision snapshot, receipt kind, and frame generation for a future
poll/retire/presenter-release implementation. The synchronous commit refuses
async receipt kinds; a later provider poll must supply that release fact.
`Unknown` is also non-acknowledging. No wait, readback, fabricated receipt, or
Rust/C implementation was added.

## Evidence

- Unit contract: `test/01_unit/os/compositor/host_frame_ack_spec.spl`
- Existing O1 receipt owner: `test/01_unit/os/compositor/compositor_gpu_surface_owner_spec.spl`
- Hosted source contracts:
  `test/03_system/gui/engine2d_gpu_offload_contract_spec.spl` and
  `test/03_system/gui/linux_hosted_wm_live_window_spec.spl`
- Production caller: `src/os/hosted/hosted_entry.spl`

Static review: `git diff --check` PASS. Runtime execution was not repeated after
the delegated package's one focused self-hosted compiler availability failure.
