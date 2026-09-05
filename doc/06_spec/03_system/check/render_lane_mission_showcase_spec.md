# Render Lane Mission Showcase Admission Specification

> Status: authored acceptance companion; the canonical docgen mirror is pending
> an admitted self-hosted Simple CLI. This document does not claim live-guest
> execution.

## Purpose and audience

For operators admitting a mission-critical SimpleOS render showcase. It tells
them exactly what evidence the production gate consumes and what it rejects.

## Preconditions

- Four independently captured regular files: WM, GUI, Web, Engine2D; each is
  at least 4096 bytes and has a distinct SHA-256.
- One live guest serial log containing first-frame, Engine2D, live-browser, and
  production-lane markers with no degraded/fault markers.
- One receipt containing `status=pass`, `backend=vulkan`, and all four hashes.
- QEMU/container producer receipts, an admitted self-hosted binary, guest image,
  and guest serial log whose SHA-256 values are each bound by that receipt.
- An operator-supplied allocation cap and a positive measured peak no greater
  than that cap.

## Operator workflow

1. Set all capture, producer-receipt, admitted-binary, guest-image, serial-log,
   Vulkan-receipt, and `ALLOCATION_CAP_BYTES` variables named in the test plan.
2. Run `sh scripts/check/check-render-lane-mission-showcase.shs`.
3. Accept only `render_lane_mission_showcase_status=pass`.

The executable scenarios in
`test/03_system/check/render_lane_mission_showcase_spec.spl` cover a valid
synthetic contract fixture, duplicate captures, a non-Vulkan receipt, a
faulted guest transcript, and an unbound capture hash.
They are not a substitute for Step 1 live evidence.

## Compatibility and limitations

This is a container/QEMU headless admission contract. It does not prove
physical scanout, and it remains blocked until a self-hosted compiler produces
the guest/capture artifacts. The Rust seed and a receipt fabricated from test
fixtures are forbidden evidence.
