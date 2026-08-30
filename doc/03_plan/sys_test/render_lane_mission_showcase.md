# Render Lane Mission Showcase Acceptance Plan

## Scope

The mission gate admits four independent capture artifacts—WM, GUI, Web, and
Engine2D—only when one strict Vulkan receipt binds each artifact hash and the
same live guest serial transcript proves the production lanes. The contract is
implemented by `scripts/check/check-render-lane-mission-showcase.shs` and
exercised by `test/03_system/check/render_lane_mission_showcase_spec.spl`.

Synthetic fixtures exercise the gate's decision logic; they never count as
live-guest rendering, allocation, or Vulkan execution evidence.

## Requirement Traceability

| REQ | Description | Executable SSpec | Cases | Coverage |
|---|---|---|---:|---|
| REQ-RLMS-001 | Four captures are regular, sufficiently sized, and distinct | `test/03_system/check/render_lane_mission_showcase_spec.spl` | 2 | Contract |
| REQ-RLMS-002 | Guest serial proves all production lanes and rejects degradation | `test/03_system/check/render_lane_mission_showcase_spec.spl` | 2 | Contract + live guest blocked |
| REQ-RLMS-003 | One Vulkan receipt binds all four capture hashes | `test/03_system/check/render_lane_mission_showcase_spec.spl` | 2 | Contract |

## Execution Order

1. Run the isolated SSpec contract with an admitted pure-Simple test runner.
2. Supply an admitted self-hosted binary, guest image, and QEMU/container
   producer receipts to the capture producers.
3. Retain the four capture files, guest serial log, Vulkan receipt, producer
   receipts, binary, image, and measured allocation receipt.
4. Run once:

   ```sh
   WM_CAPTURE=<wm> GUI_CAPTURE=<gui> WEB_CAPTURE=<web> ENGINE2D_CAPTURE=<engine2d> \
   GUEST_SERIAL_LOG=<serial.log> VULKAN_RECEIPT=<vulkan.env> \
   QEMU_PRODUCER_RECEIPT=<qemu.env> CONTAINER_PRODUCER_RECEIPT=<container.env> \
   ADMITTED_SIMPLE_BIN=<simple> GUEST_IMAGE=<image> ALLOCATION_CAP_BYTES=<bytes> \
   sh scripts/check/check-render-lane-mission-showcase.shs
   ```

Pass requires unique receipt fields, status `pass`, four distinct image capture
hashes, a Vulkan submit/fence/readback, full producer/binary/image/serial hash
binding, and a measured allocation peak not above `ALLOCATION_CAP_BYTES`.
Missing binary, QEMU/container, capture, marker, receipt, or allocation measure
is BLOCKED/FAIL—not a skip or a completed row.

## Blocked Live-Guest Handoff

Owner: pure-Simple bootstrap owner. Final reviewer: separate highest-capability
Codex reviewer. Prerequisite: an admitted self-hosted full CLI that can build
the guest and execute the capture wrappers without seed fallback. Retain
`build/bootstrap/native_cache/` and all existing capture-wrapper logs; resume
with the command above after producing the four real artifacts.

# TODO: [rendering][P0] BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command.
