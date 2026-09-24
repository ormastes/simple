# Physical Vulkan 2D qualification contract

Executable source: `test/03_system/app/ui/feature/physical_vulkan_2d_qualification_spec.spl`

Trace: REQ-2D-003, REQ-2D-005, REQ-2D-006, NFR-2D-002.

## Scenario: controlled rectangle admission

1. Hash the pinned `controlled_opaque_rect_v1.sdn` source independently of backend receipts.
2. Require a complete Engine2D Vulkan capture and a complete optional upstream Skia Ganesh Vulkan capture for the same source. A missing capture returns `blocked` with its backend named.
3. Reject a software Vulkan device even when a caller supplies nonzero handles
   and counters. Reject missing, malformed, all-zero, or unequal reported
   Vulkan device/driver UUIDs; identical model names alone do not identify
   the same physical device. Differently formatted display names and driver
   strings remain diagnostic when the structured UUIDs and physical type agree.
4. Require the selected final resource, completed submission/fence/readback and exact 16 × 16 pixel domain before comparing canonical RGBA. Missing metadata returns `blocked`; a pixel mismatch returns `fail`. Independently rasterize the pinned rectangles and fail matching but wrong backend pixels against that oracle. A correct byte match is a `candidate` until trusted device provenance is independently checked.
5. Preserve any producer degradation as a blocked scene, including an unsupported Web or GUI state.

The pinned-source loader parses the exact hashed rectangle commands into the
shared GPU DrawIR. Separate Engine2D and Skia adapters require their completed
owner-bound captures and selected-device UUIDs before assembling candidate
artifacts. The pair gate compares structured UUIDs and physical device type;
human-readable device and driver labels remain diagnostics.

The current executable scenarios cover blocked outcomes only. This manual does not certify the optional native provider, a physical Linux device, or Web/GUI corpus parity. The qualification plan and required capture fields are in `doc/03_plan/sys_test/physical_vulkan_2d_controlled_rectangle.md`.
