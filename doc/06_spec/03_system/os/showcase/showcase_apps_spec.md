# Showcase Applications Across Standalone and Window-Manager Surfaces

**Executable specification:** `test/03_system/os/showcase/showcase_apps_spec.spl`
**Status:** Source-ready; production launch/evidence wrappers intentionally fail closed.
**Doc generation:** Blocked by the deployed `bin/simple` parser/checker failure; this manual must be regenerated and accepted with `0 stubs` after that independent defect is repaired.

## Purpose

Verify the same three canonical applications on standalone, host-WM, and
SimpleOS-WM surfaces without accepting demo, source-only, dummy, or synthetic
evidence.

| Application ID | Standalone | Host WM | SimpleOS WM installed identity |
|---|---|---|---|
| `graphics_2d_showcase` | Required | Required | `/sys/apps/graphics_2d_showcase.smf` |
| `web_standards_showcase` | Required | Required | `/sys/apps/web_standards_showcase.smf` |
| `gui_widget_showcase` | Required | Required | `/sys/apps/gui_widget_showcase.smf` |

## Primary Scenario Flow

For each of the nine application/surface combinations:

1. Launch the application through its production catalog action.
2. Verify its canonical installed identity. SimpleOS must read actual bytes from
   the matching `/sys/apps/*.smf` path.
3. Verify a positive process PID owns the visible compositor window and the
   window records the matching application ID.
4. Capture a nonblank same-run framebuffer or device readback with real backend
   provenance.
5. Send input through the production host or QEMU device route.
6. Verify a later semantic state or framebuffer hash changed and remains
   correlated to that input.

The shared executable helper interface is:

- `launch_showcase`
- `require_installed_identity`
- `require_owned_window`
- `require_nonblank_frame`
- `require_post_input_change`

All five currently call `fail(...)`. This is deliberate: missing wrappers must
never turn an unverified surface green.

## Negative Evidence Matrix

The executable spec rejects these substitutes with exact reasons:

| Substitute | Required rejection |
|---|---|
| Source inspection without launch | `source-only` |
| Blank framebuffer | `blank-frame` |
| Equal before/after frame hashes | `unchanged-frame` |
| Dummy or placeholder renderer | `dummy-renderer` |
| Synthetic backend handle | `synthetic-handle` |
| Synthetic input despite changed pixels | `synthetic-input` |

Screenshots may supplement this evidence but cannot replace process ownership,
production input routing, or same-run framebuffer/readback provenance.

<details>
<summary>Executable source</summary>

See `test/03_system/os/showcase/showcase_apps_spec.spl`. The source remains the
authority until `spipe-docgen` can regenerate this mirrored manual with zero
stubs.

</details>
