# Physical Vulkan GUI button qualification (REQ-2D-006 / NFR-2D-002)

The controlled GUI slice is one 16 × 16 button produced by the real widget
theme and DrawIR path. The fixture supplies `ui_pressed=false` and
`ui_pressed=true` as two explicit input states. It does not claim that a
pointer event was dispatched. Each state has a separately pinned source
manifest and a fixed expected widget/theme/material input digest. The input
digest includes the button ID, label, action, and pressed state; changing any
of them requires a fixture revision. The independent pixel
oracle expects opaque RGBA `(39, 113, 199, 255)` for resting and
`(45, 90, 136, 255)` for pressed at every pixel.

On a physical Linux Vulkan host, run the pinned CLI executable and the
authenticated upstream Skia Ganesh Vulkan provider:

```text
sh scripts/check/check-vulkan-2d-qualification.shs <absolute-qualified-executable> <absolute-skia-provider> build/test-artifacts/vulkan_2d/<fresh-id> gui-button
```

`run-gui-button` starts Engine2D and upstream Skia as separate native workers
for each state. Each worker must complete device submission, wait and readback.
The verifier requires two exact 1024-byte frames per state, correct fixture
and input digests, matching physical-device/driver UUIDs within and across
states, a changed output between states, and the independent oracle. The
combined `run.sdn` is written only after both state runs pass. State evidence
and logs are in sibling `<fresh-id>-resting` and `<fresh-id>-pressed`
directories. A missing provider, software Vulkan device, absent readback,
changed source, mismatched UUID, or pixel error blocks or fails the run.

`verify-gui-resting` and `verify-gui-pressed` inspect retained artifacts but
return `status=candidate`; offline artifacts cannot prove fresh device work.
The synthetic oracle unit spec tests source pinning and pixel rejection only.
It is not physical GPU evidence. No physical run was executed on the macOS
development host.
