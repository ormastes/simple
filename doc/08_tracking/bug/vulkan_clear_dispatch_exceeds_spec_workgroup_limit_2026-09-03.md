# Full-surface `clear` exceeds the Vulkan spec-minimum workgroup count at 4K and above

Filed 2026-09-03. Status: OPEN. Severity: HIGH (portability/correctness —
undefined behaviour on a conformant device), but **latent on this host**.

## The defect

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:775-778`:

```simple
me clear(color: u32):
    val total = _i64(self.w) * _i64(self.h)
    val workgroups = (total + 255) / 256
    val dispatched = self._dispatch_framebuffer_checked(self.pipe_clear, pc, workgroups, 1, 1)
```

The whole surface is linearized into ONE dimension, so the X group count grows
with total pixel count:

| Resolution | pixels | groups in X | vs spec floor 65,535 |
|---|---|---|---|
| 800x600 | 480,000 | 1,875 | ok |
| 1920x1080 | 2,073,600 | 8,100 | ok |
| 3840x2160 | 8,294,400 | 32,400 | ok |
| **7680x4320** | 33,177,600 | **129,600** | **1.98x over** |
| **8192x8192** | 67,108,864 | **262,144** | **4.0x over** |

`maxComputeWorkGroupCount[0]` has a Vulkan **required-limits floor of 65,535**.
A device that guarantees only the minimum may reject or silently misbehave.
Both of the project's declared default target dimensions
(`config/graphics/resolution_targets.sdn`) exceed it, and 4K is only 2x under.

**Nothing in the runtime queries `maxComputeWorkGroupCount`.** The only device
limit read anywhere is `max_push_constants_size`.

## Why it is green here

MoltenVK on Apple silicon reports a limit far above the floor, so the dispatch
succeeds and every gate passes. This is a portability bug that this machine
structurally cannot catch — the same class as the C-runtime gap where source
that is well-formed as bytes is nonsense to a compiler.

## The fix, and why it is low-risk in shape

**Every other dispatch site in this backend already uses 2-D 16x16 groups**,
which at 8192x8192 is 512 groups per dimension — comfortably inside the floor.
`clear` is the outlier. Matching the existing 2-D pattern fixes it without
inventing anything.

Additionally the runtime should query `maxComputeWorkGroupCount` (and
`maxStorageBufferRange`, see the sizing inventory) and fail LOUDLY rather than
through `mark_cpu_fallback`, which is a silent downgrade.

## Why it is not fixed in this commit

`clear` is on every frame path, so a wrong change breaks everything. At the
time of filing, `scripts/check/check-engine2d-backend-parity.shs` was
ERRORing (`ERROR — nothing was compared`, exit 2) because several agents were
saturating the GPU with concurrent benchmarks — so pixel-identity could not be
verified. Changing the clear path without that evidence would be exactly the
kind of unverified "obvious" fix that has already produced one 4x regression in
this arc. Fix when the machine is quiet and both gates run clean.

## Verification when fixed

- `sh scripts/check/check-engine2d-backend-parity.shs` -> PASS (not ERROR)
- `sh scripts/check/check-vulkan-2d-bit-diff.shs` -> PASS
- resolution sweep 800x600 / 1080p / 4K / 7680x4320 / 8192x8192, confirming no
  regression at small sizes
- ideally, assert the computed group counts against the 65,535 floor in a unit
  check so the defect cannot silently return

## Source

Found by a delegated defaults/sizing audit; call site verified independently by
reading `backend_vulkan.spl`. Full inventory:
`doc/08_tracking/bug/engine2d_8k_default_sizing_inventory_2026-09-03.md`.
