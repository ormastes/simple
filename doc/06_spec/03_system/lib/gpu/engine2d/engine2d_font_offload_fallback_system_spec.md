# Engine2D configured-font offload fallback (system lane)

**Category:** Runtime
**Status:** In Progress — fail-closed, blocked on a qualified pure-Simple runtime
**Source spec:** `test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl`
**Requirements:** REQ-E2DFONT-001, REQ-E2DFONT-002, REQ-E2DFONT-003

## Purpose and Audience

Proves, through a real compiled binary, that Engine2D's configured-font
execution walks its documented backend preference order, records one ledger
entry per attempt, and always lands on a surface that was actually painted.

Audience: anyone changing `Engine2D` backend routing or the font offload lane.

## Scope and Preconditions

Requires an admitted pure-Simple runtime, supplied as
`SIMPLE_QUALIFIED_RUNTIME=/abs/path/to/simple`. The Rust bootstrap seed is
explicitly **not** acceptable evidence for this lane — the admission gate reads
the binary's `--version` banner and rejects it if it self-identifies as a seed.

Without an admitted runtime these scenarios **fail**. They never skip and never
pass vacuously; that is deliberate, so the lane cannot look green while proving
nothing.

The in-process shape of this behaviour is already covered by
`test/01_unit/lib/gpu/engine2d/font_runtime_config_spec.spl`. This lane exists
for what a unit spec structurally cannot observe: the lowering and native
runtime seam.

## Primary Workflow

| Step | Action |
|------|--------|
| 1 | Admit a pure-Simple runtime and native-build the fallback probe |
| 2 | Execute the probe |
| 3 | Validate the emitted attempt ledger against the documented preference order |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Attempt ledger | `font_execution_attempts()` — one `backend:outcome` entry per target tried, in order |
| Fallthrough | An attached backend that cannot service the batch records `failed`/`unavailable` and yields to the next candidate |
| Terminal cpu | `cpu:success` is the documented last resort and must terminate the ledger |

## Scenarios

### Reports the drawn text as painted after falling through to cpu — REQ-E2DFONT-001

The suggested-policy draw returns success even though the attached CUDA backend
could not service the batch.

### Records one ledger entry per attempted backend, in preference order — REQ-E2DFONT-002

The ledger equals
`cuda:failed,metal:unavailable,opencl:unavailable,vulkan:unavailable,rocm:unavailable,cpu:success`
and terminates on the `cpu:success` last resort.

### Walks the same order under the preferred policy — REQ-E2DFONT-003

Raising the policy from `Suggested` to `Preferred` changes neither the outcome
nor the order.

## Related Specifications

- `test/01_unit/lib/gpu/engine2d/bitmap_font_offload_spec.spl` — in-process offload shape
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl` — uninitialized-backend fallthrough

## Evidence and Provenance

Fence for the routing repair landed in `b10f1b4309c`. **No runtime evidence has
been produced for this lane as of 2026-08-16**: no qualified pure-Simple runtime
exists on the reference machine. A fleet sweep of 1099 binary instances (19
unique by md5) found all five self-hosted artifacts non-functional. Tracked in
`doc/08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`.

## Recovery and Troubleshooting

| Failure text | Meaning |
|---|---|
| `no qualified pure-Simple runtime admitted` | Toolchain blocker, not an Engine2D defect |
| `is the Rust bootstrap seed` | A seed was offered; deploy a self-hosted binary |
| `failed to native-build` | The admitted runtime cannot compile at all — repair it before reading the assertions |

## Compatibility and Limitations

Asserts routing and the attempt ledger only. Makes no claim about glyph raster
correctness, GPU residency, presentation, or performance.
