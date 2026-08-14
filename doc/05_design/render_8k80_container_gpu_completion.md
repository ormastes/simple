<!-- codex-design -->
# Detail design: container/GPU 8K80 completion

## Interfaces

- Checker: `scripts/check/check-render-perf-8k80-container.shs`
- Outputs: `drawir_receipt`, `producer_receipt`, `aggregate_receipt`
- Status enum: `pass`, `failed`, `blocked`, with aggregate extension
  `blocked-physical`.
- Test helpers: `given_valid_drawir_receipt`,
  `given_valid_producer_receipt`, `given_physical_receipt`,
  `run_container_aggregate`, `check_aggregate_status`.

## A4

Require an admitted Stage 4 compiler. Build the canonical CPU DrawIR benchmark
into a fresh cache/output, hash it, execute it directly under `/usr/bin/time`,
and translate stdout plus max RSS into `drawir_receipt`. Validate the benchmark
source constants, including 256x128 damage, so stale prose cannot redefine the
workload.

Build the two immutable prepared damage plans before the timed loop. Bind each
plan to the complete composition payload, 7680x4320 dimensions, exact damage,
and its revision content identity. The prepared executor must reject a crossed
identity or dimensions before mutating Engine2D and retain the exact per-frame
2 considered / 512 culled / 2 rendered / 512 skipped counters.

## A5

Add a strict semantic-producer entry that renders a changing revision through
the existing Web/GUI semantic owner and DrawIR into Engine2D Vulkan. It accepts
no software fallback and emits requested/selected backend, device identity,
readback source and handle, checksum, revision, completion, timings, and RSS.
It emits `producer_receipt_warmup_count=1` and
`producer_receipt_sample_count=60`; p50/p95 are calculated over those 60 timed
changing revisions, never over the warmup.

The selected workload is `web-semantic-retained-damage-v1`: a stable full
background plus one changing semantic element at (128,128), 256x128. Perform a
full-frame strict Vulkan seed before timing. Each timed revision includes the
canonical Web layout-to-DrawIR lowering and only the retained-damage submit and
fence; readback stays outside timing. Accept only when the final retained
device readback equals an independently full-rendered strict Vulkan checksum
oracle, with stable device/handle, exact submit/fence counts, and no fallback.

## Container owner

Use explicit GPU selection and driver capabilities, bounded timeout/memory/CPU,
`--cap-drop=ALL`, and `no-new-privileges`. Qualify CUDA with actual submit/
readback and Vulkan with actual device-origin readback. Build artifacts once;
execute cached artifacts directly.

Prepare the campaign image with the dedicated setup wrapper. It rejects a
mutable CUDA base reference, builds from `NAME@sha256:...`, checks
`vulkaninfo` and `/usr/bin/time`, rejects an installed Mesa Vulkan ICD, and can
write an atomic image receipt containing the immutable Docker image ID. Its
hardware-free contract mode is suitable for ordinary CI. The separate GPU mode
requires NVIDIA Toolkit injection with exactly the superset
`compute,utility,graphics`; Mesa enumeration cannot satisfy that check.
Both image and live-GPU checks bound memory, CPU, and process count in addition
to disabling networking, dropping capabilities, and enabling no-new-privileges.

## Aggregator

Parse a fixed key allowlist, reject duplicates and unknown/missing values,
correlate source/artifact/workload/device hashes, then publish atomically. Its
self-test covers valid software receipts yielding `blocked-physical`, complete
physical promotion, missing/malformed input, hash/workload mismatch, fallback,
unknown completion, zero metrics, timed readback, and p95 over budget.

For A6 source readiness, strict window presentation consumes the Engine2D owner
returned by strict submission and returns a new owner-result envelope. It
requires completed `window-swapchain`, device-present, known completion, zero
readback, and positive framebuffer/device/swapchain identities. These fields do
not assert scanout pixels; A7 still requires an independent physical receipt.
Its receipt binds the same semantic owner, DrawIR owner, sparse damage geometry,
seed mode, adjacent revisions, and end checksum as A5. The hardware wrapper
also requires A5's independent full-Vulkan oracle parity before admitting the
window evidence.

The A4/A5 build shares one source-matched native cache across its three native
entries and retains the semantic-window artifact plus build log/hash in the
immutable evidence manifest. This reduces repeated compilation only. A4
separately caches immutable prepared DrawIR planning outside timing; A5
deliberately keeps semantic layout inside every timed revision. Neither caches
mutable Engine2D state. The physical wrapper
executes the cached artifact and validates the separate capture receipt through
`--validate-physical` before reporting physical readiness.

The admission-only display command reuses the canonical parser for a connected
EDID-bearing output whose starred 7680x4320 mode is at least 80 Hz; it does not
run the legacy Rust performance row. Before execution, resolve the software
`current` link to one canonical immutable run and verify the retained window
binary hash plus the aggregate-bound evidence manifest. On success, copy every
physical input into a temporary publication, validate those copies, hash them,
rename the set atomically, make it read-only, and swap the physical `current`
link atomically.
