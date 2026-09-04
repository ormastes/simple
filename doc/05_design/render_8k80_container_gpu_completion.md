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
changing revisions, never over the warmup. Parse and lower the two immutable
semantic revisions before timing and report that combined work separately as
`producer_receipt_preparation_ns`. This keeps the end-to-end preparation cost
visible while matching the C Vulkan submit-and-fence measurement boundary.

The selected workload is `web-semantic-retained-damage-v1`: a stable full
background plus one changing semantic element at (128,128), 256x128. Perform a
full-frame strict Vulkan seed before timing. Each timed revision selects one
of the two canonical pre-lowered Web/DrawIR revisions and includes only the
retained-damage submit and fence; readback stays outside timing. Accept only when the final retained
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
retains its separately reported semantic preparation cost while timing the
same GPU boundary as the C comparison. Neither caches
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

## C Vulkan parity gate

`scripts/check/check-engine2d-vulkan-c-parity.shs` compares feature receipts
only after both implementations identify the same workload hash, physical
device, dimensions, warmup/sample counts, timing scope, and final checksum.
Both sides must prove known completion, zero mismatches, no fallback, and zero
timed readback. The gate passes only when Simple p95 is at most twice C p95.

The existing mixed C benchmark is not interchangeable with the semantic A5
row: its font atlas is synthetic and it has no PATH/EDGE workload. Each feature
therefore needs matching C and Simple producers using
`engine2d-vulkan-feature-perf-v1`; missing or drifted receipts fail closed and
must never be reported as a parity result.

The packed-font C producer deliberately uses a synthetic opaque 16x16 atlas.
It measures only packed parameter upload plus Vulkan submit/fence throughput;
it does not claim real-vector-font accuracy. Real-font accuracy remains owned
by the independent Simple device-readback versus CPU-oracle checksum gate. A
Simple synthetic packed-font producer must use the identical atlas, placement,
glyph count, and workload hash before the C receipt is comparable.

The primitive pair fixes four 8K workloads: 1% retained rectangle fill,
sixteen full-width horizontal lines, the same lines lowered to one-pixel
rectangle dispatches, and a 1% image copy. Both implementations seed the full
background before one warmup and 31 samples, batch each feature frame into one
submission, exclude readback from timing, and run the same exact final-pixel
oracle. Device name plus driver identity forms the cross-process device hash.
