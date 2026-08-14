# Strict semantic Vulkan producer

This manual describes the executable scenarios in
`test/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.spl`.

## Accepted receipt

The producer renders changing Web semantic revisions through canonical DrawIR
and strict Engine2D Vulkan. A passing receipt names Vulkan as both requested and
selected backend, records positive backend/device identities, distinct nonzero
start/end checksums, known completion, no fallback, one untimed warmup, sixty
timed samples, and zero timed readback bytes.

## Unavailable Vulkan

Unavailable strict Vulkan is reported as `blocked` with zero identities and
unknown completion. It is never converted to software evidence.

## Timing boundary

Each timed sample ends after strict device submit/fence completion. Device
readbacks for the start/end checksum oracle occur outside the timed interval.
The system test checks this source contract; live execution and doc generation
remain gated by the source-matched Stage 4 runtime recorded in TODO810.
