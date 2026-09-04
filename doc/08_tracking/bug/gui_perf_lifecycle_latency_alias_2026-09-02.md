# GUI performance lifecycle latency alias

Status: fixed in local commit lane; native execution pending an admitted CLI.

## Defect

`backend_measurement_software_export.spl` serialized `cold_start_us` and
`warm_start_us` from frame p50 and serialized `p95_input_to_paint_us` from
frame p95. The values were positive but were not independent measurements, so
the benchmark could falsely claim startup and interaction evidence.

## Fix

The exporter now clocks four distinct operations: first render, post-warmup
render, ordinary frame samples, and scroll-state-to-present samples through
`simple_web_layout_render_html_pixels_at_scroll` with the requested backend.
The ordinary frame is retained separately for checksum and nonblank evidence.
The interaction interval is explicitly scoped as `scroll-state-to-present`,
not full host-event dispatch.
The scale contract exports all measurements for CPU/SIMD and scalar rows, and
its source contract rejects the three historical aliases.

The scale wrapper also no longer assumes GNU `/usr/bin/time -f`. It selects
`gtime` when installed, otherwise uses Darwin `/usr/bin/time -l` on macOS and
normalizes the byte-valued maximum resident set size to KiB. This repairs the
focused native evidence path on macOS without changing the report schema.

## Remaining verification

Run the focused SSpec and native 4K/8K scale contract against the exact admitted
current compiler/runtime. The Darwin timing branch and source/manual guards are
verified, but they are not native 4K/8K timing evidence.
The currently deployed CLI reports a normal version identity, then delegates
`run` compilation to the Rust bootstrap seed and prints the seed warning only
after compilation starts. A future admitted self-hosted compiler or a
post-launch stderr rejection gate is required before native evidence can pass.
