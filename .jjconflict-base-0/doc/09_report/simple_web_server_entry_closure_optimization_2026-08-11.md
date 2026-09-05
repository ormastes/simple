# Simple web server entry-closure optimization — 2026-08-11

## Contract

The hosted server retains production asynchronous HTTP dispatch, TLS
configuration, bounded request admission, and canonical server-side rendering.
SSR still lowers in-memory HTML through the canonical web layout/Draw IR path,
resolves the Engine2D backend with
`simple_web_engine2d_resolved_backend_name`, and rasterizes with
`simple_web_layout_render_html_pixels_engine2d`. PNG encoding and the
exactly-once async completion path are unchanged.

The entry closure must not acquire browser-only URL/file loading, theme-preview
state, readback result types, or animation APIs merely to render an HTTP body.
`test/02_integration/app/simple_web_server/ssr_entry_closure_spec.spl` makes
that boundary falsifiable.

## Evidence and change

Before this change, `ssr_submitter.spl` imported the general
`simple_web_renderer.spl` facade. Its module-level imports included:

- `simple_web_file_renderer` (URL/file loading),
- `Engine2DReadback` and all readback facade functions,
- `wm_chrome_theme` (theme-preview data), and
- timed/animated readback entry points.

The server called exactly one facade symbol. The replacement
`simple_web_ssr_renderer.spl` imports only the canonical backend resolver and
canonical HTML-to-pixels operation. Static source accounting with `wc -lc`
shows the removed wrapper branch contains 667 lines / 29,501 bytes across the
general facade, file renderer, and theme module. This is a source-closure proxy,
not a native RSS claim; shared transitive modules may still be retained by the
canonical renderer.

The last authoritative full-build baseline predating this change stopped after
7m48s at 2.67 GiB maximum RSS with zero objects. Per lane scope, no full native
build was run here. A later release gate must compare the same command and
record wall time, peak RSS, object count, artifact hash, and live SSR checksum.

## Result

Status: **STATIC PASS / NATIVE PERF UNVERIFIED**.

The capability boundary is narrower without feature loss. No throughput,
latency, executable-size, or build-RSS improvement is claimed until the
authoritative self-hosted native build and live SSR evidence complete.

Both touched production `.spl` files completed the required O3 optimizer
analysis. The narrow renderer reported one low-confidence bounds-check
opportunity; the submitter reported two bounds-check and eight dead-code
opportunities. These are compiler-pass candidates, not safe source deletions,
so no semantic rewrite was made. The available `bin/simple` identified itself
as the Rust bootstrap seed, therefore these optimizer results are advisory and
not authoritative release evidence.

The focused SSpec command completed but its warning stream exceeded the output
capture budget before a test summary was retained. It is recorded as
inconclusive and was not repeated, consistent with the runaway guard. The
source contract itself has non-vacuous positive and negative assertions.
