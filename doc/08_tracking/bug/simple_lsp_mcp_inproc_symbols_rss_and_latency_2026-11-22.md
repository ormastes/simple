# In-process LSP MCP document symbols exceed Linux resource targets

Status: partially fixed 2026-11-24. Per-symbol re-reads and re-parses were already removed by 70d34196da3 and 8a04b71ff1f (one parse, facts hoisted). This change adds a per-request read memo for the in-process lsp_symbols path (source_reader begin_disk). The p95 and RSS targets are NOT re-measured: no idle host or native build was available. Keep open until remeasured.

The Phase 2 whole-program Linux LSP MCP executable built from `70d34196da3`
(SHA-256 `f029fae5735030fb4af98f3475fd9c454536f243a9522cde2cd547f039295d16`)
returned correct visibility-filtered document symbols but exceeded the
request-latency and RSS thresholds in
`scripts/check/check-mcp-lsp-nfr-evidence.shs`.

Start the native server with `SIMPLE_BINARY` pointing at a nonexistent file,
complete the MCP stdio handshake, and request `lsp_symbols` on
`src/app/simple_lsp_mcp/main.spl` once with `visibility: "all"` to verify
`SERVER_NAME`. On the same connection, send 20 successive requests with
`visibility: "public"` and verify that each returns a populated hidden summary.
Measure each request from send to response with a monotonic clock. Measure
peak child RSS after closing stdin and reaping the server.

All 20 public-view calls returned correct results. Startup was 4.7 ms.
Request p95 was 704.6 ms against a 200 ms target. Peak child RSS was
1,797,420 KiB against a 1,048,576 KiB target. These results were collected on a
Linux x86-64 host with concurrent bootstrap workloads and full swap. Repeat the
same sequence on an idle host to distinguish resource contention from the
request's retained allocations.

Inspect repeated file and boundary lookups in the visibility classification
path, and measure RSS after successive requests in the same server process.
Preserve visibility filtering and the hidden summary while reducing p95 below
200 ms and peak RSS below 1 GiB.
