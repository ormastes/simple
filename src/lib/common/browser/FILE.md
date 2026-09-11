# browser — Pure browser-boundary logic (Simple twins)

Pure, allocation-free logic shared by the embedded-browser lane. No I/O, no FFI.

## Entries

- **chrome_render_shim_twin.spl** — Simple twin of the pure logic in
  `src/runtime/browser/chrome_render_shim.c`: the frame state machine, BGRA frame-size and
  readback-capacity arithmetic, the bounded request-payload rule, and the status-code to
  receipt-token map. Any edit to the C shim's pure block is an edit to this file, and vice
  versa.

  **Not yet admitted by the dual-run shadow gate, and honestly so.**
  `scripts/check/check-dual-run-shadow.shs` discovers pairs only from
  `# @dual_pair: <name> mode=<effect-compare|value-legacy> ref=<rt_*> cand=<std...>`
  annotations in a `*_spec.spl` (`enumerate_pairs`, :47). Its `ref=` side must be a callable
  `rt_*` reference; the C counterparts here are deliberately `static` inside the shim and
  are not exported, so no such annotation can be written without widening the frozen 10-symbol
  ABI. Recorded as an open item in `.spipe/chrome_dynlib_vulkan_render/state.md`; the twin is
  written FOR that gate and is not claimed to be covered by it.

- **FILE.md** — this manifest.
