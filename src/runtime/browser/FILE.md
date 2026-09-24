# browser — Embedded-browser C boundary

The only C in the Chrome dynlib lane. It exists because CEF delivers offscreen frames by
calling BACK into the host (`cef_render_handler_t::on_paint`) and the repo's FFI is
forward-only, so the callback owner cannot be Simple. Everything in it that is not a CEF
callback is mirrored by the Simple twin
`src/lib/common/browser/chrome_render_shim_twin.spl`, written for the dual-run shadow gate
but **not yet admitted by it** — see that file's manifest for why (the gate's `ref=` side
needs an exported `rt_*`, and these counterparts are `static`).

## Entries

- **chrome_render_shim.c** — Chrome (CEF) offscreen render dynlib, C ABI v1. Exports exactly
  the 10 `simple_chrome_render_*` symbols; every other function is `static` and the build
  uses `-fvisibility=hidden`. All CEF includes are behind `SIMPLE_CHROME_CEF`, so the stub
  build compiles on a host with no CEF drop and returns
  `CHROME_RENDER_E_BACKEND_UNAVAILABLE`. Must stay `clang -fsyntax-only` clean — that is a
  blocking push gate.

- **chrome_render_shim.h** — the frozen ABI v1 declarations, status codes, frame states and
  bounds. Sibling of, not a replacement for, the 5-symbol `simple_chromium_oracle_*` broker
  ABI: disjoint prefix, same `nm`-exact-set discipline.

- **FILE.md** — this manifest.
