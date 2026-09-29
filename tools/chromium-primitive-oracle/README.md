# Chromium primitive oracle library

This test-only pure-Simple shared library implements the frozen ABI v1 from
`test/fixtures/chromium_primitive_oracle/simple_chromium_primitive_oracle.h`.
It runs the repository-pinned Electron/Chrome broker once per complete fixture
request, not once per event. The broker's CPU `capturePage` result is retained
as semantic/pixel evidence and never promoted to device-origin GPU evidence.

Build from the repository root with the self-hosted compiler:

```text
bin/simple compile tools/chromium-primitive-oracle/chromium_primitive_oracle.spl \
  --native --shared --strip \
  -o build/chromium-primitive-oracle/libsimple_chromium_primitive_oracle.dylib
```

Use `.so` on Linux and `.dll` on Windows. Consumers must validate the ABI,
symbol list, artifact hash, broker hash, and pinned Electron/Chrome versions.

The prepared-host oracle is pinned to Electron `42.5.0` and Chrome
`148.0.7778.271`. Every request carries the exact broker and npm lockfile
SHA-256 values; the broker recomputes both, verifies its running versions, and
fails before creating a window on mismatch. Browser identity in the response
includes those hashes. Scalar evidence escapes `%`, `;`, and `=` canonically so
it can pass the normalized-trace validator.
