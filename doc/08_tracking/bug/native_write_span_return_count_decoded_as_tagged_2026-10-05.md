# Native lane: `write_span` return count is decoded as a tagged value (count / 8) (2026-10-05)

**Status:** OPEN. This bug already exists on `origin/main` `4b618f09c7a`; branch `work/engine2d-mem` did not introduce it.

## Reproduction

`test/fixtures/compiler/write_span_native_inrange_probe.spl` contains
`val moved = fb.write_span(fb, 0, w * 10, w * 50)` with `w = 320`, so the call
writes 16,000 elements.

| lane | printed `moved` | framebuffer checksum |
|---|---|---|
| interpreter | 16000 | 902858392 |
| JIT (`simple run`) | 16000 | 902858392 |
| `SIMPLE_NATIVE_BUILD_RUST=1 native-build` (C runtime from `src/runtime`) | **2000** | 902858392 |

The array contents are correct in every lane. Only the returned count is
wrong: 16000 / 8 = 2000, and 320 / 8 = 40 in the per-row loop. The C
`rt_array_write_span` (`src/runtime/runtime_native.c`) returns a raw
`int64_t` count. The Rust seed runtime returns `RuntimeValue::from_int(count)`,
which is tagged. Compiled code untags the result, so the C lane's raw count
is shifted right by 3.

## Unblock condition

Make both runtimes use one return contract: either the C twin tags the count
the way the Rust runtime does, or the compiled call site stops untagging this
symbol. Then extend the probe to assert `moved == 16000` in the native lane.
