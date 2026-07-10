# Native Simple Web Layout Null Call

## Status

Open. This blocks native 4K/8K CPU-SIMD layout performance evidence.

## Reproduction

Build an entry-closure binary that calls
`simple_web_layout_render_html_software_pixels` from
`simple_web_html_layout_renderer.spl`. Cranelift links the binary with no failed
files or generated stubs, but execution exits with signal 11.

```sh
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
  --source build/check --source src/lib --entry-closure \
  --entry build/check/cpu-simd-layout-fast-probe.spl \
  --backend cranelift --mode one-binary \
  --output build/check/cpu-simd-layout-span-native
gdb -q -batch -ex run -ex 'bt 12' --args \
  build/check/cpu-simd-layout-span-native
```

## Evidence

The binary builds `10 compiled, 0 cached, 0 failed`, then calls address zero:

```text
#0  0x0000000000000000 in ?? ()
#1  simple_web_html_layout_renderer.extract_css_vw ()
#2  simple_web_html_layout_renderer.simple_web_layout_render_html_pixels_mode ()
#3  simple_web_html_layout_renderer.simple_web_layout_render_html_software_pixels ()
#4  spl_main ()
```

LLVM entry-closure builds expose additional pre-existing verification failures
in unrelated modules and also cannot provide executable layout evidence.

## Impact

- Interpreter scalar and CPU-SIMD layout outputs are bit-exact.
- The standalone C span ABI and x86-64/AArch64/RISC-V native probes pass.
- Native end-to-end layout remains unsafe for realistic multiple-style-block pages.

## Attempted Fix

The two array `+` operations that append selected selector groups and
declarations lower to a null dynamic call. Explicit append loops allowed one
focused page to render, but a two-style-block regression fixture still called
address zero. Direct mutating `push` and reassigned `push` forms both failed
native verification, so the workaround was rejected.

The one-style probe temporarily reported:

```text
Build complete: 5 compiled, 0 cached, 0 failed
pixels=57600
```

That result is insufficient: the two-style-block probe still exits with signal
11 after a clean native build. The compiler/runtime owner must fix native array
concatenation or mutation lowering before the canonical scale contract can
provide trustworthy full-size timing, RSS, and native SIMD hit evidence.
