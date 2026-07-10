# Native Simple Web Layout Null Call

## Status

Resolved on 2026-07-10. Native Simple Web layout now links and executes the
array concatenation used by `extract_css_vw`.

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

## Root Cause

MIR correctly lowered array `+` to `rt_array_concat`, but the core C runtime
did not implement or export that ABI symbol. The native linker left the call
unresolved as address zero.

## Fix

- Implement `rt_array_concat` in `src/runtime/runtime_native.c`, including byte
  array preservation and length/capacity guards.
- Declare the ABI in `src/runtime/runtime.h`.
- Require the symbol in the Rust core-runtime symbol audit.
- Add a tracked Cranelift entry-closure regression that renders a two-style
  document through the Simple Web software layout path.

## Verification

```sh
SIMPLE_BIN="$PWD/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple" \
OUT_DIR="$PWD/build/check/simple-web-layout-native-runtime-concat" \
sh scripts/check/check-simple-web-layout-native.shs
```

The native regression built with zero failed files and reported:

```text
simple_web_layout_native_status=pass
simple_web_layout_native_reason=core-array-concat-linked
```

## Impact

- Interpreter scalar and CPU-SIMD layout outputs are bit-exact.
- The standalone C span ABI and x86-64/AArch64/RISC-V native probes pass.
- Native end-to-end layout is safe for the tracked multiple-style-block probe.
- The broader 4K/8K CPU-SIMD performance target remains open because the
  attempted layout paint routing did not yet produce a valid styled AOT fixture
  or native SIMD hit evidence.

## Attempted Fix

The two array `+` operations that append selected selector groups and
declarations lowered to the missing runtime call. Explicit append loops allowed
one focused page to render, but were rejected because they avoided rather than
fixed the shared ABI defect.

The one-style probe temporarily reported:

```text
Build complete: 5 compiled, 0 cached, 0 failed
pixels=57600
```

The shared runtime ABI implementation supersedes that workaround and is covered
by the tracked native regression above.
