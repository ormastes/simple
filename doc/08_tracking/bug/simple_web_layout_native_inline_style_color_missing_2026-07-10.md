# Native Simple Web Inline Style Color Missing

## Status

Open. This blocks the native AOT color/alpha parity fixture required before
enabling the CPU-SIMD browser-layout paint path.

## Reproduction

Build a Cranelift entry-closure probe that renders this document through
`simple_web_layout_render_html_software_pixels`:

```text
<body style='margin:0;background-color:#102030'><div style='width:48px;height:24px;background-color:#224466'></div></body>
```

Use a `64x48` framebuffer and count pixels equal to `0xFF224466`. The tracked
experiment built successfully but returned exit code 6 because the count was
zero.

At the failed process's `exit(6)` breakpoint, GDB scanned writable mappings for
the native array's 64-bit pixel representation. It found zero child
`0xFF224466` values and zero body `0xFF102030` values, confirming the assertion
was not a comparison-lowering false positive.

## Evidence

- Native SIMD architecture detection was true in the same Cranelift binary.
- Scalar and CPU-SIMD-mode framebuffers were equal before the color assertion.
- Both tested inline background colors were absent from writable process memory
  at exit; only white pixel values were observed by the same scan.
- A GDB breakpoint on `rt_engine2d_simd_fill_span_u32` was never reached.
- The preceding array-concat null call is independently fixed and its tracked
  two-style-block native regression passes.

## Impact

The renderer cannot use this AOT fixture as quality evidence: equality between
two frames is insufficient when neither frame proves the requested CSS color.
The opaque-background SIMD prototype was removed after three capped
verification cycles. GPU, alpha, rounded-corner, gradient, and glyph paths
remain unchanged.

## Next Check

Trace `attr_value_by_key` -> `compute_styles` -> `apply_decls` -> `paint` in one
native probe and identify the first stage where the inline `background-color`
is lost. Do not restore SIMD routing until the scalar AOT fixture first proves
the expected color.
