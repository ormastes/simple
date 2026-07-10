# Native Simple Web Inline Style Color Missing

## Status

Resolved on 2026-07-10. Native AOT now parses the inline style and paints the
exact `48x24` opaque color area.

## Reproduction

Build a Cranelift entry-closure probe that renders this document through
`simple_web_layout_render_html_software_pixels`:

```text
<body style='margin:0;background-color:#102030'><div style='width:48px;height:24px;background-color:#224466'></div></body>
```

Use a `64x48` framebuffer and count pixels equal to `0xFF224466`. The tracked
experiment built successfully but returned exit code 6 because the count was
zero.

The initial raw-color heap scan was inconclusive because native arrays store
tagged integer pixels. A corrected tagged-value scan confirmed the failed frame
was all white.

## Root Cause

Cranelift correctly boxed dynamic array indices as `RuntimeValue` integers
(`index << 3`) before calling `rt_index_get` and `rt_index_set`. The core C
runtime consumed those values as raw offsets. `_html_scan_events` therefore
read `parts[1]` as slot 8, dropped every tag event, and produced an all-white
frame.

## Fix

- Decode and validate tagged integer indices in core-C `rt_index_get/set`.
- Preserve negative indexing and return false for invalid/out-of-range writes.
- Strengthen the tracked native layout probe to require inline-style round-trip
  and exactly 1152 pixels of `0xFF224466`.
- Extend the shared core-C/Simple-core ABI probe with tagged positive, negative,
  overly negative, out-of-range, and invalid-tag cases.

## Evidence

- Native SIMD architecture detection was true in the same Cranelift binary.
- Scalar and CPU-SIMD-mode framebuffers were equal before the color assertion.
- Direct GDB calls proved `rt_string_split`, `rt_string_find`,
  `attr_value_by_key`, and indexed writes worked independently; the failure was
  the tagged index passed by compiled scanner code.
- A GDB breakpoint on `rt_engine2d_simd_fill_span_u32` was never reached.
- The preceding array-concat null call is independently fixed and its tracked
  two-style-block native regression passes.

## Impact

The scalar AOT fixture is now valid quality evidence. The opaque-background
SIMD prototype remains removed; GPU, alpha, rounded-corner, gradient, and glyph
paths remain unchanged until CPU-SIMD routing is reintroduced and verified.

## Verification

```text
simple_web_layout_native_status=pass
simple_web_layout_native_reason=core-index-and-array-concat-linked-color-exact
```

The focused Rust ABI test reports `1 passed; 0 failed` for
`test_core_lane_runtime_required_abi_stdout_stderr_and_values`.
