# Native codegen: nested if/else inside {} string interpolation emits raw source text instead of evaluating

- **ID:** native_string_interp_nested_if_verbatim_2026-07-19
- **Status:** OPEN
- **Severity:** medium (silent wrong output; no diagnostic)
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
A colon-form conditional inside a string interpolation hole:

```
serial_println("[glyph-probe] andtest={if (probe_bits & probe_mask) != 0u8: 1 else: 0}")
```

prints, in-guest, the literal source text of the hole — braces and all:

```
[glyph-probe] andtest={if (probe_bits & probe_mask) != 0u8: 1 else: 0}
```

No compile error, no runtime error — the interpolation silently degrades to
verbatim text. Simple `{name}` holes in the same binary evaluate correctly
(other probe lines interpolated fine).

## Impact
Any diagnostic or UI string relying on an inline conditional inside `{}`
silently emits garbage on the freestanding lane. Because it fails without
diagnostics, it can invalidate probe/evidence output (it cost one boot
cycle in the 2026-07-19 glyph investigation).

## Repro
Serial probe in gui_entry_desktop.spl (2026-07-19 boot, serial-diag.log);
hoisting to `val x = if cond: 1 else: 0` then interpolating `{x}` works.

## Fix direction
Either support the conditional-expression grammar inside interpolation holes
on the native path (parser/lowering parity with whatever the hosted lane
does), or reject it at compile time — silent verbatim passthrough is the
worst of both. Per repo rule (compact expression forms that fail must be
fixed or filed): this file is the filing.
