# html_compat native text method lowering blocker

Date: 2026-06-11

## Summary

The focused HTML compatibility geometry path no longer proves a
`06_card_panel` zero-box layout failure. Interpreter mode returns three
`06_card_panel` boxes and four `24_flex_wrap_reverse_basic` boxes through the
focused native smoke input.

Native evidence was blocked before execution by text-method lowering in the
HTML renderer closure. The blocker is resolved for `substring` in this slice:
the Rust seed LLVM builtin-method path maps `String.substring` to existing
`rt_slice`, and the Pure Simple MIR lowering mirrors typed `text.substring` /
`text.slice` to the native string slice runtime.

## Repro

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple compile \
  src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl \
  --native \
  --output build/tmp/html_compat_geometry_probe_native_full_smoke \
  && build/tmp/html_compat_geometry_probe_native_full_smoke
```

Previously observed after removing iterable `for` loops from the focused
closure:

```text
error: codegen: undefined symbol: str.substring
```

Resolved evidence with the patched bootstrap compiler:

```text
Compiled src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl -> src/app/wm_compare/html_compat_geometry_probe_native_full_smoke
status=pass
```

Before that cleanup, the same native closure failed earlier with:

```text
error: codegen: undefined symbol: rt_for_iterable
```

## Interpreter Control

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple run \
  src/app/wm_compare/html_compat_geometry_probe_native_full_smoke.spl \
  --mode=interpreter --clean
```

Observed:

```text
fixture=06_card_panel count=3
fixture=24_flex_wrap_reverse_basic count=4
status=pass
```

## Current Assessment

This was a native compiler/runtime lowering gap for method-form text operations
inside the Simple Web HTML parser/layout closure, not a proved Chromium layout
geometry mismatch for `06_card_panel`.

The earlier parser-stack suspicion was also hardened in this slice:
`parse_html()` now truncates the close-tag stack by copying the kept prefix
instead of using `pstack.pop()` in a loop. The focused native smoke now executes
through that path and returns `status=pass`.

The native smoke should remain focused on both `06_card_panel` and
`24_flex_wrap_reverse_basic` so future native work continues proving real
layout output instead of only linking.
