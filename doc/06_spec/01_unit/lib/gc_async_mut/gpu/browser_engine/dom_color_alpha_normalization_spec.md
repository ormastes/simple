# CSS Alpha Number and Percentage Normalization

This manual describes the executable SSpec at
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl`.
It covers alpha parsing and propagation; RGB channel-number semantics remain
outside this change.

## Scenario: parse complete bounded CSS numbers

1. **Accept signed fractions, percentages, and exponent forms.** Exercise both
   comma and slash `rgb()`/`rgba()`/`hsl()`/`hsla()` syntax.
2. **Clamp extreme exponents before byte conversion.** Positive overflow is
   opaque; negative and underflow values are transparent.
3. **Round beyond the former nine-digit truncation boundary.** Distinguish
   `0.0019607843` from `0.0019607844` and round `50.0%` to byte 128.
4. **Leave the independent RGB channel parser unchanged.** Retain its existing
   percentage and exponent-token behavior.

## Scenario: reject malformed alpha without replacing a winner

1. **Distinguish transparent alpha from malformed alpha.** Valid zero alpha
   returns a present packed color; incomplete exponents, trailing decimal
   points, separated percent signs, and duplicate signs return no color. The
   legacy public `var(...)` parser sentinel remains transparent, while the
   checked/keyframe parser treats unresolved `var(...)` as absent.
2. **Cascade a later malformed duplicate behind the valid declaration.** Parse
   duplicate `50%` keyframes and require the earlier valid green at alpha byte
   128 to survive.

## Scenario: propagate exponent alpha through rendering

1. **Create one animation instance from exponent-alpha keyframes.** Reconcile
   RGB keyframes using `1e0`; HSL exponent alpha is covered directly above.
2. **Lower the animated opaque color to canonical Draw IR.** Require the web
   semantic/layout path to emit `0xFF22C55E` at `16 × 12`.
3. **Rasterize identically to an opaque literal control.** Compare the full
   `BrowserRenderer` pixel buffer and box-center pixel with the literal frame.

These nine numbered entries mirror the executable specification's nine
`step("...")` calls. The HTML/GUI annotations declare evidence kinds to retain
when SSpec/docgen runs; this checked-in manual claims no runtime or screenshot
result by itself.
