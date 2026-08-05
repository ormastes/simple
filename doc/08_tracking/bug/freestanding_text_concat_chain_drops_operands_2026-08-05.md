# Freestanding lane: 3+ operand text `+` chain silently drops operands

- **Date:** 2026-08-05
- **Lane:** SimpleOS guest, `--target x86_64-unknown-none` (freestanding native
  codegen), built through the stage3 pure-Simple compiler by
  `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
- **Status:** open (source-shape workaround applied at the discovered call
  sites; codegen not fixed)
- **Severity:** high — silent data loss in a boring, ubiquitous construct.

## Symptom

`a + ":" + b + "\n"`, with `a` and `b` live non-empty `text` locals, evaluates
to a 1-character string containing only the trailing literal. A two-operand
concat is correct; adding a third operand corrupts the value, and `.len()` on
the three-operand result reads back **-1** (the same "invalid value" shape
`Dict.len()` returns on this lane).

## Measured repro (verbatim guest serial receipts)

Instrumented `_css_collect_custom_props` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`:

```
[bg-diag] collect-entry bg=1 dd=3 colon=14 semi=19 body_len=468 raw_name_len=11 raw_name=<--radius-sm> name_len=11 name=<--radius-sm> val_len=3 val=<8px>
[bg-diag] concat entry_len=1 interp_len=16 two_len=12 three_len=-1 interp=<--radius-sm:8px
[bg-diag] collect base=45 variant=0 e0len=1 e0=<
```

where, for `name` = `--radius-sm` (len 11) and `prop_val` = `8px` (len 3):

| expression | expected len | measured len |
|---|---|---|
| `name + ":"` | 12 | 12 (correct) |
| `name + ":" + prop_val` | 15 | **-1** |
| `name + ":" + prop_val + "\n"` | 16 | **1** (content: just `"\n"`) |
| `"{name}:{prop_val}\n"` (interpolation) | 16 | 16 (correct) |

String interpolation is unaffected; only the `+` chain is.

## Impact found in the wild

Every CSS custom property of the installed theme was collected correctly
(45 `:root` declarations, names and values parsed exactly) and then written
into the property table as a bare `"\n"`. The var-resolution table therefore
indexed **0** properties, so every `var(...)` in the themed sheet resolved to
the empty string on the guest:

- `background: linear-gradient(...), var(--app-surface)` became
  `linear-gradient(...),` — a dangling comma, no base layer. The declaration
  handler then parsed the gradient's first stop as the surface color
  (`bg=352321535` = `window_gradient_start_rgba`) and kept the layer raw.
- `backdrop-filter: blur(var(--blur-surface)) saturate(170%)` became
  `blur() saturate(170%)` (the observed `backdrop_len=21`).

which failed the CPU-composited material admission
(`simple_web_html_layout_renderer_core.spl:~2915`) and produced
`[wm-frame] content-provenance-rejected` / `window-degraded` in the SimpleOS WM
fullscreen evidence gate. Note this was NOT a CSS, theme, or material-gate
defect at all — the gate was fail-closed correctly on corrupt input.

## Workaround applied

Rewrite affected sites as a single interpolated literal (plus at most one `+`):

- `simple_web_html_layout_renderer_core.spl` `_css_collect_custom_props`:
  `val entry = "{name}:{prop_val}\n"`.
- `simple_web_html_layout_renderer_core.spl` material receipts (cpu/solid
  entries): build one interpolated literal, then a single `+` append.

## Related, found alongside

`text.index_of(needle)` returns a bogus `0` when the receiver is a substring
slice on this lane (measured: empty line → `index_of(":") == 0` while
`find_from(line, ":", 0) == -1`). `find_from`'s own docstring already documents
the untagged-slice hazard. `CssVarResolutionState.new` was switched to
`find_from`. Other `index_of` uses on slice receivers in guest-reachable code
should be audited.

## Next steps

1. Reduce to a minimal `.spl` freestanding repro outside the browser engine and
   locate the lowering (constant-fold of literal chains vs. runtime
   `rt_string_concat` re-entry on an intermediate result).
2. Audit guest-reachable code for `x + y + z` text chains; the corruption is
   silent, so nothing else will report it.
3. Add a freestanding codegen test that asserts `(a + b + c).len()`.
