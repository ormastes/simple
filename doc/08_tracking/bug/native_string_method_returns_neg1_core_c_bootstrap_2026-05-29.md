# Bug: String method calls return -1 in core-c-bootstrap native builds

- **ID:** native_string_method_returns_neg1_core_c_bootstrap
- **Severity:** P1 (blocks native string ops) — *needs confirmation of scope*
- **Date:** 2026-05-29
- **Area:** compiler / seed native codegen (string method dispatch)
- **Status:** open — reported mid-investigation, needs isolated repro

## Summary

In `native-build --runtime-bundle core-c-bootstrap`, calling `.len()` on a
`text`-typed receiver returns **-1**, even though the string runtime symbols
are present in the linked binary (`_rt_string_len`, `_spl_str_len`, `_rt_len`
all confirmed via `nm`). The native codegen appears NOT to call these functions
for string `.len()` — it emits a dynamic-dispatch path that returns -1 (the
"not-found" sentinel). The same affects `.slice()` and `.substring()`.

## Impact

Blocks the editor TUI **native render path (Route 2)** — `len`/`slice` are used
throughout the render/controller code, so the editor cannot draw a frame even
after the `EditorBuffer`/LSP layer compiles. Likely affects other native
programs that use string methods in `core-c-bootstrap` mode.

## Evidence (from the render agent, 2026-05-29)

- The string runtime IS linked (symbols present in the binary).
- `.len()` still returns -1 → codegen isn't dispatching to the runtime fn.
- Earlier a related symptom appeared as `function not found: str.slice`.

## Caveats / needs confirmation

The render agent stalled (watchdog) before isolating this:
1. Confirm with a MINIMAL repro: native-build a trivial program doing
   `"abc".len()` with `core-c-bootstrap` and check the return value.
2. Determine scope: editor-specific call shape vs. all `text` receivers.
3. Test whether a different runtime bundle (`rust-hosted` / `hosted-runtime`)
   dispatches correctly — if so, the bundle/codegen pairing is the fault.

## Proposed fix

Investigate seed native codegen for string method-call lowering on `text`
receivers; ensure `.len()/.slice()/.substring()` lower to the `rt_string_*`
runtime calls rather than a dynamic-dispatch path that returns the -1 sentinel.

## See also

- `doc/08_tracking/feature_request/editor_markdown_editing_subsystem_2026-05-28.md`
- `doc/08_tracking/bug/editor_jit_run_route_blockers_2026-05-28.md`
