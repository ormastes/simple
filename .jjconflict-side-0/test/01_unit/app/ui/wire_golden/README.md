# UI Wire-Protocol Golden Fixture

This directory holds the byte-exact regression oracle for the
`ui_access_snapshot_to_json` encoder defined in
`src/lib/common/ui/access.spl`.

The Phase 0 deliverable for the **UI Typed Core RFC**
(`doc/05_design/ui_typed_core_rfc.md`). Phases 1–8 of the migration must
keep `wire_golden_spec.spl` passing byte-identically — any drift means the
wire contract changed and clients downstream (web/TUI/CLI/Tauri/Electron
backends + IPC v1 socket consumers) will break.

## Cases covered

| Case | Tree | Encoder branches exercised |
|------|------|----------------------------|
| A | Empty snapshot | envelope keys + empty arrays |
| B | One surface + one root `panel` node | surface, node, empty props/children/actions |
| C | Panel + Button + Dialog + 1 event | non-empty props, child_ids, action_names, recent_events |

## When to update

**Do not** edit the `GOLDEN_*` literals to make a failing test pass.

If the wire format intentionally changes (e.g. a new field is added,
a serialization order shifts, an enum case maps to a new wire string),
the change requires:

1. A separate RFC under `doc/05_design/`
2. A bump of `UI_ACCESS_PROTOCOL_VERSION` in `src/lib/common/ui/access.spl`
3. New `GOLDEN_*` literals captured by running the spec, copying the
   actual output, and committing in the same change as the format change

## Capturing a fresh baseline

If you need to regenerate a literal (e.g. after an intentional protocol
bump), temporarily replace the `expect(...)` with a print:

```
val out = ui_access_snapshot_to_json(_multi_widget_snapshot())
println(out)
expect(out).to_equal(GOLDEN_MULTI_WIDGET)
```

Run with `bin/simple test test/unit/app/ui/wire_golden/wire_golden_spec.spl`,
copy the printed JSON into the corresponding `GOLDEN_*` literal, escape
quotes (`"` → `\"`), then revert the println.

## Interpreter-mode caveat

Per `.claude/rules/testing.md`: the test runner only verifies file loading
in interpreter mode. Real assertion execution requires compiled mode.
Until Phase 2 lands typed kinds, run via:

```
bin/simple test test/unit/app/ui/wire_golden/wire_golden_spec.spl
```

If `it` block bodies don't actually execute in your environment, the
fixture still serves as a compile-time check that the encoder API
shape (`UiAccessSnapshot`, `UiAccessNode`, `UiAccessSurface`,
`UiAccessEvent`, `ui_access_snapshot_to_json`) has not changed.
