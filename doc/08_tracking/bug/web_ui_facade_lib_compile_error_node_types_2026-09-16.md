# web_ui facade spec blocked: lib compile error in common/web/node_types.spl

Date: 2026-09-16
Status: OPEN

## Observed

`web_ui/web_ui_facade_spec.spl` fails before any example runs: loading the
stdlib surfaces `Common mistake detected` at
`src/lib/common/web/node_types.spl:69:5` — the `namespace: text` field
declaration inside `class Element` (likely the reserved-ish `namespace` field
name or a field-shape the checker rejects).

## Impact

Every spec importing the web_ui tree fails at compile time; no web_ui
behaviour can be verified.

## Expectation

`src/lib/common/web/node_types.spl` compiles; `Element` carries its namespace
field (renamed or restructured per language rules).

## Unblock condition

Fix the declaration at node_types.spl:69 (rename the field or adjust to the
sanctioned class-field syntax), then re-run
`test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl`.
