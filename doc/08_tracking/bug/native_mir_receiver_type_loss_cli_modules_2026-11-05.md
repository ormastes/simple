# Native MIR lowering loses receiver/iterable types in three valid forms (2026-11-05)

Found while clearing the 15 full-CLI `mir-module-failure` modules. Each was
worked around with a type annotation / local binding that is valid, ordinary
Simple; the compiler should infer these without help. Repro: admitted Stage 2,
`simple compile <file>.spl --format=smf` (reports `unresolved method call` /
`for-in over non-array iterables` as FATAL lowering errors).

1. Chained index + field + method: `_calc_access_hosts[0].controller.find_json(x)`
   (module-level `[CalcSessionHost]`) -> `unresolved method call: find_json`
   (`receiver_has_type=false`). `val h: CalcSessionHost = arr[0]` then
   `h.controller.find_json(x)` resolves. Site:
   `src/app/office/sheets/calc_access_session_host.spl`.
2. `var x = button(...)` (imported `common.ui.builder.button -> WidgetNode`) then
   `x.set_prop(...)` -> unresolved; `text_field(...)` in the same function
   resolves. A second, unrelated free `fn button(text, type) -> text` exists in
   `src/compiler_rust/lib/std/src/tooling/html_utils.spl`; bare-name return-type
   lookup is the suspected cause (unconfirmed). Annotating
   `var x: WidgetNode = button(...)` resolves. Site:
   `src/app/office/sheets/access_controller.spl`.
3. Tuple-pattern destructure `case Ok((pin, result)):` then
   `for edge in pin.dependencies:` -> `for-in over non-array iterables ... (collection
   mir type: Unit)`. `val edges: [DepEdge] = pin.dependencies` resolves. Site:
   `src/app/update/main.spl`.

Also noted, not touched (out of scope): `src/lib/nogc_sync_mut/mcp/dispatch.spl:137`
and `src/os/installer/staged_root_tree_enumerator_v1.spl:155` use the
non-existent `text.from_bytes(...)` (same `undefined variable text` class as
the fixed `app.provider_cli.entry`).
