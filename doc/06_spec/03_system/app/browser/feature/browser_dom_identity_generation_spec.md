# Generation-qualified browser DOM identity

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Status | Integrated static evidence; runtime and docgen held |
| Requirements | REQ-WEB-BROWSER-004/007/008/017/018 |
| Planned NFRs | NFR-WEB-BROWSER-004/005/006/008/014/015/016 |
| Executable source | `test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl` |
| Plan | `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md` |
| Canonical render path | BrowserSession -> Web semantic/layout -> DrawIrComposition -> Engine2D |

## Scenario: retire stale routes across browser script UI and hosted rendering

### Build the document identity index

Create a real blank `BrowserSession`, verify its generation-1 index, then open
the document fixture. The published two-pass index proves first duplicate-ID
ownership, external form ownership, explicit and nested label association,
form-owned and ownerless radio groups, canonical `id:`/`path:` layout keys,
and the session-owned `layout_target_key_for_route`, `author_id_for_route`,
`document_generation`, and `current_dom_identity_index` projections.

### Dispatch through stable routes

Dispatch a callable JavaScript listener using the typed route stored beside its
JS heap object. The receipt exposes the same target/current route, while the
textual UI adapter and SimpleScript bridge accept that live route. Focus,
value, and style changes must preserve the generation, index object, and JS
object identity; replacing child text must publish a new generation.

Folded label cases require sibling `label,control` order, nested
`label,control,label` order, interactive-descendant suppression, label
cancellation, and canceled-control preactivation rollback. A 4,096-listener
checkbox case requires its synthetic input phase to share the outer dispatch
budget instead of executing a 4,097th action.

### Replace the document during a handler

An oversized script-driven `innerHTML` candidate is rejected at the
`BrowserSession.publish_dom_snapshot` boundary after a broker cookie write. It
must leave generation, index, DOM, JavaScript runtime/object map, callable
listeners, SimpleScript root/runner/index/callbacks, and
`pending_script_cookie_writes` unchanged. `BrowserSession` owns no stateful
`ScriptHost`; `script_host_apply_action_to_route` is a pure DOM transform, so
the oracle does not invent a ScriptHost root. An oversized load and an injected
duplicate-node candidate have the same rollback obligation. The handler then replaces
the document with a visually different button that intentionally reuses the
old author and numeric identity. The old SimpleScript callback is retired, the
generation advances once, and neither old nor new click default runs while the
handler unwinds.

### Reject stale routes and release the index

The session layout gate, reverse layout projection, author projection, DOM
dispatch, SimpleScript bridge, and stale textual UI snapshot reject the old
route without mutation. Both the direct hosted adapter and isolated worker
replace during press and release without a click. The worker also clears its
pressed/stale-hit routes and root-request/command-capability authority. The
release oracle replaces the document between a valid press and capability-
bound release, then proves no callback, body, title, or navigation mutation.
surviving current route is recovered from the canonical hit index,
its `replace` Draw IR command is an exact green `8x8` rectangle, and Engine2D
produces a green inside pixel and white outside pixel. Closing the session
advances the generation and clears the current index and script document.

## Folded work and production-receipt policy

The executable fixture builds exact 32-node and 64-node indexes and checks 64
and 128 build visits: two bounded passes and exact N/2N work scaling. It also
defines `dom-identity-runtime-receipt-v1` with these mandatory fields:

- 10,000 replacement/dispatch cycles;
- build and input-to-paint p95;
- allocation count;
- live/retired index counts and index bytes;
- post-warmup, final, and maximum RSS;
- stale and budget reject counts.

Every runtime-measured field remains `-1` and status remains `runtime-held` in
this static lane. No timing, allocation, RSS, 10,000-cycle, docgen, or target
runtime PASS is claimed.

Source remains **HOLD/RED**: rejected evaluation can leak
`pending_script_cookie_writes`, and isolated stale rejection does not yet prove
all route/capability cleanup. These are acceptance oracles, not a source PASS.

## Traceability

| Requirement | Evidence | Status |
|---|---|---|
| REQ-WEB-BROWSER-004 | canonical layout key, Draw IR command, Engine2D pixels | executable oracle; runtime held |
| REQ-WEB-BROWSER-007 | typed callable/SimpleScript/UI event routes and label/default cases | executable oracle; runtime held |
| REQ-WEB-BROWSER-008 | hosted stale press/release cannot click equal replacement | executable oracle; runtime held |
| REQ-WEB-BROWSER-017 | old generation callbacks/listeners and failed candidates retire or roll back | executable oracle; runtime held |
| REQ-WEB-BROWSER-018 | N/2N counters and complete held 10,000-cycle receipt schema | schema complete; numeric evidence held |
| NFR-WEB-BROWSER-004/005/006/008/014/015/016 | receipt fields and fail-closed status | not promoted |

## Provenance

This manual is hand-reconciled with the executable scenario because the lane
forbids runtime, bootstrap, and docgen execution. The executable SSpec is the
authoritative assertion source; this page makes no PASS claim.
