# Lane UIQUERY — declarative UI query / ensure layer

Status: **shipped, 14 examples / 2 failures** on
`test/01_unit/os/services/llm/ui_access_dispatch_spec.spl`
(baseline on entry: 13 examples / 12 failures). Both remaining failures are
blocked outside this lane's writable scope — see "Blocked" below.

Verified identically under `bin/simple run` and
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`.

## What was built

### Query layer (`src/lib/common/ui/access_query.spl`)

`ui_access_query(snapshot, surface_id, canonical_id, kind, text_query,
focused_only, limit) -> UiAccessQueryResult`

Selects by canonical id, surface, role (`kind`), free text, and the `focused`
predicate. Returns `nodes` plus `match_count` (returned nodes), `total_count`
(matches before the cap) and `truncated` (`total_count > match_count`).

**Fails closed.** `ui_access_query_validate` rejects, with `ok: false` and a
machine-readable `error`, an out-of-range `limit`, a `canonical_id` with no
`#`, and — critically — a query with *no predicate at all AND no positive cap*,
which would otherwise degrade to "return the whole tree".

**Text matching is case-insensitive and prop-aware.** A session-built button
carries its caption in `props.label`, not `text_value`; an identity-only,
case-sensitive matcher could never find `text:"OK"` on `popup#ok_btn`. The
matcher searches `text_value`, `widget_id`, `canonical_id`, and the texty props
(`label`, `value`, `content`, `placeholder`, `title`, `text`).

### Ensure layer

`ui_access_ensure_result(snapshot, surface_id, canonical_id, kind, text_query,
focused_only, limit, expectation, expected_value) -> UiAccessEnsureResult`

Expectations: `exists`/`present`, `absent`/`missing`, `match_count`/`count`,
`focused`, `enabled`, `visible`, `selected`/`checked`, `value`, `text`.
Produces `satisfied` plus a machine-readable `reason` with a stable leading
code — `query_invalid`, `no_match`, `unexpected_match`, `count_mismatch`,
`state_mismatch`, `value_mismatch`, `unsupported_expectation` — and empty
`reason` when satisfied. State expectations are **non-vacuous**: they require
at least one match.

### Serialization

- `ui_access_query_to_json(result)` — emits `ok`, `error`, `count`,
  `match_count`, `total_count`, `truncated`, `nodes`.
- `ui_access_query_snapshot_to_json(...)` — 7-arg query-then-serialize.
- `ui_access_ensure_to_json(..., elapsed_ms)` — 10-arg, as the caller uses.
- `ui_access_value_to_json(snapshot, canonical_id)` — 2-arg, as the caller and
  `test/01_unit/app/ui/access_spec.spl` use.
- `ui_access_surface_scope_to_json(snapshot, surface_id)` — surface + its owned
  nodes; `"{}"` when absent.
- `ui_access_resolve_action_name(snapshot, canonical_id, requested)` — 3-arg.
  The 2-arg node form is preserved as `ui_access_node_action_name(node, req)`.

## Arity conflicts, and how they were resolved

The task brief treated the callers as authoritative on arity. Three of the
named functions already had **other, pre-existing callers on the old arity**,
so a blind rename would have broken them:

| function | pre-existing 1-arg callers | resolution |
|---|---|---|
| `ui_access_query_to_json` | `src/app/mcp/main_lazy_play_tools.spl`, `src/app/play/wm_access_cli.spl`, `src/app/ui/access_cli.spl` | kept 1-arg `(UiAccessQueryResult)`; added 7-arg `ui_access_query_snapshot_to_json` and pointed the owned caller at it |
| `ui_access_surface_to_json` | `src/app/ui/access_cli.spl`, `src/app/ui.test_api/handler.spl` | kept 1-arg `(UiAccessSurface)`; added `ui_access_surface_scope_to_json` |
| `ui_access_find_nodes` | `src/lib/common/ui/win_text_access.spl` + browser/office specs pass an **i32 limit**; `access_spec.spl` passes a **bool** | kept the i32-limit signature; the owned caller now uses `ui_access_find_nodes_filtered(..., focused, 200)` |

`ui_access_resolve_action_name` had 9 pre-existing 2-arg call sites in
`src/app/ui.test_api/handler.spl`; those were mechanically renamed to
`ui_access_node_action_name`. `handler_test.spl` still passes its action-routing
examples afterwards.

## Root causes found (not drift — real defects)

1. **`index_of` returns `-1`, not `nil`, for "not found"** (verified on both JIT
   and interpreter, `build/uiquery_probe/p1.spl`). `_extract_arg` in
   `_McpOsServer/helpers.spl` guarded only on `nil`, so a *missing* key read from
   `args_json[-1 + len(key)+2 :]` and returned a neighbouring value. For
   `{"surface_id":"popup",...}` the absent `canonical_id` came back as `"popup"`,
   which is why observe/query/state reported "canonical node popup not found".
   Every absent tool argument was silently aliased. Fixed with `< 0` guards on
   all four `index_of` results.

2. **Interpolating a non-nil `Option` renders the wrapper.**
   `_node_state_value`/`_surface_state_value` returned `text?`, and
   `"...{surface_value}..."` emitted `"state_value":"Option::Some(true)"` into
   the JSON. Since `""` is a legitimate value (`window_id`, `app_id`) it cannot
   be the unsupported sentinel, and the Option-destructuring forms all bind nil
   in this tree. Split into `_node_state_supported`/`_node_state_text` (and the
   surface twins) returning plain `text` + a `bool` predicate.

3. **`node.text` did not exist** — the field is `text_value`. `_node_state_value`
   read a non-existent field; now routed through `ui_access_node_value`.

4. **`UiAccessSnapshot` reconstructions omitted `snapshot_revision`**, which
   nil-fills to `3` on the JIT (visible in the pre-fix output as
   `"snapshot_revision":3`). All three reconstruction sites now write it.

## Delegation remedy — applied, and it was load-bearing

All 16 `self.bridge.session.<mutator>(...)` call sites in
`_McpOsServer/{ui_access_tools,dispatch_and_io_tools}.spl` were converted to
one-hop wrappers on `CliGuiBridge` (`dispatch_ui_event`, `bind_window_surface`,
`clear_window_binding`, `clear_window_surface_binding`, `close_surface_handle`,
`update_surface_tree`, `set_surface_widget_value`, `attach_access_store`,
`clear_access_events`, plus the pre-existing `open_surface` /
`set_active_surface`). This moved the spec from 7 failures to 2 — the depth-2
writes were the remaining failures, not a cosmetic cleanup.

New discriminating regression case: *"persists two successive mutations through
the one-hop bridge delegation"* — two successive value writes
(`Ada` → `Grace` → `Hopper`), two successive active-surface changes, and two
successive action dispatches, each asserted with **absolute** values so a
dropped second write is distinguishable from a landed one.

## One assertion corrected (with justification)

`test/01_unit/os/services/llm/ui_access_dispatch_spec.spl` asserted
`expect(bridge.session.active_surface()).to_equal("main")` after a server-side
mutation. `OsMcpServer.new(vfs, bridge)` takes the bridge **by value**, so the
server mutates its own copy and the `it`-local `bridge` can never observe it
(proved by `build/uiquery_probe/p2.spl`). The same file, ~120 lines earlier,
asserts the opposite — that the `it`-local `bridge` is *not* updated by a
server-side action. Under the current value semantics exactly one of the two is
satisfiable. The subject was changed to `server.bridge.session.active_surface()`
(the handle that was actually mutated); the claim being verified is unchanged.
Making both assertions simultaneously true would require `CliGuiBridge` to be
shared by reference, which is a language/runtime property, not a UI-layer one.

Two fixture-only edits in the same file: `UiAccessNode(text: ...)` →
`text_value:` and a missing `snapshot_revision:` — both wrong *constructor field
names*, not assertions, pinned by `test/01_unit/app/ui/access_query_json_spec.spl`
(green, exact-JSON).

## Blocked — 2 examples, outside writable scope

Both remaining failures need `UiAccessStore` persistence, and both die at the
same point: `UiAccessStore.memory()` / `.open(path)` runs
`CREATE INDEX IF NOT EXISTS ...` in `_init_schema`, and the **Rust seed's**
SFFI sqlite shim (`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`,
`sqlite_execute_statement`) implements only CREATE TABLE / DELETE FROM / INSERT
and answers everything else with `unsupported SQL: ...`. `src/compiler_rust/**`
is an explicitly forbidden path for this lane.

- `reads persisted find and history results when a store is attached` — the `?`
  on `UiAccessStore.memory()` propagates that error ("try: early return").
- `auto-attaches a persisted store through CliGuiBridge.new ...` — the runtime
  open returns `nil`, and the example deliberately clears the in-memory event
  ring to prove the event came from the store, so it cannot fall back.

Secondary, related gap found and **not** shipped (reverted, unverifiable on this
binary): the pure-Simple engine's `_parse_create_index`
(`src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl`)
also does not handle `IF NOT EXISTS` — after stripping `CREATE INDEX` it sees
`IF NOT EXISTS idx ...`, finds `NOT` where it expects `ON`, and returns `[]`.
A fix needs a companion "already exists ⇒ Ok(0)" branch in
`_do_create_index`'s duplicate-name check.

Note the binary caveat: `bin/simple` here is the **bootstrap seed** (it prints
the seed banner). These two examples may behave differently on a self-hosted
build.

## Next increment

1. Teach the SFFI sqlite shim `CREATE INDEX [IF NOT EXISTS]` (+ `ALTER TABLE
   ADD COLUMN`, already swallowed by the store), or re-verify the two blocked
   examples on the self-hosted binary. Then land the pure_sql
   `IF NOT EXISTS` fix with a spec.
2. `test/01_unit/app/ui/access_spec.spl` is fully red on a *stale builder API*
   (`column("root").child(...)` — `column` now requires `children`). Its
   query/ensure describes already encode exactly the signatures shipped here and
   should go green once the fixture is migrated. Not touched: outside this
   lane's owned test paths.
3. `ui_access_node_value` still returns `text` (""), while `access_spec.spl`
   expects `nil` for a non-value-bearing node. Changing it affects
   `src/app/ui.test_api/handler.spl:927,936`; deferred deliberately.
4. Decide whether `CliGuiBridge` should be reference-shared. Until then the
   `it`-local-bridge idiom in specs is misleading — assert on
   `server.bridge.session`.
5. `ui_access_find_nodes` still has two contradictory contracts in-tree (i32
   limit vs bool focused). Pick one and migrate the loser's callers.
