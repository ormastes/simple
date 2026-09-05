# `/api/test/click` on `lab_add_cell` reports success but doesn't add a cell

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Found:** 2026-08-07, during notebook-lanes L4 verification
(`test/03_system/tools/simple_lab/lab_shared_ui_contract_spec.spl`).

**FIXED:** 2026-08-08, in `f8e9a1e5ddf2253385eea40e831063cee9c36a82` ("fix(lab):
reject truncated oversized header lines (431) + route test-API clicks to real
app actions"). `lab_test_api_inject_event` in `src/app/simple_lab/lab_server.spl`
now dispatches the event to the generic `LAB_UI_SESSION` layer as before, but
for `Action`/`InputChange` events it additionally resolves the semantic
`click_<widget_id>` action name back to the widget's own declared `action` prop
(`_lab_test_api_app_event`) and forwards it to `LAB_UI_APP.handle_event(...)`
(real `SimpleLabApp` business logic), then rebuilds and re-syncs the widget
tree via `LAB_UI_SESSION.update_tree(LAB_UI_APP.build_ui())`. Re-verified
2026-08-09 on a fresh worktree at this commit:
`SIMPLE_MODULE_LIMIT=4000 bin/simple test
test/03_system/tools/simple_lab/lab_shared_ui_contract_spec.spl` →
`Results: 5 total, 5 passed, 0 failed`, including
`✓ POST /api/test/click on lab_add_cell adds a cell — read-after-write via
GET /api/test/elements`. No further code change needed; sections below are
kept as the original diagnosis record.

## Symptom

`POST /api/test/click {"id":"lab_add_cell"}` against `lab_server.spl`'s L4-added
`/api/test/...` routes returns `200`, `{"ok":true}` — but a follow-up
`GET /api/test/elements` still shows only `cell_0`; `cell_1_editor` never
appears. The click is acknowledged but has no observable effect on the widget
tree the elements endpoint reports.

## Root cause (as far as diagnosed)

L4 wired `/api/test/...` through the shared `handle_test_request` handler
against a `UISession` built from `SimpleLabApp.build_ui()` (L2's widget tree).
The click event is injected into that generic `UISession`/widget-tree layer,
but `SimpleLabApp`'s actual `add_cell()` business logic (which is what really
grows the cell list and stable-ID scheme documented in `main.spl`'s header) is
never invoked by the generic test-API click path — so the click succeeds
against a layer that doesn't own the real state `/api/test/elements` reads
back from afterward. This is the same class of gap L4's own landing report
flagged for `/api/test/type` ("updates the generic widget layer only, not
`SimpleLabApp`'s cell source").

## Impact

Read-after-write proof for interactive mutations (add cell, run cell, etc.)
through the generic `/api/test/...` S4 contract surface is not yet real for
Simple Lab — only read-only endpoints (`status`, `elements`, `element?id=`,
unknown-route 404) are proven end to end. `lab_shared_ui_contract_spec.spl`'s
click-then-read-after-write example is red on this specific assertion; left
RED rather than weakened, per `.claude/rules/testing.md`.

## Unblock condition

The generic test-API click/type handlers need to route through
`SimpleLabApp`'s own event dispatch (whatever function `main.spl`'s toolbar/
cell-button click handlers call) rather than (or in addition to) mutating the
generic widget-tree snapshot — so a `lab_add_cell` click actually calls
`add_cell()` and the elements endpoint reflects the new cell afterward.
