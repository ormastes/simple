# todo-scan records every TODO as `status: open`, including `[blocked:...]` ones

Date: 2026-08-18
Status: fixed
Area: process / tracking

## Symptom

`doc/08_tracking/todo/todo_db.sdn` has a `status` column with curated `blocked`
rows, but `bin/simple todo-scan` can never produce one: `scan_file`
(`src/app/todo_scan/main.spl`) hardcoded `status: "open"` for every entry, even
when the marker carried a `[blocked:<reason>]` tag that the same function
already parsed into the `blocked` column. Any rescan therefore flattens the
curated blocked rows back to `open`, and blocked work becomes indistinguishable
from actionable work when the db is triaged by `status`.

A second, independent defect in the same parser: `[#issue]` was extracted by
truncating everything after the tag, so a marker written
`... [#42] [blocked:reason]` lost its blocked tag entirely.

## Reproduce (RED, before the fix)

Fixture `/tmp/tdscan/src/fixture.spl`:

```
# TODO: [demo][P1] blocked demo item [blocked:no-self-hosted-deploy]
# TODO: [demo][P2] plain actionable item
```

`bin/simple run src/app/todo_scan/main.spl` from `/tmp/tdscan` emitted:

```
    0, TODO, demo, P1, "blocked demo item", src/fixture.spl, 1, , "no-self-hosted-deploy", open, true
    1, TODO, demo, P2, "plain actionable item", src/fixture.spl, 2, , "", open, true
```

Both rows `open` despite row 0 carrying a blocked reason.

## Fix

`src/app/todo_scan/main.spl`:

- derive `status` from the parsed blocked tag (`blocked` when non-empty,
  otherwise `open`);
- when stripping the `[#issue]` and `[blocked:...]` tags out of the description,
  keep the text on BOTH sides of the tag instead of truncating, so the two tags
  are order-independent and neither erases the other.

## GREEN

Same fixture after the fix:

```
    0, TODO, demo, P1, "blocked demo item", src/fixture.spl, 1, , "no-self-hosted-deploy", blocked, true
    1, TODO, demo, P2, "plain actionable item", src/fixture.spl, 2, , "", open, true
```

Specs:

```
SPEC FILE VERDICT: test/01_unit/app/todo_scan_blocked_status_spec.spl outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0
Results: 2 total, 2 passed, 0 failed
SPEC FILE VERDICT: test/01_unit/app/todo_scan_blocked_status_class_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
Results: 6 total, 6 passed, 0 failed
```

## Row amended

`todo_db.sdn` row 676 (`sspec-verification`, P1) carried
`blocked = "no-self-hosted-deploy"` with `status = open`; its marker at
`test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl:40`
says `[blocked:no-self-hosted-deploy]`. Status corrected to `blocked`, which is
what the fixed scanner now emits.

## Premise audit of the P1 rows in the small non-compiler areas

All 21 in-scope P1 rows were checked. Every cited file path resolves — no
drifted citations in this set. Three rows are already `status: done`
(528 renderdoc, 553/576 engine2d). Of the remaining 18, seventeen are
`status: blocked` and one (676) was mislabelled `open` by the defect above.
Their blockers are genuine and were verified, not assumed:

- `bin/simple` here resolves to the Rust bootstrap seed and says so in its own
  banner, so every "close only on a provenance-admitted pure-Simple runtime"
  row (673, 674, 676, 681, 686, 687, 688, 807, 817, 818, 822, 829) cannot be
  closed in this environment. The sentinel spec
  `live_capture_blocker_sentinels_spec.spl` is GREEN
  (`Results: 2 total, 2 passed, 0 failed`), which is itself the positive proof
  that the seed is still what is deployed — it is written to turn RED the moment
  a self-hosted binary is deployed.
- 684/685 need a physical EDID-bearing 7680x4320 80 Hz display; 810/811/812/813
  need live Vulkan GPU receipts; 807 needs an RV64 QEMU lane. All fall under the
  standing environment-skip decision.

No row in this set was found to describe a defect that no longer reproduces.
