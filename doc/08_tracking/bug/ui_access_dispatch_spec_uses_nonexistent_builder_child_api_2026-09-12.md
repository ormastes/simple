# `ui_access_dispatch_spec` is written against a `column(id).child(...)` builder API that does not exist — 13 of 13 examples red

- Status: OPEN (2026-09-12)
- Found by: BUGFIX-2 fan-out lane, while re-checking
  `selfhost_two_hop_field_method_mutation_lost_2026-07-27` (whose record names this
  spec as "the only covering spec"). The 13 failures are NOT that bug.
- Severity: medium — the spec is the named coverage for a high-severity mutation
  defect and has executed zero useful assertions for as long as this has stood.
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  sha256 `3d120a6f`

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 bin/simple test test/01_unit/os/services/llm/ui_access_dispatch_spec.spl --no-session-daemon
SPEC FILE VERDICT: outcome=ERROR declared>=13 executed=13 passed=0 failed=13 skipped=0 dropped=0
```

All 13 fail with the same message:

```
semantic: function expects argument for parameter 'children', but none was provided
```

## Cause

`test/01_unit/os/services/llm/ui_access_dispatch_spec.spl:26` builds its tree as

```simple
val root = column("root").child(
```

i.e. one-argument `column` plus a `.child(...)` chaining method. Neither exists:

```
$ grep -n 'fn column' src/lib/common/ui/builder.spl
31:fn column(id: text, children: [WidgetNode]) -> WidgetNode:

$ grep -rn 'fn child' src/lib/common/ui/
src/lib/common/ui/widget_store.spl:146:    fn children_from(store: WidgetStore) -> [WidgetNode]:
src/lib/common/ui/widget_store_ops.spl:274:    fn children() -> [WidgetNode]:
src/lib/common/ui/widget_store_ops.spl:294:    fn child_count() -> i32:
src/lib/common/ui/widget_store_ops.spl:300:    fn child_at(index: i32) -> WidgetNode?:
```

`children` is a required positional parameter with no default, and there is no
`child` method on `WidgetNode` — only the read-side `children()`, `child_count()`
and `child_at()`.

## Two possible fixes — not chosen here

1. The builder was meant to support fluent chaining and lost it: give `column` (and
   its siblings) `children: [WidgetNode] = []` and add a `child(node)` method that
   returns a new `WidgetNode`. This makes the spec compile as written, but it adds
   public builder API and needs its own coverage.
2. The spec was written speculatively and should be rewritten to the real API:
   `column("root", [ ... ])`.

Deciding between them needs the UI builder owner, since option 1 changes a public
stdlib surface. Not fixed in the bug-fix shard that found it.

## Knock-on

`selfhost_two_hop_field_method_mutation_lost_2026-07-27` cites this file as its only
covering spec. That citation is currently worthless — the spec cannot reach any
assertion, so it can neither confirm nor refute the two-hop mutation defect.
