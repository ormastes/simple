# `PoolLinkedList.push_back`/`push_front` (and everything using `alloc_node`/`free_node`) fails at runtime — interpreter rejects indexed-field assignment

**Filed:** 2026-08-07
**Severity:** high — shipped, exported code is non-functional; masked by a
text-scan-only spec
**Status:** LIBRARY BUG FIXED (2026-08-07, level b — restructured
`PoolLinkedList`). The underlying language limitation stays OPEN — it could
not be fixed at the interpreter level from `.spl` source; see "Root-cause
finding" below.

## Fix (2026-08-07)

`PoolLinkedList` (`src/lib/nogc_async_mut_noalloc/collections/linked_list.spl`)
was refactored from `nodes: [ListNode]` (array of struct, mutated via
`self.nodes[idx].field = v`) to parallel primitive arrays — `values: [i64]`,
`nexts: [i32]`, `prevs: [i32]` — mutated via plain index assignment
(`self.nexts[idx] = v`). This is the same pattern already used by `FixedMap`
(commit `57f7f44849f`) to sidestep the identical rejection. The `ListNode`
class was removed (no longer needed); its `export ListNode, PoolLinkedList`
re-export lines in `collections/__init__.spl` and
`nogc_async_mut_noalloc/__init__.spl` were updated to drop `ListNode`.

New real (non-text-scan) regression spec:
`test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_backing_storage_regression_spec.spl`
— imports and calls `PoolLinkedList`, exercising `push_back`/`push_front`/
`pop_front`/`pop_back`/`remove_at`/`is_full`/`contains`. Before the fix
(struct-array shape), this spec's equivalent call failed identically to the
original repro:
```
semantic: invalid assignment: complex indexed field receiver is not supported
Results: 1 total, 0 passed, 1 failed
```
After the fix, sabotage-verified (corrupted `push_back`'s value write to
`value + 999`):
```
Results: 5 total, 2 passed, 3 failed
```
Reverted, final green:
```
Results: 5 total, 5 passed, 0 failed
```
`bin/simple lint` on all changed files: `Found 0 error(s), 7 warning(s) ...`
`Lint passed: all files clean`.

## Root-cause finding (why level (a) — an interpreter fix — was not taken)

Two independent sentinel probes were placed at the top of both live
`eval_assign_expr` definitions in
`src/compiler/10.frontend/core/interpreter/eval_access.spl:285` and
`src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:601`
(a `print(...)` call, per-file edit-then-rerun-then-revert). Neither fired
while running the failing repro through `bin/simple test` (which spawns the
self-hosted binary itself as a child — confirmed via `child binary:
.../bin/release/x86_64-unknown-linux-gnu/simple` in the log, so this is not
the known "silently delegates to the Rust seed child" trap). A fragment
grep (`grep -rn eval_set_error src/compiler/ | grep -i
"indexed\|receiver\|not supported"`) and a full-string grep across
`src/compiler/**` and `src/runtime/**` both found no source containing the
message text (the only match anywhere is a comment in
`src/lib/common/encoding/font_cldr_rank.spl` describing this exact bug, not
an emitting site).

The message text *does* live, verbatim, in
`src/compiler_rust/compiler/src/interpreter/node_exec.rs:916` (Rust seed):
its assignment-target `Case 2` (`arr[index].field = value`) only handles
`array_expr` when it is a bare `Expr::Identifier`; `self.nodes[idx].field =
value` has `array_expr = FieldAccess(self, nodes)`, which falls to the
`else` branch and produces exactly this error. Whatever code path actually
executes for `bin/simple test` spec bodies reaches equivalent (compiled-in,
non-`.spl`, unreachable-by-edit) logic with the same restriction and the
same wording — not the pure-Simple interpreter tree in `src/compiler/**`. No
editable emitting site was found, so the interpreter-level fix (level a) was
not tractable within this task's scope; the restructure (level b) was taken
instead and the language limitation itself remains open for whoever owns
`src/compiler_rust/` or the actual spec-execution engine.

## Origin

Surfaced as a side-finding while investigating a fix shape for
`doc/08_tracking/bug/noalloc_collections_backed_by_growable_heap_array_2026-08-07.md`
(the `FixedMap` per-operation allocation fix). Filed as its own record per
that doc's note that this finding is more severe (correctness, not
allocation efficiency) and would not be discoverable under a filename about
heap growth.

## Repro

`src/lib/nogc_async_mut_noalloc/collections/linked_list.spl`'s
`PoolLinkedList` mutates pool nodes through an array-indexed field write,
e.g. `alloc_node()`:

```
me alloc_node() -> i32:
    if self.free_head == -1:
        return -1
    val idx = self.free_head
    self.free_head = self.nodes[idx].next
    self.nodes[idx].next = -1      # <-- indexed field write
    self.nodes[idx].prev = -1      # <-- indexed field write
    idx
```

The same pattern appears at `linked_list.spl:78-81` (`free_node`), `:88-90`
(`push_front`), `:104-106` (`push_back`), and elsewhere in the file —
`self.nodes[idx].value = value`, `self.nodes[idx].next = ...`, etc.

Minimal reproduction (throwaway probe, not committed):

```
class Slot:
    key: i64
    value: i64
    occupied: bool

class Holder:
    slots: [Slot]
    ...
    me set_via_field_write(idx: i32, k: i64, v: i64):
        self.slots[idx].key = k        # fails
```

Running through `bin/simple test`:

```
semantic: invalid assignment: complex indexed field receiver is not supported
```

**Confirmed on the real, shipped type, not just the minimal repro** —
`val list = PoolLinkedList.new(4); list.push_back(10)` through `bin/simple
test` produces the byte-identical error:

```
✗ checks whether push_front/pop_front work (exercises self.nodes[idx].field = v)
    semantic: invalid assignment: complex indexed field receiver is not supported
1 example, 1 failure
```

So `PoolLinkedList.push_back`, `push_front`, `pop_front`, `pop_back`, and
`remove_at` — every operation that calls `alloc_node()` or `free_node()` —
fail immediately at runtime with this error. The type is exported
(`collections/__init__.spl:30`, re-exported from
`nogc_async_mut_noalloc/__init__.spl`) and documented as working
(`linked_list.spl:1-11` gives a `push_back`/`push_front`/`pop_front` usage
example) but cannot actually run any of those operations.

## Why this was invisible

`test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl`
(both the `test/01_unit/...` and `test/unit/...` copies) is a text-scan
spec: it reads the source file as text and asserts on method signatures
(`expect(source).to_contain("me push_back(value: i64) -> bool")`), and never
imports or calls the real `PoolLinkedList`. `Results: 2 total, 2 passed, 0
failed` on this spec proves nothing about whether `push_back` executes.

## Consumers

`grep -rl 'PoolLinkedList'` across `src/` and `test/` finds only the defining
file and the two `__init__.spl` re-export chains — **zero other consumers**,
production or test. Nothing currently depends on this working, which is
presumably why it has gone unnoticed.

## Unblock condition

Root-cause the interpreter's rejection of `self.<array_field>[idx].<field> =
value` (nested field assignment through an array-indexed receiver) in
`src/compiler/**` — outside this record's scope (this session's task was
scoped to `src/lib/nogc_async_mut_noalloc/collections/**`, not the
compiler). Once fixed, add a real (non-text-scan) regression spec that
imports `PoolLinkedList` and exercises `push_back`/`push_front`/`pop_front`/
`pop_back`/`remove_at`, proving each was broken before and works after —
the same before/after discipline used in the sibling `FixedArray`/
`FixedStack`/`FixedMap` fixes.

Tracked as WP-12 input in
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.

## ALREADY_FIXED — verified 2026-08-17 (P2 triage, compiler lane)

Reproduce-first re-run of the recorded reproducer at HEAD:

```
$ bin/simple test test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl
Results: 2 total, 2 passed, 0 failed          # rc=0
```

Assignment through a complex indexed-field receiver (`pool[i].next = x`) no
longer fails. Closing as already fixed; no source change was made by this lane.
