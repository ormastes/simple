# MIR lowering access violation in `_assistant_child_tasks_append` (mcp closure)

- **id:** `mir_lower_child_tasks_append_access_violation_2026-10-19`
- **status:** fix-implemented-verification-pending (source fix landed; workaround tag kept until a rebuilt native producer passes the repro)
- **severity:** blocks Phase 4 `src/app/mcp/main.spl` native build on Windows
- **DB reconciliation:** pending — the qualified `simple check-dbs` / bug DB
  command was not available on this host; this dated record carries the fields.

## Original failure

Phase 4 early check (`C:/dev/simple-bootstrap-storage/p4check-20261019/check-one.shs mcp`),
producer `scope-producer-3d9d-20261018/strict-link-preparation/simple-scope-diagnostic-strict.exe`
(source `ee3d4d7359a`), project tree `d862cc6b9fc`:

```
error: ICE[mir_lower] module app.mcp.assistant.session_store_helpers (attributed):
  worker died inside this module (worker exit status -1073741819)   # 0xC0000005
```

Receipt `build/ice/38916_n6362048407940886807/ice_receipt.tsv` (p3build tree).
HIR passed 11/11. The nearby `E-MC-ANY-002` warnings
(`json_parse_with_error`) are unrelated advisories.

## Localization (evidence)

The MIR worker's `[mir-lower]` trace (`SIMPLE_COMPILER_PHASE_PROFILE=1`) ends inside
`_assistant_child_tasks_append`, statement 2 (the `for item in items:` loop): the
loop body block `stmts=0 has=true` prints `block:value-read` and then the process
dies before the then-arm's `block:start`. So the fault is inside `lower_if`
before the then-block is lowered — i.e. lowering the `and` condition
`value.task_id != "" and item.task_id == value.task_id` (class-field reads on a
parameter and on the loop variable), or the merge-slot setup.

Reproduced in an isolated sparse worktree at `d862cc6b9fc` with the same producer
and the check-one environment (4 threads):

| run | debugger/injection | `_assistant_text_list_append_unique` lowered before the crashing fn | result |
|-----|--------------------|-----------------------------------------------------|--------|
| original p4check | none | yes | 0xC0000005 |
| m4, m6 | none | yes | 0xC0000005 (same trace point) |
| m2, m5 | none | no | links (unrelated extern link errors) |
| m11, m13, m42 | lldb attach (early or late) | yes | no crash |
| m31 | remote-thread DLL injection | yes | no crash |
| 6 more lldb runs | lldb | no | no crash |

Facts established:

1. Per-module function lowering order is randomized per process
   (`module.functions.values()` over `Dict<SymbolId, HirFunction>`); module order is stable.
2. Without any attached debugger, the crash occurred in every run where
   `_assistant_text_list_append_unique` (same param names `items`/`value`,
   `value.trim()`, an early `return items`) was lowered earlier in the same module, and
   in no run where it was not.
3. Any extra thread in the worker (lldb attach — even late, at the start of the preceding module
   — or a `CreateRemoteThread` VEH injection) suppresses the crash. That points at a heap-layout
   dependent memory-safety defect (use-after-free / stale reference inside the per-module transient
   MIR scope, or a dict probe over a stale carrier) rather than a deterministic logic error, and it
   prevented capturing a faulting PC. No WER report is produced on this host.
4. A single-file fixture with the same function shape (struct record) and one run of an entry
   importing only `session_store_helpers` both lowered cleanly (single samples; function order of
   the latter not recorded).

## Workaround (active)

`src/app/mcp/assistant/session_store_helpers.spl::_assistant_child_tasks_append` — tagged
`# @workaround bug=mir_lower_child_tasks_append_access_violation_2026-10-19 recover=cd6206a31bf`.
The loop-tail `if <and-condition>: ... else: ...` expression is replaced by a statement-form `if`
on a helper predicate `_assistant_child_task_replaces(item, value_task_id)` that pushes a chosen
value. Semantics are identical (replace the entry with a non-empty, equal `task_id`, else keep;
append if not found). Recovery commit for the intended form: `cd6206a31bf`.
Workaround commit: see the PR that introduced this record.

## Remaining work (background fix owner: MIR lowering, 50.mir)

- Capture the faulting PC without perturbing the heap (WER `LocalDumps` needs admin on this host;
  attaching or injecting suppresses the fault). With a PC, symbolize against
  `strict-link-preparation/strict-link.map`.
- Audit `lower_if` → `lower_mcdc_decision` → `lower_cond_expr` (Binary And with field reads) and
  `present_collection_binding` for reads of state written by a previously lowered function in the
  same transient scope.
- Prevention test: the original form lowered after `_assistant_text_list_append_unique` in the
  mcp closure, repeated without a debugger, must not fault.
- Retire the workaround only after a rebuilt producer passes that test (see
  `doc/07_guide/tooling/bug_linked_workarounds.md`).

**Revalidated 2026-11-02: still plausible because the report title (native MIR lowering access-violates on the loop-tail `if a.f != '' and b.f == a) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Root-cause analysis 2026-11-03 (opus fix lane)

- Condition path read: `lower_if` (`src/compiler/50.mir/mir_lowering_stmts.spl:3656`) -> `lower_mcdc_decision` (:3103, returns `lower_cond_expr` when MC/DC is off) -> `lower_cond_expr` (:3368) -> `lower_cond_operand`; `present_collection_binding` (:3584) returns `missing` immediately for this cond (right side is not `NilLit`). None of these read per-function state left by a previous function. Every `Dict<i64,...>` lowering field not cleared by `reset_function_local_tracking` (`_MirLowering/function_lowering.spl:350`) is module/symbol-scoped (globals, externs, field maps), not LocalId-scoped.
- New prevention spec `test/01_unit/compiler/mir/child_tasks_append_lowering_spec.spl` lowers the ORIGINAL form (`cd6206a31bf`) right after a same-param-name `items`/`value` function with `value.trim()` + early `return items`, 3 rounds: **PASS** under the seed interpreter (`bin/simple.exe run <spec>`). The MIR lowering logic is therefore correct for this shape; the 0xC0000005 is a memory-safety defect in the **natively compiled** producer (codegen/runtime of the compiler binary), consistent with facts 1-3 above (heap-layout dependent, suppressed by any extra thread).
- Concrete blocker: reproducing needs the native strict producer (`simple-scope-diagnostic-strict.exe` / stage2) run without a debugger plus a faulting PC; lane rules forbid touching stage2 and no WER LocalDumps (admin) are available on this host. Status stays open, workaround tag kept. Repro once a stage3 producer exists: native-compile `src/app/mcp/main.spl` with the workaround reverted to `cd6206a31bf`'s form, 10 runs, no debugger; any 0xC0000005 in `app.mcp.assistant.session_store_helpers` reproduces it.

## Source audit and fix 2026-11-03 (comp-mirav2)

Dumping the MIR of the original form (seed interpreter) showed the real defect:
a statement-position `if ...: <unit stmt> else: <value stmt>` is lowered by
`lower_if_chain` (`src/compiler/50.mir/mir_lowering_stmts.spl`), which copies each
arm's value into a shared `result` temp only in arms yielding a non-unit value.
Then-arm ends in `found = true` (unit); else-arm ends in `out.push(item)` (value),
so `Copy 14 <- 4` exists only on the else edge and `if_chain_merge` (bb5) has an
operand (14) undefined on the then edge (bb9 -> bb5). Backends that materialise
the merge operand (phi / value lookup) dereference a NULL value there; this is
layout/heap dependent, which matches the earlier "extra thread suppresses it"
observations. `lower_if` has the same pattern (`merge` block).

Fix: when the if/chain has an else and no expected type, emit a dominating default
`Const 0` for `result` in the entry block before the branch; arms overwrite it.

Spec: `test/01_unit/compiler/mir/child_tasks_append_lowering_spec.spl` second
example runs a forward must-defined dataflow over the lowered MIR and asserts
that every Copy-defined arm result at a `merge` / `if_chain_merge` join is defined
on every incoming edge. Before: FAIL (`local 14 undefined on edge bb9 -> join bb5`);
after: PASS (seed interpreter, `bin/simple.exe test <spec>`).

Native verification (needs a stage3 producer): native-compile `src/app/mcp/main.spl`
with `_assistant_child_tasks_append` reverted to the form of `cd6206a31bf`, 10 runs
without a debugger; no 0xC0000005 in `app.mcp.assistant.session_store_helpers`
expected. Then retire the `@workaround` tag.
