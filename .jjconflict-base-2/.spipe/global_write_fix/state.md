# Lane GFIX — module-global write-visibility defect

**Bug:** `doc/08_tracking/bug/module_global_write_invisible_to_callee_2026-07-27.md`
**Status:** FIXED (interpreter), verified 2026-07-28. Not committed (lane is no-commit).
**Scratch binary (fix):** `build/gfix_out/simple`
**Scratch binary (baseline, fix reverted, same tree otherwise):** `build/gfix_out/simple_base`
**Source backups:** `build/gfix_backup/function_exec.rs.fix` / `.base`

## Fix option chosen

**Option (b'), publish-on-write-at-call-entry.** One new function
`publish_live_owned_globals(env)` in
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`,
called at the five `exec_function_*` entry points immediately before
`captured_env_with_live_globals` builds the callee env.

Why this and not (a) or (c):

- **(a) lift the BDD `Node::Assignment` seed/sync into `exec_block_fn`** is a
  *partial* fix by construction — `resolve_module_global_target` only handles
  `Expr::Identifier` targets, so indexed (`g[i] = v`), field (`g.f = v`) and
  bare mutating-method (`g.push(v)`) writes stay broken (truth-table rows 3 and
  4). Rejected.
- **(c) shared `Rc<RefCell<Value>>` global slots** is the right end state but
  rewrites the env/value model, deletes `captured_env_with_live_globals` and
  `sync_owned_captured_globals`, and touches every read path. Too large to land
  safely in one lane. Left as the follow-up.
- **(b') publishes the writer frame's *env overlay*, not a parsed assignment
  target**, so it is target-form agnostic — it covers every write form at once,
  which is what makes it a total rather than partial fix. Publishing at call
  entry (rather than after every statement) is the minimum number of publish
  points that is still correct: a write is only observable to another frame
  across a call. Cost is one overlay scan per call — the same order as the
  existing per-return `sync_owned_captured_globals`.

**Safety argument.** The publish predicate is deliberately *identical* to the
existing return-path predicate (overlay entry, present in the owner map, not a
frame-local; params are marked local by `execute_function_body`, so the extra
`func.params` filter there is subsumed). The *set* of names published is
therefore unchanged — only the timing moves earlier. The fix cannot publish a
name the return path would not already have published. Only **overlay** entries
are published, never base entries, so a frame that merely inherited a snapshot
can never write a stale snapshot back over a newer value.

The two silent-drop guards (`function_exec.rs` `!owner_globals.contains_key`,
`block_execution.rs` `if globals.contains_key`) were **kept**: they do not mask
this fix (the repro globals are all declared and present in the owner map), and
removing them would promote every unmarked temporary in a frame overlay to a
module global — a much larger semantic change than the correctness fix needs.
Filed as a follow-up in the bug doc.

## Diff shape

Single file, `interpreter_call/core/function_exec.rs`:
- +1 function `publish_live_owned_globals` (~35 lines + doc comment)
- +5 call sites, one line each, at
  `exec_function_with_values_and_self`, `exec_function_with_captured_env`,
  `exec_function_inner`, `exec_function_with_values_and_writeback_inner`,
  `exec_function_with_bound_args_inner`.
No other file changed. No signature changes.

## Regression spec added

- `test/01_unit/compiler/global_write_visible_to_callee_spec.spl` (13 examples)
- `test/fixtures/global_write_visibility/gwv_owner.spl`
- `test/fixtures/global_write_visibility/gwv_reader.spl`

Covers scalar / whole-array / indexed / push-loop / nested-if writes, each
asserted from a same-module callee **and** from a callee in another module, plus
a mid-write ordering case and two write-back-on-return controls. Each writer
returns what its callee observed, so every expectation is an assertion about the
callee's mid-write view.

Guard value: **2/13 on the baseline binary, 13/13 with the fix.** (The 2 that
pass on the baseline are the write-back-on-return controls, which must stay
green — they do.)

## Follow-ups not done here

1. Option (c) — real shared global storage — remains the correct end state.
2. The silent-drop guards should create-or-raise rather than discard.
3. Separate pre-existing defect, unchanged by this fix: a module-level `var` in
   the **entry** file (spec file or `fn main()` module) is rejected under the
   interpreter with `cannot reassign to immutable variable`
   (`build/global_repro/main_ctl.spl`, `g_spec.spl`). Deserves its own bug.
4. The `fd_table_spec` residual 6/20 is the DEPTH / two-hop place-model defect,
   not this one — unchanged by this fix (14/20 before and after).
5. Arg-evaluation ordering hole (pre-existing): a global written *during*
   evaluation of a callee's arguments is not seen by that callee, because
   `captured_env_with_live_globals` runs before `bind_args`. Not in the truth
   table; not addressed.
