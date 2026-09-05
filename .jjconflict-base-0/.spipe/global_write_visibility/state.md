# Lane GLOBAL — module-global write visibility

**Status:** Root-cause COMPLETE. No fix applied (deliberate — see below).
**Date:** 2026-07-27
**Bug doc:** `doc/08_tracking/bug/module_global_write_invisible_to_callee_2026-07-27.md`

## Verdict

A module-global written inside a `fn` is invisible to every function that `fn`
calls; the write commits only on return. **Interpreter only** — the JIT is
correct.

The original "works from `main()`, fails in a spec" framing is an engine
artifact: `bin/simple run` defaults to the JIT, the spec runner always uses the
interpreter. `SIMPLE_EXECUTION_MODE=interpreter bin/simple run` reproduces it
from a plain `fn main()` with no spec runner involved.

Type, assignment target form, nesting, and same-module vs cross-module are all
irrelevant — 5/5 rows fail uniformly under the interpreter.

## Root cause (file:line)

Module globals are copy-in / write-back, not shared storage.

- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:100-102`
  — `base.extend(owner_globals)` extends LAST at call entry, clobbering the
  caller's fresher values with the committed (stale) owner map.
- `.../function_exec.rs:105` `sync_owned_captured_globals` — publishes the
  writer's overlay only on RETURN (entry `:644,:708,:965,:1056,:1149`,
  exit `:691,:732,:1013,:1081,:1163`).
- The per-statement write-through that would fix this exists **only in the BDD
  colon-block executor**: `interpreter_call/block_execution.rs:311-312` /
  `:321-322` inside `exec_block_closure` (`:206`) and `exec_block_closure_mut`
  (`:1070`). The function-body executor
  `src/compiler_rust/compiler/src/interpreter/block_exec.rs:167 exec_block_fn`
  has none.
- Silent-drop guards: `function_exec.rs:118`, `block_execution.rs:325` discard
  writes to globals absent from the owner map.
- JIT is correct because it uses real data slots:
  `codegen/cranelift_emitter.rs:96-136`.

## Blast radius

1,446 exploitable sites in 208 owned files (2,746 hazardous mutations in 271
files; 13,738 `.spl` scanned). 910 in kernel/sched/alloc/mem/driver/security/
crypto/capability/compiler paths. **Lower bound** — the scan targeted non-bare
write forms only, and bare `G = expr` fails identically.

Worst: `pmm.spl:340` (page refcount / UAF), `capability.spl:1085` (task→vmspace
binding), `syscall_spm.spl:48` (privilege mask), `heap.spl:182` (allocator
accounting), `fd_table.spl:452` (CLOEXEC), `paging.spl:222,230` (all 4 arches).

## Why no fix landed

The fix belongs in `src/compiler_rust/**`, which has a **live lane (CAPFIX2)**.
Per lane rules, not raced. Three options are written up in the bug doc
(§Fix sketch): (a) lift the seed/sync into `exec_block_fn` — cheap, partial;
(b) sync on every write via the existing place model — covers all rows;
(c) shared `Rc<RefCell>` global slots, deleting copy-in/write-back — correct,
matches JIT and the pure-Simple interpreter, needs its own lane.

## Workaround (in effect today)

Build in a local, publish once. A function that writes a module global must not
call anything that reads it. Already applied in `src/os/kernel/smp/percpu.spl`
(see comment at `:39-45`).

## Artifacts

`build/global_repro/` — modules (`gmod.spl`, `gtf.spl`), drivers
(`main_ctl.spl`, `main_cross.spl`, `target_form.spl`), specs (`g_spec.spl`,
`g2_spec.spl`, `g3_spec.spl`, `gtf_spec.spl`), transcripts (`out_*.txt`).
Backup of the bug doc: `/tmp/global_bug_backup.md`.

## Follow-ups filed in the bug doc

- Separate defect: same-module module-level `var` is rejected as immutable by
  the interpreter (`invalid assignment: cannot reassign to immutable variable`)
  while the JIT accepts the identical file. Deserves its own bug.
- Regression spec to add with the fix:
  `test/01_unit/compiler/module_global_write_visibility_spec.spl` — must run on
  the interpreter; a JIT-only run is a false green (every row passes there).
