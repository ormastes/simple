# Interpreter: a function-local binding writes through to a same-named module-global in another module (2026-08-24)

- **Status:** SUPERSEDED — 2026-11-11 (lane interp8): round-8 fix (1889cc95543d) verified live on the fresh seed (build 46fe8f6b6def); acceptance spec 2/2 under `--mode=interpreter`. The 2026-11-10 LIVE reading was stale-binary build skew, as the same-day seedfix lane diagnosed.
- **Severity:** HIGH — silently corrupts compiler arena state; the observable
  failure surfaces several layers away and names neither the variable nor the file
- **Area:** seed interpreter variable scoping / global environment
- **Found by:** root-causing
  `doc/08_tracking/bug/io_runtime_import_breaks_native_build_len_on_i64_2026-08-24.md`

## What was observed

`src/compiler/10.frontend/core/_Ast/decl_nodes.spl:1240` owns a module-global
arena `var arm_body: [[i64]] = []`.

`src/compiler/10.frontend/core/parser_stmts.spl` (a DIFFERENT module) declared
function-local bindings of the same name and a different type:

```
:1790   val arm_body = parse_block()          # [i64]
:1827   var arm_body: [i64] = []
:1956   val arm_body = parse_block()          # [i64]
```

Probes inside `arm_new_with_binding_and_rationale` show the arena is correct
immediately after each push (`arm_body=[[0], [1]]`), and a probe in
`flat_decl_pools_dump` shows it is `[1]` — the last arm's flat body — by the time
the frontend cache is written. Renaming the three parser locals to
`case_arm_body` (nine token replacements, no behaviour change) makes the
corruption disappear entirely.

So the parser's local write reached the other module's global.

## Why it matters beyond the one symptom

The victim here was an arena, so the corruption showed up as
`method 'len' not found on type 'i64' (receiver value: N)` raised inside
`flat_pool_enc_i64`, on the frontend cache STORE path, with no source location
and no mention of `arm_body`, `parser_stmts.spl` or `match`. Three prior
investigation lanes chased the import graph, an import cycle, tuple-returning
externs, and a recent typing change before the interpreted call stack pinned it.
Any same-shaped collision elsewhere would be equally invisible.

## NOT characterized — read before assuming a general rule

"Any same-named local clobbers the global" is **too strong**, and this tree
contains the counterevidence. A scan of `src/compiler/10.frontend/core/**` for
locals sharing a name with an `_Ast/**` module-global found these, which do NOT
fire (the same build now completes parse and cache-dump cleanly):

| site | local | global |
|---|---|---|
| `parser_decls_use.spl:475,488,506,524` | `val decl_span` (`i64`) | `decl_span: [i64]` |
| `_ParserDecls/fn_struct_decls.spl:666,724` | `val decl_span` (`i64`) | same |
| `_ParserDecls/enum_module_body.spl:571,918` | `val decl_span` (`i64`) | same |
| `interpreter/eval_decls.spl:29` | `val decl_name` | `decl_name: [text]` |
| `compiler/cg_stmt.spl:518` | `val arm_body` | `arm_body: [[i64]]` |

What distinguishes the firing site from these is unknown. Candidate differences
worth testing: `var` vs `val`; whether the local is reassigned after
declaration; whether the local is passed as an argument to a function in the
global's owning module; whether the global's owning module has been entered
before the local is bound. None of these was tested.

These sites are deliberately **not** renamed. They provably do not misbehave, and
renaming working code on a theory would be speculative churn.

## Repro

The seven-line reproducer in the companion record, run against a tree where
`parser_stmts.spl` still carries the `arm_body` locals.

## Diagnostic technique that found it

`SIMPLE_INTERP_OOB_DEBUG=1` at the "method not found" site prints a Rust
backtrace only, which names interpreter dispatch frames, not interpreted code.
Adding `crate::interpreter::debug_call_stack_snapshot()` to that probe (the
stack is populated when `SIMPLE_DEBUG_FIELD_ACCESS=1`) prints the interpreted
`.spl` call stack and pinned the failing function in a single 21 s run. That
probe enhancement is worth landing in the seed; it is level-gated and default
off.

## 2026-11-06 round 8: FIXED
Root cause: plain `name = value` ran the "also sync to MODULE_GLOBALS if it exists there" step by bare name even when `name` is a function-local that merely shares its name with a global, publishing the local into the flat global store. The four sync sites in `exec_assignment` now skip locals. Spec: test/01_unit/compiler/interpreter/local_shadows_module_global_spec.spl (RED on seed, GREEN after).

## 2026-11-10 triage — LIVE on worktree seed, routed (seed-smoke, lane p3-interp3 row 15)

The round-8 source fix (`1889cc95543d`; four `env.is_local(name) ||` guards in
`exec_assignment`, `src/compiler_rust/.../interpreter/node_exec.rs:1424/1457/1488/1553`)
IS in this branch's source and the committed binary carries round-8-unique
strings, yet the failure reproduces on the worktree seed:

- `bin/simple.exe test test/01_unit/compiler/interpreter/local_shadows_module_global_spec.spl`
  -> 2 total, 0 passed, 2 failed ("expected 2 to equal 1";
  "semantic: variable `r8a_slots` not found").
- Direct probe (`build/p3fix-interp3/row15_probe.spl` + `shadow_arena2.spl`):
  `SIMPLE_EXECUTION_MODE=interpreter` -> `global_len=2` (the local
  reassignment `r8a_arena = [7]` still publishes into the cross-module
  global); default (JIT) -> `global_len=1` (correct).

Residual hole or build skew in the seed — either way the fix surface is
`src/compiler_rust`, which is write-forbidden to this lane (agent-10 active).
Routed to the compiler-seed lane; spec and probe stay RED as the acceptance
test. Note the second `it` (round-8 fixed-size module arrays,
`interpreter_fd_ownership_private_module_globals_not_linked_2026-08-12`) fails
on the same binary too.

## 2026-11-10 P3 seedfix lane — BUILD SKEW, round-8 fix present and correct (no source fix)

Routed today as "guard IS in source but FAILS at runtime — residual hole or build
skew". Finding: BUILD SKEW. The round-8 fix (1889cc95543d) is present and correct in
this branch's source: the four `env.is_local(name) ||` guards in
`interpreter/node_exec.rs` (1424/1457/1488/1553) AND the `module_global_target`
`is_local` early-return in `interpreter_call/block_execution.rs:34`. A FRESH debug
AND release build from HEAD source passes the acceptance spec
`test/01_unit/compiler/interpreter/local_shadows_module_global_spec.spl` 2/2.

The deployed `bin/simple.exe` (git blob 1e46cf298, committed 9e7e7a526edb) fails the
same spec 2/2 ("expected 2 to equal 1"; "r8a_slots not found") — the committed seed
binary predates the round-8 fix. The residual-hole hypothesis is ruled out by the
fresh build passing.

Action: no source change (correctly — modifying working code on the stale-binary
symptom would be speculative churn). The .spl acceptance spec is the
regression/acceptance lock and passes on a fresh build. Recommend a seed
rebuild+redeploy so the deployed binary matches source. Evidence:
build/review/p3fix-seedfix-20261110.sdn.


## 2026-11-11 triage — SUPERSEDED (seed-smoke, lane interp8)

Re-ran the round-8 acceptance spec on the fresh worktree seed (build-commit
`46fe8f6b6def`, `SIMPLE_LIB=src`, `--mode=interpreter --no-cache`):
`bin/simple.exe test test/01_unit/compiler/interpreter/local_shadows_module_global_spec.spl`
-> 2 total, 2 passed, 0 failed. The local reassignment no longer publishes
into the cross-module global, and the fixed-size module-array `it` is green
on the same run.

This confirms the same-day seedfix lane's BUILD-SKEW diagnosis: the round-8
fix (`1889cc95543d` "interp: round 8 fixes (part A)") is present in source
AND carried by the current deployed seed; the spec is the acceptance lock and
is GREEN. The second `it` (round-8 fixed-size module arrays) covers
`interpreter_fd_ownership_private_module_globals_not_linked_2026-08-12` —
see that record's 2026-11-11 addendum (3/3 on the same binary).
