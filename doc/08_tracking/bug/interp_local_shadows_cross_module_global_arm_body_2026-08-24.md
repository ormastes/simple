# Interpreter: a function-local binding writes through to a same-named module-global in another module (2026-08-24)

- **Status:** OPEN
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
