# SVM-G Task D4 lowering pass — deferred subset (design §4.4)

Status: 2 open, in-subset-but-not-yet-implemented gaps remain in
`src/compiler/70.backend/svmg_lowering.spl` (Task D4, test-body lowering to
SVM-G). Both fail fast with a diagnostic naming the gap — neither is silently
mis-lowered. This doc was reported missing by an earlier audit; this is its
first landing.

Design reference: `doc/05_design/runtime/gpu_remote_interpreter_architecture.md`
§4.4 ("Supported Simple subset for `interpreter(remote(gpu))` test bodies
(v1)"). §4.4 lists as in-subset: integer/float arithmetic and comparisons,
`if/elif/else`, bounded `for`, `while` (step-budget backstop), non-recursive
`fn` calls, fixed-size arrays, `print` of string literals and integers,
`expect(x).to_equal(y)`. As of this update, everything in that list is
implemented **except** the two items below.

## 2026-08-08 update — if/while/print-of-string-literal/float landed

`if/elif/else`, bounded `while`, `print` of a **string-literal** argument, and
float arithmetic/comparison are now implemented (`_Lowerer.lower_if`,
`lower_while`, `lower_print`, `expr_is_float` + `binop_opcode(op, is_float)` in
`svmg_lowering.spl`). Verified by
`test/01_unit/compiler/backend/svmg_lowering_spec.spl`
(`Results: 17 total, 17 passed, 0 failed`, up from 9; sabotage-probed: cross-
wiring the float `Add` opcode to the integer `OP_ADD` produced
`16 passed, 1 failed`, reverted back to 17/17). Conformance regression
(`test/02_integration/svmg/conformance/conformance_suite_spec.spl`) unaffected
at `61 total, 61 passed, 0 failed`.

## Open gap 1 — `print` of a non-string-literal argument (e.g. an integer)

- **File:line:** `src/compiler/70.backend/svmg_lowering.spl`, `_Lowerer.lower_print`
  (the `case _:` arm after the `HirExprKind.StringLit` case).
- **What's missing:** design §4.4 lists "`print` of string literals **and
  integers**" as in-subset. Only the string-literal half is implemented.
  Printing an arbitrary (possibly non-constant) `i32` value via `SYS_PUTC`
  requires runtime decimal-digit extraction (repeated `DIV`/`REM` by 10,
  reversing the digit order, handling the sign and the zero case) synthesized
  as bytecode at lowering time — a small but real sub-routine, not a
  one-line change.
- **Current behaviour:** fails fast with `"`print` of a non-string-literal
  argument (e.g. an integer) is in the design §4.4 subset but is not yet
  implemented by this D4 lowering pass"`. Proven by the spec case "rejects
  print of a non-string-literal argument (e.g. an integer)".
- **Unblock condition:** implement a `lower_print_int` helper that emits a
  digit-extraction loop (mirroring `lower_for`'s bounded-loop codegen
  pattern) into a fixed scratch DATA slot, then walks it in reverse emitting
  one `SYS_PUTC` per digit; special-case value `0` and negative values (emit
  `'-'` first, negate via `0 - v`, mind `i32::MIN`'s asymmetric range).

## Open gap 2 — compound assignment (`+=`/`-=`/etc) on a float-typed local

- **File:line:** `src/compiler/70.backend/svmg_lowering.spl`,
  `_Lowerer.lower_stmt`'s `HirStmtKind.Assign` arm (the `expr_is_float(target)
  or expr_is_float(value)` guard added 2026-08-08).
- **What's missing:** `assign_opcode(op: HirAssignOp) -> i64?` only maps to
  the nine integer opcodes (`OP_ADD`/`OP_SUB`/.../`OP_SHR`); there is no float
  variant. Using it unconditionally on a float local would silently reinterpret
  the local's f32 bit pattern as an i32 and emit the *integer* opcode — a
  real, dangerous mis-lowering (not caught by any assembler/VM-level check,
  since the VM has no concept of a slot's "declared" type). The guard added
  2026-08-08 turns that into an honest fail-fast instead.
- **Current behaviour:** fails fast with `"compound assignment (+=/-=/etc) on
  a float local is in the design §4.4 subset but is not yet implemented by
  this D4 lowering pass (assign_opcode only maps to integer opcodes)"`.
  Proven by the spec case "rejects compound assignment on a float local
  instead of silently emitting the integer opcode".
- **Unblock condition:** add a float-opcode variant of `assign_opcode`
  (`HirAssignOp.Add -> OP_FADD`, etc. — `Mod`/bitwise ops have no float
  opcode and should stay rejected even then, matching the `Binary`-op
  precedent) and route `compound_assign`'s call site through it the same way
  `binop_opcode(op, is_float)` already routes `Binary`.

## Verification commands

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/compiler/backend/svmg_lowering_spec.spl --no-session-daemon
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/02_integration/svmg/conformance/conformance_suite_spec.spl --no-session-daemon
```

## Related

- `doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md` § "D4 update
  2026-08-08" — also records that `src/lib/common/svmg/ref_vm.spl` and its
  spec were found deleted from `main` (a sibling-commit clobber) at the start
  of this work and were recovered before any D4 edit.
- `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md` §5 Task D4.
