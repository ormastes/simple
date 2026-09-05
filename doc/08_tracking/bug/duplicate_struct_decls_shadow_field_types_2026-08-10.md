# Duplicate same-named struct/class decls shadow field types; test-runner main dropped to interpreter

**Status:** LIKELY RESOLVED — re-probed 2026-08-17 on WEAK evidence; read the
caveat before closing it.

## Re-probe 2026-08-17 (partial-fix sweep, lane 1)

This file's own oracle for the last (`Span.end`) collision is a `jit-fallback`
line on `bin/simple test` startup. Across six independent `bin/simple test`
invocations in this session, `grep -c jit-fallback` was **0** in every log, so
the collision is no longer dropping the test-runner main to the interpreter.

EXPLICITLY WEAKER THAN THE FILING: the doc's evidence was a full-suite run;
this is a startup-path observation over six single-spec runs. It is the same
startup path that emitted the original line, but it is not the same experiment.
Treat this as "symptom absent", not "collision proven deduped" — whoever closes
this should confirm the duplicate declaration itself is gone from the tree.

NOT PROVED: that the duplicate `Span` declaration was actually removed; the
"blocked" reason recorded under "STILL OPEN — the last collision" was not
re-examined.

--- original filing below, kept for history ---

**Status (original):** PARTIALLY FIXED (three collisions deduped and verified; one remains, blocked)
**Date:** 2026-08-10
**Impact:** suite-wide. `bin/simple test` startup emits
`[jit-fallback] HIR lowering error: Cannot infer field type: struct '<X>' field '<f>' [in src/app/test_runner_new/main.spl]: whole module dropped to the interpreter (expect ~100-1000x slowdown)`
— the test runner's own entry module runs interpreted.

## Mechanism

The seed JIT co-compiles the whole entry closure and registers struct/class
types by BARE NAME. A field access on a value statically typed by name resolves
against whichever same-named declaration won registration
(`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:733`,
`CannotInferFieldType` when the winning declaration lacks the accessed field).
One declaration lacking the field poisons every other type of the same name in
the closure. Same family as
`duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09.md`
(functions) and `duplicate_hirtype_enum_decls_drop_module_to_interpreter_2026-08-04.md`
(enums).

## Repro / oracle (~110 s)

```bash
SIMPLE_TIMEOUT_SECONDS=0 timeout 200 bin/simple test > /tmp/tb.log 2>&1
grep -a 'jit-fallback' /tmp/tb.log
```

The fallback message names the currently-losing struct+field, so each dedupe
moves the message to the next collision — a built-in progress meter.

## Fixed 2026-08-10 (measured RED->next-collision each step)

1. `CompileOptions` field `mode` — three decls:
   - `src/compiler/00.common/driver_compile_options.spl` (has `mode`) — KEPT as
     the one true `CompileOptions`.
   - `src/compiler/70.backend/backend/backend_types.spl:251` -> renamed
     `BackendCompileOptions` (31 files in 70.backend, internal-only).
   - `src/compiler/10.frontend/core/backend_types.spl:312` -> renamed
     `FrontendCompileOptions` (file-local + its `__init__` export).
   After this the fallback moved from `CompileOptions.mode` to `Span.col` —
   direct confirmation the backend decl was the collider.
2. `Span` field `col` — `src/lib/common/sdn/value.spl` `class Span` (has
   `column`, not `col`) -> renamed `SdnSpan` across sdn + game2d/editor users
   and 4 specs. Also deduped `web_framework/tracing.spl` `Span` -> `TraceSpan`
   and `compute/containers.spl` `Span<T>` -> `ComputeSpan` (both lacked `col`).
   Fallback moved from `Span.col` to `Span.end`.

Regression spec (sabotage-verified 6->5 passed on reintroducing sdn `Span`):
`test/01_unit/compiler/duplicate_struct_decl_dedup_spec.spl`.
Affected lib specs all green: `sdn_schema_spec` 6/6, `containers_spec` 8/8,
`tracing_otlp_spec` 7/7.

## STILL OPEN — the last collision

`Cannot infer field type: struct 'Span' field 'end'`: the two remaining `Span`
decls are `src/compiler/00.common/diagnostics/span.spl:7` (has `end`) vs
`src/compiler/10.frontend/core/lexer_types.spl:12` (has `end_pos`, deliberately
renamed "to avoid C++ keyword"). A `.end` access on a diagnostics `Span`
resolves against the lexer decl and fails. Correct fix: rename the lexer
`Span` (e.g. `LexSpan`) across `10.frontend` — ~26 files reference `Span`
there, and per-site attribution matters (some references are the imported
diagnostics `Span`). NOT DONE 2026-08-10 because many of those files
(`core/lexer.spl`, `core/parser.spl`, `_FlatAstBridge/*`, `core/__init__.spl`,
...) carry another session's uncommitted edits in the shared WC. Once landed,
the oracle above must show `jit-fallback` count 0.

## Note on the 2026-08-04 HirType doc

The `case Str:` irrefutable-binding fallback that doc tracks no longer
reproduces (0 hits in the same time-boxed run); the field-type collision above
is what fires now. See the update appended there.
