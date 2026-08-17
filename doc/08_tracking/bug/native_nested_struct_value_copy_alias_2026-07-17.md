# Native nested struct copies retain aliases

- Date: 2026-07-17
- Status: source fixed; execution pending
- Severity: P1 silent wrong result

## Symptom

Copying an outer value-type struct rebuilt only its first level. Any nested
value-type struct field kept the original pointer, so mutating
`copy.inner.field` also changed `original.inner.field`. The same shallow loop
was duplicated for plain struct parameters. Embedded `class` fields correctly
remained shared and must continue to do so.

## Root cause and fix

`maybe_copy_struct_value` and the plain-parameter binder emitted one
`GetField`/`Aggregate` layer. The MIR metadata already records each field's
declared nested type and which named aggregates are classes.

Both boundaries now use one recursive value-struct copier. It follows
`struct_field_type_name`, skips `class_type_names`, preserves nil nested
fields with a guarded merge, and rebuilds each non-nil nested value struct.
Normal scalar fields and class references remain unchanged. Cyclic value-type
back-edges remain shared; the type checker should reject such layouts before
that ceiling is removed.

## Regression

The strict dual-backend `nested_struct_value_copy` parity case covers local
binding and plain-parameter copies in one program. It requires nested structs
to remain isolated while the same outer struct's embedded class remains
shared. Linux runs the full parity board; macOS and Windows select the case in
their hosted matrix, and FreeBSD selects it under both LLVM and Cranelift.

Execution remains pending under the current no-runtime/no-compiler-command
restriction.

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

ALREADY-FIXED (source). Content: `maybe_copy_struct_value` (src/compiler/50.mir/mir_lowering_stmts.spl:393-427) no longer emits one GetField/Aggregate layer — it resolves the struct SymbolId and delegates to `copy_struct_value_recursive(init_local, struct_type_name, type_symbol, [struct_type_name])`, and still returns nil (no copy) for `class_type_names`, preserving class-field sharing as required. Not executed natively by this lane (native-build lanes are claimed); the doc's own 'execution pending' caveat stands.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: ALREADY-FIXED IN 50.mir BY CONTENT; ALSO MIS-ATTRIBUTED.**

The real site is `src/compiler/50.mir/mir_lowering_stmts.spl:393-427`
(`maybe_copy_struct_value` -> `copy_struct_value_recursive`), NOT the attributed
`_MirLowering/function_lowering.spl`. The recursive copier replaces the
single-layer GetField/Aggregate copy this doc describes. Residual: class-typed
fields are still skipped by the copier, which is intended sharing but is worth
recording here. Recommend re-attributing this row to `mir_lowering_stmts.spl`.
