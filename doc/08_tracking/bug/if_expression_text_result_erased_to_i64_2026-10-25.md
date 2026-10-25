# Nested if-expression text result erased to i64 (runtime_compiler rt_dir) (2026-10-25)

## Symptom
Phase 3 Stage 3 hello world (bypass route) after codegen: `Hosted native linking
failed: Runtime compilation failed: Required runtime source not found:
202444832811553/runtime_native.c`. 202444832811553 = 0xb81f5c58aa21, a tagged
text handle rendered as a decimal.

## Root cause
`compile_runtime_objects` (src/compiler/70.backend/backend/runtime_compiler.spl)
computed `val rt_dir = if strict: (if env: strict_dir()? else: find()) else: find()`.
In the Stage-2-compiled run-27e object the expression's static type was i64, so
`"{rt_dir}/{name}.c"` interpolated the handle as an integer and file_exists
failed. Same class as the struct if-expression in module_build.spl:571
(doc generic_extern_enum_arg_boxed_as_int_2026-10-25).

## Workaround (this change)
`var rt_dir: text` assigned in statement form: the strict + configured-source-root
case calls `native_runtime_strict_source_dir_v1()?` directly (exactly once, so its
real Err text still propagates), every other case uses `find_runtime_source_dir()`.
Same values and errors as the original if-expression in all four cases. (The first
port called find_runtime_source_dir() unconditionally first; review found that its
Err->"" consumed the sticky authority failure, so the second `?` call reported
only "managed runtime authority previously invalidated". Fixed before landing.)
Evidence measured on the FIRST port (the review-fixed statement form is not
yet Stage-2-compiled): Stage-2 compiled object: defined-symbol set identical to the
run-27e object; Stage 3 hello world then links and runs ("hello stage3").

## Compiler fix (open)
MIR/HIR must keep the declared text type of a nested if-expression whose arm
contains `?`.

## Bug DB
DB reconciliation pending: no `bug_db.sdn` row was added for this ID in this change.
