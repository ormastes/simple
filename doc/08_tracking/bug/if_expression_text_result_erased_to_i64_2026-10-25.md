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
`var rt_dir: text = find_runtime_source_dir()` plus a statement-form override
for the strict + configured-source-root case. Same values as before for all
three branches. Stage-2 compiled object: defined-symbol set identical to the
run-27e object; Stage 3 hello world then links and runs ("hello stage3").

## Compiler fix (open)
MIR/HIR must keep the declared text type of a nested if-expression whose arm
contains `?`.
