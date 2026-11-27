# MIR replaces CLI-named function results and intercepts declared eprint

Status: source repairs and regression specifications authored; runtime verification pending.

## CLI array indexing

Under `SIMPLE_BOOTSTRAP=1`, `try_lower_bootstrap_cli_arg_index` recognized a
zero-argument call named `get_args` or `get_cli_args` and replaced its index
result with `spl_get_arg(index)`. Both Var and NamedVar forms were affected.
The ordinary index path had already lowered the base call, so this MIR defect
substituted the value; it did not itself remove that call's effects.

There is no universal wrapper identity that permits this substitution.
Source CLI wrappers use different argument offsets and filtering, and a local
function can return an unrelated array. The repair removes the shortcut and
its call site, allowing the normal evaluated-array indexing path to run.

## Declared eprint

`lower_call` unconditionally routed direct calls named `eprint` to
`lower_bootstrap_print_call`, bypassing a source definition and its result or
effects. The repair preserves known top-level/provider callables through the
existing `is_known_top_level_function` ownership check. The unresolved builtin
keeps its existing `rt_eprintln` dispatch; no new runtime symbol is introduced.

This MIR interception is separate from the LLVM backend's runtime-name alias
ownership defect; their fixes and verification evidence must remain distinct.

## Authored prevention and qualification

- `test/01_unit/compiler/50.mir/bootstrap_cli_named_array_index_spec.spl`
  exercises actual index/call lowering with Var and NamedVar under bootstrap
  modes 0 and 1. It checks the original call remains once, ordinary array
  reads exist, and `spl_get_arg` is absent. Source and builtin eprint controls
  check that ownership selects the intended call route.
- `test/fixtures/compiler/mir_cli_local_ownership.spl` checks local argument
  array values, a filtered-array offset, declared eprint's integer result,
  and exact side-effect counts. Run the native fixture under both bootstrap
  settings and both supported native backends once a runtime is admitted.

No Simple test, bootstrap build, native compilation, or native execution was
performed for these repairs; no Rust seed fallback was used. Bootstrap
performance and runtime correctness remain unqualified. Source review and
authored assertions do not establish an executed PASS. Required compiler/core
and MCP/LSP smoke checks also remain pending.
