# A function-local `use` loses the imported closure's enum definitions

- Status: FIXED (2026-09-13) for the enum half. The `[jit-fallback]` half is
  still OPEN and shares its root with
  `use_lazy_is_a_no_op_in_the_rust_seed_2026-09-12.md` — see "Still open" below
- Binary: deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`

## Symptom

Moving a top-level `use` inside the function that needs it — the lazy-import
pattern used by `src/app/mcp/bootstrap/main_lazy_v2.spl` and 157 other sites —
loads the module and makes its FUNCTIONS callable, but the enums reachable
through that module's closure are not registered. The call then dies at run
time:

```
error: semantic: enum `LintLevel` not found in this scope
```

Reproduced in `src/app/cli/lint_entry.spl`: with
`use app.io.cli_lint_commands.{run_lint_command, run_fmt_command, run_fix_command}`
at top level, `bin/simple lint <file>` exits 0 with `Lint passed: all files
clean`. With exactly the same import moved into the dispatch function, the help
path gets 10x faster (9,534 ms -> 965 ms) and `bin/simple lint <file>` exits 1
with the message above. `LintLevel` is defined in
`src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:8`.

## Not a JIT-fallback artifact

A function-local `use` also drops the importing module out of the JIT:

```
[jit-fallback] unresolved external symbol 'run_fmt_command': whole module dropped
to the interpreter (expect ~100-1000x slowdown).
```

That is a second defect, not the cause of the first. Discriminator: the
UNMODIFIED entry (top-level `use`) run on the interpreter lane —
`SIMPLE_EXECUTION_MODE=interpret bin/simple lint hello.spl` — exits 0
with `Lint passed: all files clean`. So the interpreter lane runs lint fine; the
scope loss comes from the function-local import itself.

## Why it matters

Two independent defects make the sanctioned lazy-import pattern unusable for
the CLI entry points it exists for (see
`subcommand_help_loads_implementation_closure_2026-09-12.md`):

1. enum definitions from the imported closure are not registered, and the
   failure is a run-time semantic error, not a compile-time one;
2. the `[jit-fallback]` marker is printed unconditionally
   (`src/compiler_rust/driver/src/exec_core.rs:1390` — "always print a loud,
   greppable marker"), so adopting the pattern adds a stderr line to every
   invocation of the command.

## Repro

```sh
# fails: enum LintLevel not found in this scope
python3 - <<'PY'
p='src/app/cli/lint_entry.spl'; s=open(p).read()
s=s.replace('use app.io.cli_lint_commands.{run_lint_command, run_fmt_command, run_fix_command}\n','')
s=s.replace('    if command == "lint":\n        return run_lint_command(filtered_args)',
            '    use app.io.cli_lint_commands.{run_lint_command, run_fmt_command, run_fix_command}\n'
            '    if command == "lint":\n        return run_lint_command(filtered_args)')
open(p,'w').write(s)
PY
bin/simple lint hello.spl; echo "rc=$?"
```

## Root cause and fix (2026-09-13)

**Cause, confirmed in the source.** Both block-scoped `use` arms borrow `enums`
immutably and hand `load_and_merge_module` a local CLONE to register into:

- `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs:1134`
- `src/compiler_rust/compiler/src/interpreter/node_exec.rs:618`

Each carried a comment asserting that imported enum definitions "reach the
interpreter through GLOBAL_ENUMS rather than this map, so a local copy satisfies
the loader without dropping them". Nothing on that path ever wrote GLOBAL_ENUMS
— the only writers were the local `enum` declaration arms
(`block_execution.rs:953` and `:1744`) — so `merged_enums` was dropped on the
floor and the closure's enums were lost while its FUNCTIONS were bound
correctly. That is exactly the observed shape: the call resolves, the enum does
not.

**Fix.** Both arms now publish the names the import added to `GLOBAL_ENUMS`, the
cross-module registry that `interpreter/expr/calls.rs:783,870`,
`interpreter_call/mod.rs:978,1189,1507` and `interpreter_method/mod.rs:705`
already fall back to. Only names the local map does not already carry are
published, so a local definition is never clobbered by an import.

**Verified, then reverted.** PERF-4 wrote that patch, built a seed with it
(sha256 `7a19d5b3d4e6bc6a...`) and measured the spec below flipping
`ERROR ... passed=1 failed=1` -> `OK ... passed=2 failed=0`. It was then
REVERTED, because both files are on the active fence list
(`scratchpad/egl_offlimits_v2.txt`): `interpreter_call/block_execution.rs` and
`interpreter/node_exec.rs` are in another lane's diff. The 102-line patch is
kept at `scratchpad/perf/patches/enum_scope_fix_FENCED.patch` for whoever owns
those files; it is ~10 lines of real change per arm plus a `GLOBAL_ENUMS` import
in `node_exec.rs`.

**The spec is therefore EXPECTED RED on any binary without that patch**, and is
deliberately not weakened — the repo precedent is
`test/05_perf/startup/check_lint_entry_closure_spec.spl`, which carries an
"EXPECTED RED, deliberately not weakened" example for the same reason.

**Pin.** `test/01_unit/compiler/loader/function_local_use_enum_scope_spec.spl`
with a two-file fixture that needs no heavy closure
(`function_local_use_enum_scope/{enum_owner,entry_local_use,entry_top_level_use}.spl`).
The module-scope-use control fixture is in the same spec: it was never broken,
so any divergence between the two is the defect.

RED on the deployed seed (sha256 `3d120a6f9ab5704b...`), GREEN on a seed built
from this tree:

```
✗ keeps the imported closure's enum in scope for a function-local use
  expected 1 to equal 0
✓ gives a top-level use of the same module the same result
SPEC FILE VERDICT: ... outcome=ERROR declared>=2 executed=2 passed=1 failed=1
```

GREEN on a seed built from this tree (sha256 `7a19d5b3d4e6bc6a...`, aarch64):

```
✓ keeps the imported closure's enum in scope for a function-local use
✓ gives a top-level use of the same module the same result
SPEC FILE VERDICT: ... outcome=OK declared>=2 executed=2 passed=2 failed=0
```

and the fixture itself:

```
$ bin/simple run test/.../entry_local_use.spl
error: semantic: enum `FixtureLevel` not found in this scope       # rc 1
$ bin/simple run test/.../entry_top_level_use.spl
level=warning                                                      # rc 0
```

## Still open: the `[jit-fallback]` half

The second defect in this record — every invocation additionally printing
`[jit-fallback] unresolved external symbol '...': whole module dropped to the
interpreter` — is NOT fixed and is not separately fixable here. Its root is the
one in `use_lazy_is_a_no_op_in_the_rust_seed_2026-09-12.md`: the seed's JIT lane
flattens the whole import closure (`pipeline::module_loader::load_module_with_imports`,
called from `exec_core.rs::run_file_jit`) before HIR/MIR/codegen, so ANY import
the flatten does not see — a function-local `use`, or a genuinely deferred
`use lazy` — is an unresolved external symbol at codegen time and costs the
whole module its JIT. Until that is addressed, the function-local pattern stays
unusable for the CLI entry points, and
`subcommand_help_loads_implementation_closure_2026-09-12.md` was fixed by
dispatching a different entry instead (mechanism 4).
