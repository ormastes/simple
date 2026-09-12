# A function-local `use` loses the imported closure's enum definitions

- Status: OPEN (2026-09-12)
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
`SIMPLE_EXECUTION_MODE=interpret bin/simple lint .perf2/hello.spl` — exits 0
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
