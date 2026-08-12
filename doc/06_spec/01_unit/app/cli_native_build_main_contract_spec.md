# CLI Native Build Main Contract Spec

Source: `test/01_unit/app/cli_native_build_main_contract_spec.spl`

## Native build main dispatch contract

The spec verifies that `src/app/cli/native_build_main.spl` uses the in-process
`cli_native_build(args)` path by default while preserving the bounded worker
fallback for bootstrap, interpreter, explicit worker, and `--timeout` cases.

Checked contract snippets:

```text
use app.io._CliCompile.compile_targets.
cli_native_build
fn native_build_text_eq(a: text, b: text) -> bool:
fn native_build_should_use_worker(args: [text]) -> bool:
SIMPLE_NATIVE_BUILD_FORCE_WORKER
SIMPLE_BOOTSTRAP
native_build_has_timeout(args)
return run_native_build_worker(args)
cli_native_build(args)
worker_args.push("--mode=interpreter")
```

The startup flag filter is also pinned to indexed array traversal so deployed
native binaries do not lower this path through the unresolved array iterator.

Latest full-file evidence (2026-08-12):

```text
FAIL test/01_unit/app/cli_native_build_main_contract_spec.spl
15 assertions: 11 passed, 4 unrelated existing failures
```

This is source-contract evidence only; no rebuilt self-hosted executable was
produced, so it does not verify the native startup repair.
