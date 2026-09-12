# `simple <subcommand> --help` loads the subcommand's whole implementation closure

- Status: OPEN (2026-09-12)
- Binary: deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`
- Host: aarch64, 20 cores, load ~29 (shared box; wall times are an envelope,
  the `.spl`-open counts are deterministic and reproduce exactly)

## Symptom

| entry | wall | what it does |
|---|---:|---|
| `simple --help` | 17 ms | static Rust path in the driver |
| `simple run --help` | 13 ms | static Rust path |
| `simple build --help` | 17 ms | static Rust path |
| `simple nosuchcommand` | 20 ms | driver rejects unknown commands |
| `simple check --help` | 546 ms | interprets `src/app/cli/check_entry.spl` + closure |
| `simple lint --help` | 9,534 ms | interprets `src/app/cli/lint_entry.spl` + closure |
| `simple test --help` | **37,628 ms** | interprets the test-runner closure, then prints `Error: unknown option: --help` |

`simple test --help` is the worst case twice over: it spends 37.6 s and then
never prints help at all.

## Cause

`src/compiler_rust/driver/src/main.rs` routes the pure-Simple tool commands
(`command_is_pure_simple_tool`, :287) to an `app_path` — `lint`/`fmt`/`fix` to
`src/app/cli/lint_entry.spl` (:552), `check` to `src/app/cli/check_entry.spl`.
The entry file's top-level `use` statements are resolved before its `main()`
runs, so the help branch inside `main()` is reached only after the whole
implementation closure has been loaded.

`SIMPLE_PERF_COUNTERS=1 simple lint --help` reports `VT_CALLS 1`. The process
executes essentially no interpreted work; all of the 9.5 s is module loading
for a branch that never runs.

Deterministic attribution (`strace -f -e trace=openat`, `.spl` opens, probe file
importing exactly one name):

| import | `.spl` opens |
|---|---:|
| `app.io.cli_lint_commands.{run_lint_command}` | 1,237 |
| `std.cli.cli_util.{get_cli_args}` (before the 2026-09-12 leaf fix) | 183 |
| `app.io.env_ops.{env_get}` | 32 |
| `app.io.process_ops.{process_run_timeout}` | 31 |
| `std.nogc_sync_mut.io.file_ops.{file_exists}` | 28 |
| `app.check.targets.{expand_check_targets}` | 15 |
| `app.cli.check_options.{check_option_error}` | 9 |
| `std.cli.log_modes.{parse_log_options}` | 7 |
| `app.check.worker_failure.{...}` | 7 |

`src/app/cli/lint_entry.spl`'s own header already states the intent — "Keep this
wrapper thin: command-specific work lives in app.io.cli_lint_commands so
help/error paths do not import the old compiler CLI surface" — and an eager
top-level import defeats it.

`check_entry.spl` has a second, smaller ordering defect: `check_option_error(args)`
runs before the `--help` branch (`main()`, :206 vs :211).

## Three fix mechanisms were tried; all are blocked

1. **`use lazy`** (the sanctioned keyword, already used three times inside
   `src/app/io/cli_lint_commands.spl`). No effect: `simple lint --help` opened
   **1,532 `.spl` files with `use lazy` and 1,532 with an eager `use`** —
   byte-identical. Deliberate, documented seed limitation at
   `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs:575`.
   See `use_lazy_is_a_no_op_in_the_rust_seed_2026-09-12.md`.
2. **Function-local `use`** (precedent: `src/app/mcp/bootstrap/main_lazy_v2.spl`,
   158 occurrences repo-wide). Cuts `lint --help` to 965 ms but BREAKS the real
   command: `simple lint <file>` dies with `error: semantic: enum LintLevel not
   found in this scope` (rc 1, was rc 0), and every invocation additionally
   prints a `[jit-fallback] unresolved external symbol ...` line. See
   `function_local_use_loses_enum_scope_2026-09-12.md`.
3. **Delegation through `cli_run_file`** to a sibling implementation entry.
   Cuts `lint --help` to **258 ms** (37x) and is the most promising shape, but
   the real path then fails with `error: rt_cli_run_file is not available in
   standalone mode`: the runtime stub
   (`src/compiler_rust/runtime/src/value/cli_sffi.rs:169`) is what a dispatched
   app links, not the driver's real implementation.

## Suggested fix

Unblock mechanism 3 (make the driver's `cli_run_file` reachable from a
dispatched app) or mechanism 1 (implement deferred loading for `use lazy` in the
seed). Either makes the thin-wrapper design in `lint_entry.spl`'s header work as
written. Mechanism 2 should not be used until the enum-scope and JIT-visibility
defects are fixed.

Partial mitigation already landed (commits `85fd1d2f0d5`, `968edf98ef1`):
`std.cli.cli_util` now uses leaf owners instead of the `std.io`/`std.env`
facades, which cut `simple check --help` from 203 to 81 `.spl` opens and
`simple lint --help` from 1,532 to 1,259. Pinned by
`test/05_perf/startup/cli_args_closure_budget_spec.spl`.

## Repro

```sh
time bin/simple lint --help          # ~9.5 s for four lines of usage text
bin/simple test --help | tail -1     # ~37.6 s, then: Error: unknown option: --help
SIMPLE_PERF_COUNTERS=1 SIMPLE_PERF_COUNTERS_OUT=/tmp/pc bin/simple lint --help
grep VT_CALLS /tmp/pc                # VT_CALLS 1
```
