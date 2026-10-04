# Bootstrap interpreter product selected the legacy AST port

Both early Phase4 interpreter builds failed on imports in app/interpreter.
That failure did not establish a defect in the currently shipped interpreter:
the bootstrap schedule selected an obsolete product entry.

## Current ownership evidence

- `src/compiler/10.frontend/core/interpreter/mod.spl:20-23` identifies
  app/interpreter as the legacy interpreter replaced on 2026-02-10. The old
  files still exist, so directory existence is not a product ownership proof.
- `src/app/cli/_CliMain/main_and_help.spl` imports cli_run_file from the app IO
  command facade; `_CliCommands/run_commands.spl:137` calls interpret_file.
- `src/compiler/80.driver/driver_api_interpret.spl:28-41` sets CompileMode.Interpret
  and calls the compiler driver. `driver.spl:105-135` executes its HIR through
  InterpreterBackendImpl.interpret_hir_module.
- `src/app/test_runner_new/inprocess_probe.spl:3,26` separately uses the current
  compiler.core.interpreter.mod/core_interpret for its in-process test path.
- Managed and provisional bootstrap schedules nevertheless compiled
  `src/app/interpreter/main.spl` into simple_interpreter.

## Repair

`src/app/cli/interpreter_main.spl` is a native product entry that calls the same
CLI dispatcher as the full CLI. The dispatcher receives an explicit forced
interpreter mode, applies force_interpret/no_jit before existing JIT configuration,
and suppresses bootstrap-driver delegation for this admitted native product.
Argument forwarding, normal error reporting, execution-mode receipts, help and
version remain owned by the production CLI. This adds no interpreter evaluator.

Compilation commands (`--compile`, compile, build, native-build) at the command
position return the existing CLI usage-error status. Script arguments are not
scanned as commands. The full CLI continues to call the shared dispatcher with
forced mode disabled. All three bootstrap entry declarations now select this
product. Required interpreter manifests/receipts and six backend/subsystem suite
lanes remain required; no test inventory or suite is replaced by a hello probe.

The unrelated legacy-import/control repair candidates remain isolated,
unqualified diagnostic artifacts. They are not included in this change or
presented as necessary fixes for the canonical interpreter.

## Validation

Both existing scheduler regressions now reject a legacy interpreter entry while
retaining their failure-continuation, complete-product and six-suite assertions.
The native product smoke executes an actual supplied binary: exact output and
forced-mode receipt, inherited-bootstrap override rejection, JIT/backend option
precedence, compilation conflicts, parser errors, help and version.

Native product build/smoke and full native subsystem suites are pending root
resource admission, with --threads 80 and frontend memory admission retained.
A static scheduler PASS is not interpreter/compiler/loader suite qualification,
not six aggregate executables, and not a discovered or registered case count.
