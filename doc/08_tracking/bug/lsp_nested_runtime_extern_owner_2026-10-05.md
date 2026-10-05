# LSP entry function-local externs have no resolved HIR owner

Status: source repair; native qualification pending.

Actual failure: `executable-batch20-buildrunner-fix1/cranelift-025-lsp/artifact/compile.log`
reports two `[hir-fatal]` errors in `src/app/lsp/main.spl`: unresolved
`rt_cli_get_args` and `rt_env_get`. The source declared both extern functions
inside `main`; no module-level imported owner was registered for those calls.
This is a fatal diagnostic, distinct from the provisional re-export warnings
used to group several other batch failures.

The repair uses the existing narrow `app.io.minimal_runtime_ops` facade. It
preserves argument handling and uses that owner's defined missing-environment
behavior (empty text). No additional runtime FFI declaration or process owner
is introduced in the leaf. No change to full LSP server implementation is
claimed; the existing entry's documented guidance remains unchanged.

Regression specs invoke the real compiled binary with help and both version
forms, checking actual exits/stdout/stderr. They require
`SIMPLE_LSP_TEST_BINARY`; no mock or successful missing-binary fallback exists.
Native tests are UNRUN pending a new admitted source and available test lane.
Qualify both backends and re-run the original entry closure before closing.
