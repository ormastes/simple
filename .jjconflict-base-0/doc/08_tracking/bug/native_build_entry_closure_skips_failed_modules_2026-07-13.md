# Bug: native-build entry closure skips failed semantic dependencies

## Symptom

`native-build --entry-closure` reports imported modules as `FAILED FILES`, labels
them non-critical, skips them, and proceeds to link. A dependency of the entry
is not optional merely because another module failed to provide its types.

## Reproduction

At revision `f27a7d9f322b`, the UI CLI focused checker imported
`t32_cli.bridge_access`, whose legacy T32 MCP dependencies lacked the
`McpT32Session` state owner removed with the old MCP entrypoint. The pinned
pre-fix build reports four HIR failures, including:

```text
bridge_access.spl: cannot infer field type: struct 'ANY' field 'connected'
session_tools.spl: cannot infer field type: struct 'ANY' field 'connected'
Warning: 4 non-critical file(s) failed to compile (skipped)
```

It then invokes the linker instead of failing the build at semantic closure.
The bounded transcript is
`build/mini_builds/ui_cli_checker/native-build.log` in the reproducing workspace.

## Expected

Any source module required by the resolved entry closure that fails parse,
resolution, type checking, HIR, or code generation must terminate native-build
before link with a nonzero exit. Only modules proven outside the entry closure
may be omitted.

## Actual risk

Continuing can produce unresolved stubs, misleading runtime/link failures, or a
binary missing behavior that the entry imports. `SIMPLE_NO_STUB_FALLBACK=1` did
not turn these skipped dependency failures into an immediate hard error.

## Owner and fix direction

Owner: native-build entry-closure dependency accounting and failure aggregation.
Propagate requiredness from the entry graph to every compilation unit and reject
the build when any required unit fails. Add one regression with a required
module containing a deterministic HIR error; assert no linker invocation and no
output binary.
