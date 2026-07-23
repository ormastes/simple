# Bug: native-build entry closure skips failed semantic dependencies

## Status

Reported dotted-import resolution, parse, and HIR-skip path source-fixed; fresh
self-hosted execution pending. Unresolved single-segment imports remain open:
the closure walker still skips them as possible prose/pseudo-imports. The
optional whole-program type-check pass also remains warn-only under
`SIMPLE_TYPECHECK_WARN=1` and belongs to the separate type-check burndown.

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

## Current owner and resolution

Owner: the pure-Simple driver phase gates in `src/compiler/80.driver/driver.spl`.
Closure resolution adds unresolved dotted or empty-import errors to
`ctx.errors`, and phase 1 returns `ParseError` before parsing. Entry-closure
parsing returns false on parser diagnostics, and phase 2 returns `ParseError`.
HIR lowering collects every non-recovered `LoweringError` into `ctx.errors`;
phase 3 returns `TypeError` before monomorphization and link.

`entry_closure_physical_source_dedup_spec.spl` scopes its regression assertions
to the four owning function bodies and pins each fail-fast edge plus the phase-3
return before phase 4. The deployed self-hosted runner still has the separately
tracked stale `rt_env_set` crash, so fresh executable evidence remains pending;
no Rust-seed result is substituted.

The next source fix must distinguish valid single-segment module imports from
scanner false positives and fail unresolved required modules closed. Do not
remove the skip while another agent owns the active driver/bootstrap rebuild.
