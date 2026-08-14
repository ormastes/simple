# Stage 3 `runtime_error` static-owner receiver corruption

Date: 2026-08-14
Status: FIXED (2026-08-14); downstream Stage 3 remains blocked
Owner: compiler MIR method-call lowering
Source: `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1000`

## Fresh reproducer and evidence

The third and final restart12 fix/verify cycle ran:

```sh
env SIMPLE_NO_STUB_FALLBACK=1 /usr/bin/time -v \
  sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --full-cli --no-mcp --backend=llvm --jobs=min
```

Stage 2 and its sanity gate passed. The previous fourteen
`cannot derive module constant type from folded value` errors did not recur,
which verifies the HIR-expression-based folded-constant repair. Stage 3 then
exited 139 after 39:38 with maximum RSS 25,605,268 KiB.

The retained log
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log` ends
while lowering `runtime_error`. `MethodResolution` is correctly classified as
`Unresolved`, but recovery of the type-valued receiver produces unsupported
expression discriminant `-1` and impossible local ID `103079215111`. This is
the last observable frontier, not a symbolized crash-site claim.

## Unblock condition

In a fresh lane, capture a symbolized native backtrace or reduce the
`runtime_error` static-owner call to a candidate-bound native fixture. Repair
the owner in `method_calls_literals.spl`, then pass that exact fixture, the
adjacent payload-enum/static-factory/inferred-constant regression, and one
strict Stage 3 plus Stage 4 bootstrap. Do not use the Rust seed as test or
deployment authority. This lane exhausted all three global cycles and must not
rerun the bootstrap command unchanged.

## Fresh repair evidence

The fresh repair lane scalarized the type receiver name/id before the native
aggregate call boundary and added an unambiguous owner-qualified symbol-table
fallback. The fallback accepts a method leaf only when every matching exact
symbol names the same static `Function`; ambiguous leaves remain unresolved.

Cycle 1 retained the old impossible `runtime_error` receiver and did not close
this bug. Cycle 2 produced zero `method=runtime_error`, zero
`unresolved-receiver method=runtime_error`, and zero `unsupported expr kind`
rows. Lowering continued past the former frontier before a new exit-139 after
`file_copy`.

Authoritative final Cycle 3 log:
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`, SHA-256
`51877e1e469e9504934b68097db3a8250bbf85f666247aa652e3e1c676606a5b`.
It retains the same zero-row proof with the ambiguity guard present.

Regression coverage is in the unit, integration, and modern SSpec system lanes
named `static_factory_receiver_identity` and
`native_crossmodule_static_error_factory`. The admitted Stage 2 compiler also
compiled and executed the fixture with `STATUS: PASS ... factories=2`. This
bug is closed; the downstream crash is tracked separately.
