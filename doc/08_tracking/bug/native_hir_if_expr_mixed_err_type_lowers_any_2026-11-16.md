# Native HIR: if-expression with mismatched `Err` payload types lowers to ANY

- Date: 2026-11-16
- Status: verification-pending (source workaround landed; compiler gap open)
- Area: compiler / 20.hir type inference (native-build lane)

## Symptom

Native rebuild of the full CLI (`native-build src/app/cli/main.spl`) aborted:

```
src/os/apps/smux/server.spl: hir: Unsupported feature: cannot infer field type while lowering _serve_on: struct 'ANY' field 'fd'
```

## Root cause

`_serve_on` had

```simple
val accepted = if quiescing:
    Err("host-service-auth-quiescing")        # Result<?, text>
else: listener.accept_timeout(10)             # Result<TcpStream, IoError>
var stream = accepted.unwrap()
... stream.fd ...
```

The two branches disagree on the error type (`text` vs `IoError`) and the
then-branch has no `Ok` type at all. HIR inference does not unify or reject
this: it silently degrades `accepted` to ANY, and the failure surfaces only
later as an unrelated-looking field-access error on `stream.fd`. The
interpreter accepts the code because it is dynamically typed.

## Workaround (landed)

`src/os/apps/smux/server.spl`: `accepted` is annotated
`Result<TcpStream, IoError>` and the quiescing branch builds a real
`IoError(kind: IoErrorKind.WouldBlock, ...)`; `stream` annotated `TcpStream`.

## Verification

The full K1 CLI rebuild with the workaround compiled `server.spl` and linked
`build/nb/cli_tip.exe` (`Build complete: 4 compiled, 3764 cached, 0 failed`).

## Reduction attempt (no repro yet)

The diagnostic is emitted by the Rust seed
(`src/compiler_rust/compiler/src/hir/lower/expr/access.rs:519`). A
reduced unit test in `hir/lower/tests/control_flow_tests.rs` (if-expr
`Err(text)` vs `Result<Stream, IoErr>`, `.unwrap().fd` with two structs
sharing `fd`) PASSED on the current seed, so the reduction does not
reproduce; it was not landed. The real trigger likely also needs
module-level context present in `server.spl` (cross-module `TcpListener`
import, module-level `var` globals in the same function).

## Compiler gap (open)

The if-expression branch-type mismatch should be a diagnosed type error at
the `if` (or the `Ok` type should be taken from the other branch when the
error types agree), never a silent ANY. Needs a native-build repro spec in
the HIR inference tests before fixing.
