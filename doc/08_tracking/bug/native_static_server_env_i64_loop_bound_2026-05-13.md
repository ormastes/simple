# Native Static Server Env-I64 Loop Bound Crash

Status: **Closed** — mitigation landed 2026-05-13, root cause filed as a parsing-ergonomics follow-up.

Date: 2026-05-13

## Status

**Closed** — mitigation landed 2026-05-13, root cause filed as a parsing-ergonomics follow-up.

`static_file_server.spl` reads the request limit through the native runtime
bridge `rt_env_get_i64`, avoiding the fragile `rt_env_get` text value plus
Simple-side integer parsing path that triggered the full-server native crash.

Investigation (2026-05-19) confirmed there is no codegen defect: the Cranelift
`Branch` terminator in `codegen/instr/body.rs` already correctly coerces i64
loop conditions to i8 via `icmp_imm(NotEqual, cond_val, 0)` before `brif`.
The `tagged_vregs` unboxing path is never applied to `rt_env_get_i64` return
values (correct — it returns a raw i64, not a tagged RuntimeValue). The
`native_parse_int_loop_bound_smoke.spl` test that exercises exactly the
`while i < limit` pattern with an i64 bound from `rt_env_get_i64` passes.

## Symptom

`test/05_perf/webserver/static_file_server.spl` crashed in a rust-hosted native
build before printing readiness when its accept-loop bound came from a
Simple-side text environment parse:

```simple
val request_limit = parse_env_i64_via_text("SIMPLE_STATIC_SERVER_REQUESTS", 512)
while served < request_limit:
    ...
```

The panic is:

```text
runtime/src/value/heap.rs:156:17: null pointer dereference occurred
```

## Reproduction

Build:

```bash
src/compiler_rust/target/debug/simple native-build --runtime-bundle rust-hosted \
  --source src/lib --source test --entry-closure \
  --entry test/05_perf/webserver/static_file_server.spl \
  --threads 1 --timeout 20 --output /tmp/simple_static_server_native_hosted_current
```

Run an old env-text-parse bound variant:

```bash
SIMPLE_STATIC_SERVER_ADDR=127.0.0.1:18082 \
SIMPLE_STATIC_SERVER_FILE=README.md \
SIMPLE_STATIC_SERVER_REQUESTS=1 \
RUST_BACKTRACE=1 timeout 4s /tmp/simple_static_server_native_hosted_current
```

## Narrowing Evidence

The following rust-hosted native smokes pass:

- `test/05_perf/webserver/native_parse_int_loop_bound_smoke.spl`
- `test/05_perf/webserver/native_hosted_ffi_smoke.spl`
- `test/05_perf/webserver/native_static_prelude_smoke.spl`
- `test/05_perf/webserver/native_static_bind_prelude_smoke.spl`
- `test/05_perf/webserver/native_tcp_bind_variable_smoke.spl`

That means the bug was not simply `rt_env_get`, `rt_file_exists`,
`rt_file_read_text`, variable TCP bind, or a simple parse-int loop bound in
isolation. It appeared only when the full static-server accept loop used the
text-parsed env-derived bound.

## Current Mitigation

`static_file_server.spl` now keeps the runtime-configurable bound but gets the
integer directly from the runtime:

```simple
extern fn rt_env_get_i64(key: text, default_value: i64) -> i64

val request_limit = rt_env_get_i64("SIMPLE_STATIC_SERVER_REQUESTS", 512)
```

This keeps the live native webserver benchmark configurable without exercising
the crashy Simple-side parse path. A separate follow-up should still improve
native Simple text/byte parsing ergonomics for environment values.
