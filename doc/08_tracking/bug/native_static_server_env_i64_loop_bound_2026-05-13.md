# Native Static Server Env-I64 Loop Bound Crash

Date: 2026-05-13

## Status

Open. The perf target uses a fixed request limit until this native-codegen
interaction is fixed.

## Symptom

`test/perf/webserver/static_file_server.spl` crashes in a rust-hosted native
build before printing readiness when its accept-loop bound comes from:

```simple
val request_limit = env_i64("SIMPLE_STATIC_SERVER_REQUESTS", 512)
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
  --entry test/perf/webserver/static_file_server.spl \
  --threads 1 --timeout 20 --output /tmp/simple_static_server_native_hosted_current
```

Run with the env-derived bound variant:

```bash
SIMPLE_STATIC_SERVER_ADDR=127.0.0.1:18082 \
SIMPLE_STATIC_SERVER_FILE=README.md \
SIMPLE_STATIC_SERVER_REQUESTS=1 \
RUST_BACKTRACE=1 timeout 4s /tmp/simple_static_server_native_hosted_current
```

## Narrowing Evidence

The following rust-hosted native smokes pass:

- `test/perf/webserver/native_parse_int_loop_bound_smoke.spl`
- `test/perf/webserver/native_hosted_ffi_smoke.spl`
- `test/perf/webserver/native_static_prelude_smoke.spl`
- `test/perf/webserver/native_static_bind_prelude_smoke.spl`
- `test/perf/webserver/native_tcp_bind_variable_smoke.spl`

That means the bug is not simply `rt_env_get`, `rt_file_exists`,
`rt_file_read_text`, `parse_int() ?? default`, variable TCP bind, or a simple
parse-int loop bound in isolation. It appears only when the full static-server
accept loop uses the env-derived bound.

## Current Workaround

`static_file_server.spl` keeps:

```simple
val request_limit: i64 = 512
```

This keeps the live native webserver benchmark running while preserving the bug
as a focused follow-up.
