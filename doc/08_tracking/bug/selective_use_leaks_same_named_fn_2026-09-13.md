# Selective `use m.{a}` leaks m's same-named functions over the importer's own

- **Date:** 2026-09-13
- **Component:** interpreter / module name resolution
- **Binary:** `bin/release/x86_64-pc-windows-msvc/simple.exe` (Rust seed), `run`
- **Severity:** high — wrong function silently called; can die with rc 0 and no output

## Symptom

`std.nogc_sync_mut.http_client/request.spl` defines its own
`fn http_get(url) -> (text, text, list, text)`. After adding
`use std.nogc_sync_mut.io.http_sffi.{http_request_raw}` to that file, calls to
`http_get` resolved to `io.http_sffi.http_get`, which returns an
`SffiHttpResponse` object. A spec calling `request_add_header(http_get(url), ...)`
failed with `semantic: invalid operation: tuple index access on non-tuple type object`.
Only `http_request_raw` was named in the import list.

## Minimal repro (three files in one directory)

`leak_provider.spl`
```
class Obj:
    code: i64

fn http_get(url: text) -> Obj:
    Obj(code: 7)

fn helper() -> i64:
    42
```

`leak_consumer.spl`
```
use leak_provider.{helper}

fn http_get(url: text) -> (text, text):
    ("GET", url)

fn build() -> (text, text):
    http_get("x")
```

`leak_main2.spl`
```
use leak_consumer.{http_get}

fn main():
    val r = http_get("y")
    print "method={r.0} url={r.1}"

main()
```

| run | expected | actual |
|---|---|---|
| `simple run leak_main2.spl` | `method=GET url=y` | `method=nil url=nil` (provider's `Obj` came back) |
| same, calling `build()` inside the consumer | `method=GET url=x` | no output at all, rc 0 |
| control: delete `use leak_provider.{helper}` | `method=GET url=y` | `method=GET url=y` |

The only difference in the control is the selective import that names
`helper`, never `http_get`.

## Expected

A selective import binds only the listed names. A module's own top-level
definition always wins over anything a `use` brings in, and names that are not
listed must not become visible at all.

## Workaround in tree

`send_request` now lives in `src/lib/nogc_sync_mut/http_client/transport.spl`,
which defines no `http_*` builder names, so importing `io.http_sffi` there has
nothing to shadow. `request.spl` no longer imports `io.http_sffi`. Pinned by
`test/01_unit/lib/nogc_sync_mut/http_client/header_shim_spec.spl`, which calls
`http_get` through the root shim.

Related: the root shim's earlier `add_header as request_add_header` alias
resolved back onto the shim's own `add_header` and recursed forever. That is
likely the same resolution defect seen through an alias.
