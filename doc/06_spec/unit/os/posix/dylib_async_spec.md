# Async Dynamic Library Specification

Native SimpleOS dynamic loading is async-first. The POSIX/libc `dlfcn` surface

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/posix/dylib_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Native SimpleOS dynamic loading is async-first. The POSIX/libc `dlfcn` surface
is a synchronous compatibility layer over this request model.

## Scenarios

### dylib_async backend ownership

#### routes self handles without kernel dynamic loader

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dylib_backend_for_path("")).to_equal(DYLIB_BACKEND_SELF)
expect(dylib_backend_for_path("self")).to_equal(DYLIB_BACKEND_SELF)
```

</details>

#### routes SMF and absolute paths to kernel dynamic loader

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dylib_backend_for_path("/lib/app.smf")).to_equal(DYLIB_BACKEND_KERNEL)
expect(dylib_backend_for_path("plugin.smf")).to_equal(DYLIB_BACKEND_KERNEL)
expect(dylib_backend_for_path("plugin.so")).to_equal(DYLIB_BACKEND_KERNEL)
```

</details>

#### rejects ambiguous relative paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dylib_backend_for_path("plugin")).to_equal(DYLIB_BACKEND_INVALID)
```

</details>

### dylib_async request lifecycle

#### opens the self handle as an already-complete async request

1. dylib async init
   - Expected: dylib_async_is_complete(req) is true
   - Expected: dylib_async_result(req) equals `DYLIB_MAIN_HANDLE`

2. dylib async free request


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_async_init()
val req = dylib_async_open("", 0)
expect(dylib_async_is_complete(req)).to_equal(true)
expect(dylib_async_result(req)).to_equal(DYLIB_MAIN_HANDLE)
dylib_async_free_request(req)
```

</details>

#### resolves known self symbols to stable ids

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dylib_builtin_symbol_id("simpleos_syscall")).to_equal(1)
expect(dylib_builtin_symbol_id("dlopen")).to_equal(8)
expect(dylib_builtin_symbol_id("missing")).to_equal(0)
```

</details>

#### reports builtin self symbols as process-callable

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dylib_symbol_is_process_callable(DYLIB_MAIN_HANDLE, "malloc")).to_equal(true)
expect(dylib_symbol_is_process_callable(DYLIB_MAIN_HANDLE, "missing")).to_equal(false)
```

</details>

#### returns ENOENT for unregistered kernel-backed paths

1. dylib async init
   - Expected: dylib_async_is_complete(req) is true
   - Expected: dylib_async_result(req) equals `0 - ENOENT as i64`

2. dylib async free request


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_async_init()
val req = dylib_async_open("/lib/plugin.smf", 0)
expect(dylib_async_is_complete(req)).to_equal(true)
expect(dylib_async_result(req)).to_equal(0 - ENOENT as i64)
dylib_async_free_request(req)
```

</details>

#### returns ENOENT for missing self symbols

1. dylib async init
   - Expected: dylib_async_is_complete(req) is true
   - Expected: dylib_async_result(req) equals `0 - ENOENT as i64`

2. dylib async free request


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_async_init()
val req = dylib_async_symbol(DYLIB_MAIN_HANDLE, "missing")
expect(dylib_async_is_complete(req)).to_equal(true)
expect(dylib_async_result(req)).to_equal(0 - ENOENT as i64)
dylib_async_free_request(req)
```

</details>

#### sync wrappers block over the async request surface

1. dylib async init
   - Expected: handle equals `DYLIB_MAIN_HANDLE`
   - Expected: dylib_symbol(handle, "malloc") equals `2`
   - Expected: dylib_close(handle) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_async_init()
val handle = dylib_open("", 0)
expect(handle).to_equal(DYLIB_MAIN_HANDLE)
expect(dylib_symbol(handle, "malloc")).to_equal(2)
expect(dylib_close(handle)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

