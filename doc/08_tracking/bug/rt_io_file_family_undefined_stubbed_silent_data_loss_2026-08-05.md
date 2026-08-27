# `File.write` reports Ok and writes NOTHING — all 13 `rt_io_file_*` externs are undefined and RT_KEEP-stubbed

Date: 2026-08-05
Lane: IO-REWIRE
Status: CONFIRMED. Silent data loss in an exported stdlib API.
Severity: HIGH (silent, exit 0, engine-divergent)

## Summary

`src/lib/nogc_sync_mut/io/file.spl` — the public `FileHandle` / `File` API,
re-exported from `std.nogc_sync_mut.io` — declares 13 `extern fn` symbols that
**are defined nowhere in the repo**. Under native/JIT they are silently replaced
with fabricated zero-returning stubs, so `File.write` returns `Ok`, creates no
file, and every subsequent read returns empty. Exit status is 0 throughout.

## The 13 undefined symbols

Declared at `src/lib/nogc_sync_mut/io/file.spl:504-516`:

```
rt_io_file_open   rt_io_file_read     rt_io_file_read_all  rt_io_file_read_line
rt_io_file_write  rt_io_file_write_all rt_io_file_seek     rt_io_file_flush
rt_io_file_close  rt_io_file_metadata  rt_io_file_set_permissions
rt_io_file_exists rt_io_file_delete
```

None is defined in `src/compiler_rust/runtime/**`, `src/runtime/*.c`, `build.rs`
codegen, or the interpreter's extern registry.

## Evidence — `nm`, with a positive control

```
$ /usr/bin/nm -g --defined-only src/compiler_rust/target/bootstrap/libsimple_runtime.a \
    | /usr/bin/grep -c 'rt_io_file'
0
$ /usr/bin/nm -g --defined-only src/compiler_rust/target/bootstrap/libsimple_runtime.a \
    | /usr/bin/grep -c ' T rt_file_'
43
```

The positive control matters: the *other*, correctly-defined family `rt_file_*`
(43 symbols — `rt_file_open`, `rt_file_read_text`, `rt_file_write_text`,
`rt_file_size`, `rt_file_exists`, `rt_file_delete`, …) is present in the same
archive. So the zero is a real absence, not a broken `nm` invocation.

## Mechanism — RT_KEEP suppresses the link-time check

`src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:569` is supposed
to hard-fail a native link on any undefined `rt_*` symbol:

```rust
.filter(|s| s.starts_with("rt_") && !RT_KEEP.contains(s) && !real.contains(*s))
```

All 13 are listed in `RT_KEEP` at `stubs.rs:195-208`, so the filter drops them
and each one instead receives the fabricated zero-returning stub that the file's
own header comment warns about. The allowlist that exists for *compiler-internal
bootstrap placeholders* is here shielding a user-facing data path.

## Observed behavior (engine-divergent)

| engine | behavior |
|--------|----------|
| native / JIT | `File.write` returns **Ok**; no file on disk; `File.exists` = false; size 0; reads return `''`. **Exit 0.** |
| `SIMPLE_EXECUTION_MODE=interpret` | fails closed: `unknown extern function: rt_io_file_open` |

Probe verdict line:

```
VERDICT: FAIL rt_io_file family broken (4 failures)
```

This divergence is why a single-engine check is not evidence: the interpreter
refuses to run the path at all, so an interpreter-only suite never sees the data
loss, and a JIT-only suite sees a green `Ok` on a write that did nothing.

## Blast radius

- `file.spl` **is** in the Stage-3 closure via
  `src/lib/nogc_sync_mut/io.spl:153` (`export use ... {FileHandle, File}`), so
  it compiles and links in every bootstrap.
- It has **zero owned callers.** All 29 `File.open(` call sites live in the
  vestigial `src/compiler_rust/lib/std/**`.
- Owned code uses the *other* family, `io.file_ops` (426 references, backed by
  the defined `rt_file_*` symbols) — which is why this has never been noticed.

So today the damage is latent: the API is exported, documented-looking, and
importable, and the first owned caller to use it silently loses data.

## Why the `rt_file_*` family cannot simply absorb it

`rt_file_*` is overwhelmingly **path-level** (`read_text(path)`,
`write_text(path, ...)`). `file.spl` is an **fd-level** API. Only 4 of the 13
have a counterpart (`open`, `close`, `exists`, `delete`); the other 9 —
`read(fd,size)`, `read_all(fd)`, `read_line(fd)`, `write(fd,data)`,
`write_all(fd,data)`, `seek(fd,off,whence)`, `flush(fd)`, `metadata(fd)`,
`set_permissions(fd,ro)` — have none. `src/compiler_rust/runtime/src/value/
sffi/file_io/descriptor.rs` is the natural home: it already holds the fd-level
`rt_file_open` / `rt_file_get_size` / `rt_file_close`, and stops there.

## Ordering hazard for any fix

Removing entries from `RT_KEEP` converts every native build into a hard failure
for any symbol still undefined, and a Stage-3 bootstrap runs off the live
working tree. **Define the symbols first, verify with `nm`, and only then touch
`RT_KEEP`.** Never the reverse.

## Related cleanup landed with this report

`test/01_unit/lib/io/file_seek_openmode_native_check.spl` (lane FFI-ENUM) was
deleted. It asserted seek positions on this exact broken path, so it could only
ever fail — and it would have failed against the zero-stubs, not against the
FFI enum-crossing defect it claimed to test. Its header also asserted that an
interpreter run is "vacuous for this defect"; in fact the interpreter fails
closed with `unknown extern function`, which is the single clearest signal
available. Both of its conclusions were false.
