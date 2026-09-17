# rt_driver_poll_data interpreter marshalling returns header garbage

Date: 2026-09-16. Host: macOS arm64 (M4), seed binary rebuilt 2026-09-14
(`bin/simple`).

## Symptom

`rt_driver_poll_data(handle, index)` is declared in Simple as
`extern fn ... -> text`. The runtime symbol (seed twin
`src/compiler_rust/runtime/src/async_driver_sffi.rs:516`; C twin
`src/runtime/platform/async_driver.c:276`) returns a NaN-boxed RuntimeValue
string word (`ptr | 0b001`, `src/compiler_rust/runtime/src/value/core.rs:511`).

- Under the **JIT**, the call marshals correctly: probe reads returned the
  exact bytes (`"proac"` for a 5-byte read at offset 6, `"hello proactor"`
  for 14 bytes at 0).
- Under the **interpreter**, the dispatch
  (`src/compiler_rust/compiler/src/interpreter_extern/io_driver.rs:188`)
  treats the returned word as a raw `*const u8` and copies `data_len` bytes
  from it: `from_raw_parts(word as ptr, len)`. The word is the boxed heap
  handle, not the string data address, so the caller receives heap-header
  garbage of the right length (measured: 5 and 2 correct-length junk reads;
  `rt_driver_poll_data_len` is correct in both engines).

## Why it bites specs

Any spec-shaped file importing `std.spec.*` runs **interpreted** on this
seed: the spec package's own `skip` decorator factory returns a closure, and
the JIT refuses those ("function 'skip' creates a lambda/closure the JIT
closure ABI cannot compile … deferring to interpreter"). That fallback is
silent for ordinary specs — the `[INFO]` line only appeared when a *colliding*
`skip$dup1` variant (from additionally importing
`std.nogc_sync_mut.spec`) made the failure loud. So `bin/simple run
<spec>` never exercises the working JIT path for `rt_driver_poll_data`.

Related measurement: `rt_driver_submit_open` has the mirror-image ABI defect
in both engines — the bindings declare 4 parameters for a 5-parameter C ABI
and drop `path_len`, leaving `mode` (x4) uncontrolled; the same `O_RDONLY`
open returned `-22` (EINVAL) in one process and a valid fd in another (probe
sources inlined in the Appendix below; scratchpad copies deleted 2026-09-17).

## Workaround in product code

`src/lib/nogc_async_mut/sosix/macos_driver.spl` (sosix C5 macOS provider)
does not bind `rt_driver_poll_data` at all: the proactor read completion
(status/transferred/partial via `rt_driver_poll_result`) stays authoritative,
and read bytes are materialized with a positioned re-read through the deployed
typed alias `file_read_text_at`. Opens use `rt_io_file_open` (C1 pair) for
the same ABI reason.

## Fix direction (compiler lane)

Interpreter dispatch for `rt_driver_poll_data` should extract the string via
the runtime value API (as the JIT path effectively does) instead of
`from_raw_parts` on the boxed word; and the `rt_driver_submit_open` bindings
(interpreter extern block + JIT arg tables) need the 5th `path_len` parameter
restored so `mode` is caller-controlled. Until then, specs touching the
proactor data channel must stay on the workaround or run JIT-only non-spec
programs.

## Appendix — probe sources (inlined 2026-09-17; scratchpad copies deleted)

The two probes that produced the measurements above, kept inline so the record
is self-contained. Probe 1 exercises the full proactor surface including the
defective `submit_open` 5-param declaration; probe 2 drives the proactor from
a proven C1 `file_open` fd and sweeps `submit_open` flag variants.

Probe 1 (was `scratchpad/rt_driver_probe.spl`):

```simple
use std.nogc_async_mut.io.{file_write_text_at, file_remove}
use std.env.platform.{get_temp_dir}

@unsafe(reason: "probe: raw proactor FFI bridge", capabilities: [ffi])
extern fn rt_driver_create(queue_depth: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_destroy(handle: i64)
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_submit_open(handle: i64, path: text, path_len: i64, flags: i64, mode: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_submit_read(handle: i64, fd: i64, buf_size: i64, offset: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_submit_write(handle: i64, fd: i64, data: text, len: i64, offset: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_submit_close(handle: i64, fd: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_flush(handle: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll(handle: i64, max: i64, timeout_ms: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_id(handle: i64, index: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_result(handle: i64, index: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_data(handle: i64, index: i64) -> text
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_data_len(handle: i64, index: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_backend_name(handle: i64) -> text

fn reap(handle: i64, expect_op: i64) -> i64:
    val flushed = unsafe(capabilities: [ffi]):
        rt_driver_flush(handle)
    val n = unsafe(capabilities: [ffi]):
        rt_driver_poll(handle, 16, 0)
    print "  flush={flushed} poll={n}"
    var i: i64 = 0
    var found: i64 = -999999
    while i < n:
        val cid = unsafe(capabilities: [ffi]):
            rt_driver_poll_id(handle, i)
        val cres = unsafe(capabilities: [ffi]):
            rt_driver_poll_result(handle, i)
        val dlen = unsafe(capabilities: [ffi]):
            rt_driver_poll_data_len(handle, i)
        val d = unsafe(capabilities: [ffi]):
            rt_driver_poll_data(handle, i)
        print "  [{i}] id={cid} result={cres} data_len={dlen} data=\"{d}\""
        if cid == expect_op:
            found = cres
        i = i + 1
    found

fn main() -> i64:
    val path = get_temp_dir() + "/sosix_rt_driver_probe.bin"
    file_remove(path)
    val seeded = file_write_text_at(path, 0, "hello proactor")
    print "seeded={seeded} path={path}"

    val h = unsafe(capabilities: [ffi]):
        rt_driver_create(64)
    print "handle={h}"
    val backend = unsafe(capabilities: [ffi]):
        rt_driver_backend_name(h)
    print "backend_name=\"{backend}\""

    # O_RDONLY on macOS/BSD = 0
    val op_open = unsafe(capabilities: [ffi]):
        rt_driver_submit_open(h, path, path.len(), 0, 0)
    print "submit_open op={op_open}"
    val fd = reap(h, op_open)
    print "fd={fd}"

    val op_read = unsafe(capabilities: [ffi]):
        rt_driver_submit_read(h, fd, 5, 6)
    print "submit_read op={op_read}"
    val rd = reap(h, op_read)
    print "read_result={rd}"

    val op_write = unsafe(capabilities: [ffi]):
        rt_driver_submit_write(h, fd, "WORLD", 5, 6)
    print "submit_write op={op_write}"
    val wr = reap(h, op_write)
    print "write_result={wr}"

    val op_close = unsafe(capabilities: [ffi]):
        rt_driver_submit_close(h, fd)
    reap(h, op_close)

    unsafe(capabilities: [ffi]):
        rt_driver_destroy(h)
    file_remove(path)
    print "probe-done"
    return 0
```

Probe 2 (was `scratchpad/rt_driver_probe2.spl`):

```simple
use std.nogc_async_mut.io.{file_write_text_at, file_remove}
use std.nogc_sync_mut.sffi.fs.{file_open, file_close}
use std.env.platform.{get_temp_dir}

@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_create(queue_depth: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_destroy(handle: i64)
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_submit_open(handle: i64, path: text, path_len: i64, flags: i64, mode: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_submit_read(handle: i64, fd: i64, buf_size: i64, offset: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_submit_write(handle: i64, fd: i64, data: text, len: i64, offset: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_flush(handle: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll(handle: i64, max: i64, timeout_ms: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_id(handle: i64, index: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_result(handle: i64, index: i64) -> i64
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_data(handle: i64, index: i64) -> text
@unsafe(reason: "probe", capabilities: [ffi])
extern fn rt_driver_poll_data_len(handle: i64, index: i64) -> i64

fn reap(handle: i64, expect_op: i64) -> i64:
    val flushed = unsafe(capabilities: [ffi]):
        rt_driver_flush(handle)
    val n = unsafe(capabilities: [ffi]):
        rt_driver_poll(handle, 16, 0)
    print "  flush={flushed} poll={n}"
    var i: i64 = 0
    var found: i64 = -999999
    while i < n:
        val cid = unsafe(capabilities: [ffi]):
            rt_driver_poll_id(handle, i)
        val cres = unsafe(capabilities: [ffi]):
            rt_driver_poll_result(handle, i)
        val dlen = unsafe(capabilities: [ffi]):
            rt_driver_poll_data_len(handle, i)
        val d = unsafe(capabilities: [ffi]):
            rt_driver_poll_data(handle, i)
        print "  [{i}] id={cid} result={cres} data_len={dlen} data=\"{d}\""
        if cid == expect_op:
            found = cres
        i = i + 1
    found

fn main() -> i64:
    val path = get_temp_dir() + "/sosix_rt_driver_probe2.bin"
    file_remove(path)
    file_write_text_at(path, 0, "hello proactor")

    val h = unsafe(capabilities: [ffi]):
        rt_driver_create(64)

    # fd from the proven C1 sync open (O_RDONLY)
    val fd = file_open(path, 0)
    print "file_open fd={fd}"

    val op_read = unsafe(capabilities: [ffi]):
        rt_driver_submit_read(h, fd, 5, 6)
    print "submit_read(op={op_read}) offset=6 len=5"
    val rd = reap(h, op_read)
    print "read_result={rd} (expect 5)"

    # full read to test binary-safety of poll_data
    val op_read2 = unsafe(capabilities: [ffi]):
        rt_driver_submit_read(h, fd, 14, 0)
    print "submit_read2(op={op_read2}) offset=0 len=14"
    reap(h, op_read2)

    # proactor write on the O_RDONLY fd should fail EBADF (-9)
    val op_write = unsafe(capabilities: [ffi]):
        rt_driver_submit_write(h, fd, "WORLD", 5, 6)
    reap(h, op_write)

    # submit_open variants: is -22 flag-independent? (mode=x4 garbage theory)
    val o1 = unsafe(capabilities: [ffi]):
        rt_driver_submit_open(h, path, path.len(), 0, 0)
    print "submit_open flags=0 op={o1}"
    reap(h, o1)
    val o2 = unsafe(capabilities: [ffi]):
        rt_driver_submit_open(h, path, path.len(), 2, 0)
    print "submit_open flags=2(O_RDWR) op={o2}"
    reap(h, o2)
    val o3 = unsafe(capabilities: [ffi]):
        rt_driver_submit_open(h, path, path.len(), 0x202, 0)
    print "submit_open flags=0x202(O_RDWR|O_CREAT) op={o3}"
    reap(h, o3)

    file_close(fd)
    unsafe(capabilities: [ffi]):
        rt_driver_destroy(h)
    file_remove(path)
    print "probe2-done"
    return 0
```
