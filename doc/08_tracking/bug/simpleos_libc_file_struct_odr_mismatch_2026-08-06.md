# SimpleOS libc defines `struct __simpleos_FILE` twice, with incompatible layouts

Status: FIXED 2026-08-06
Found: 2026-08-06, while porting the real Simple runtime to SimpleOS
(`simpleos_payload_link_missing_20_rt_symbols_2026-08-06.md`).

## Summary

Two translation units in `src/os/libc/` define the same tag `struct
__simpleos_FILE` with **different layouts**. `FILE` is an opaque
`typedef struct __simpleos_FILE FILE;` in `include/stdio.h`, so neither TU sees
the other's definition and the compiler cannot diagnose it.

| File | Definition | Size |
|---|---|---|
| `src/os/libc/simpleos_libc.c:362` | `struct __simpleos_FILE { int fd; };` | 4 bytes |
| `src/os/libc/simpleos_fs.c:116` | `struct __simpleos_FILE { int fd; int eof; int error; int mode; };` | 16 bytes |

This is undefined behaviour in C (one-definition rule for a tag used across TUs)
and, more concretely, a live out-of-bounds access.

## The concrete hazard

`simpleos_libc.c` allocates the three standard streams as **4-byte statics**:

```c
struct __simpleos_FILE { int fd; };
static struct __simpleos_FILE _stdin_f  = { 0 };
static struct __simpleos_FILE _stdout_f = { 1 };
static struct __simpleos_FILE _stderr_f = { 2 };
```

`simpleos_fs.c` implements `fread`/`fwrite`/`fclose` (and `fopen`, which
`malloc`s the full 16 bytes) against the **16-byte** view, touching `fp->eof`,
`fp->error` and `fp->mode`:

```c
size_t fread(void *buf, size_t size, size_t nmemb, FILE *fp) {
    ...
    if (r <= 0) {
        if (r == 0) fp->eof = 1;      /* +4  — past the end of _stdout_f */
        else        fp->error = 1;    /* +8  — past the end of _stdout_f */
```

So **any `fread`/`fwrite` on `stdin`/`stdout`/`stderr` writes up to 12 bytes
past the end of a 4-byte static object**, corrupting whatever `.data`/`.bss`
follows. `fclose(stdout)` would additionally `free()` a non-heap pointer.

This is latent rather than always-fatal only because most SimpleOS output goes
through `write(2)`/`printf` rather than `fwrite(stdout)`.

## Why it surfaced now

Adding `fdopen()` for the runtime port forced the question of which layout is
authoritative. `fdopen` was deliberately placed in `simpleos_fs.c` (not
`simpleos_libc.c`) so its `malloc(sizeof(struct __simpleos_FILE))` matches what
`fread`/`fwrite`/`fclose` actually read — i.e. the port works around this bug
rather than depending on it. The workaround is noted in a comment at the
`fdopen` definition.

## Fix

Hoist ONE definition into a shared internal header (e.g. `simpleos_libc.h`) and
delete both local copies, so every TU agrees:

```c
struct __simpleos_FILE { int fd; int eof; int error; int mode; };
```

Then re-initialise the three statics with the full field set
(`{ 0, 0, 0, O_RDONLY }`, `{ 1, 0, 0, O_WRONLY }`, `{ 2, 0, 0, O_WRONLY }`) and
make `fclose()` refuse to `free()` the standard streams.

A regression guard belongs with it: the layouts are only comparable at link
time, so a check that greps for more than one `struct __simpleos_FILE {`
definition across `src/os/libc/*.c` is the cheap durable version.

## Resolution (2026-08-06)

The 16-byte layout won: `simpleos_libc.c` only ever touched `->fd` (4 sites, all
offset 0), so 16 bytes is a strict superset and nothing had to shrink.

- New `src/os/libc/simpleos_file_internal.h` holds the single definition plus a
  `_Static_assert(sizeof(struct __simpleos_FILE) == 16)`. Both TUs include it;
  both local definitions are gone.
- The three statics are now `{ fd, 0, 0, mode }` of the unified type.
- `fclose()` recognises the standard streams by pointer identity
  (`is_std_stream`) and closes the fd without `free()`ing the static.
- `Makefile`: the new header is a prerequisite of the `%.o: %.c` pattern rule,
  so incremental builds cannot keep a stale object.

### Evidence

`readelf -sW simpleos_libc.o | grep _std`, before → after:

```
before:  _stdin_f  size 4    _stdout_f size 4 (0x08)   _stderr_f size 4 (0x18)
after:   _stdin_f  size 16   _stdout_f size 16(0x08)   _stderr_f size 16(0x20)
```

The statics are now genuinely the size every `fread`/`fwrite` writes.

Regression guard is structural, not a grep: a re-added local definition is a
hard compile error. Verified as a negative control —

```
.neg_control.c:365:8: error: redefinition of '__simpleos_FILE'
./simpleos_file_internal.h:24:8: note: previous definition is here
```

Runnable check: `src/os/libc/test/file_stream_roundtrip.c`, cross-compiled for
`x86_64-unknown-none-elf` and linked against `build/os/sysroot` (with `-lm`
ahead of the library group, as on real link lines). The standard-stream half —
the actual corruption path — runs and passes; the `fopen`/`fread`/`fwrite` half
needs a SimpleOS kernel and self-skips (see the follow-up below). Not run
in-guest: another lane owns the QEMU gates.

Both sysroot copies were refreshed — `build/os/sysroot/lib/libsimpleos_c.a` and
`build/os/sysroot/lib/libm.a`, which is a plain `cp` of it
(`src/os/port/llvm/sysroot.shs:304`) and is reached first via `-lm`.

## Follow-up found while fixing this

`simpleos_fs_stream_ops_lack_host_fallback_2026-08-06.md` — `fopen`/`fread`/
`fwrite` call `simpleos_syscall` directly and skip the Linux-host fallback that
`write()`/`read()` in `simpleos_libc.c` honour.
