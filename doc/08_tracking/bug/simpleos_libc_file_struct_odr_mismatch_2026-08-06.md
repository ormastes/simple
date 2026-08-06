# SimpleOS libc defines `struct __simpleos_FILE` twice, with incompatible layouts

Status: OPEN
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

## Not fixed here

Out of scope for the runtime-port lane, and it touches stdio init for every
SimpleOS program, so it wants its own change and its own boot test rather than
being folded into a link-unblocking commit.
