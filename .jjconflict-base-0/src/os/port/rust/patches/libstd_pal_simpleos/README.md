# libstd PAL for SimpleOS — patch bundle

This bundle seeds `library/std/src/sys/pal/simpleos/` in the `ormastes/rust`
fork (branch `simpleos`) with a minimal but real Platform Abstraction Layer
on top of `libsimpleos_c`. It is the Workstream B3 deliverable from
`/home/ormastes/.claude/plans/mutable-giggling-raccoon.md`.

## What it does

Provides real implementations (via `libsimpleos_c` externs) for:

- `alloc` — `System` global allocator on `malloc`/`free`/`realloc`/`calloc`.
- `io` / `stdio` — `Stdout`/`Stderr`/`Stdin` via `write`/`read` on fd 0/1/2.
- `fs` — `File::open`/`read`/`write`/`seek`/`set_len` via `open`/`close`/
  `read`/`write`/`lseek`/`ftruncate`; directory ops via
  `opendir`/`readdir`/`closedir`.
- `env` — `args()` walks a `__simpleos_argv_ptr` extern populated by the
  runtime.
- `time` — `Instant`/`SystemTime` via `clock_gettime`.
- `process::exit` — via `_exit`.
- `os::errno`, `error_string`, `getcwd`, `chdir` via libc.

Stubs returning `ErrorKind::Unsupported`:

- `net::*`, `Command::spawn`, `Thread::new`, `Mutex`/`RwLock`/`Condvar`
  contention paths, `current_exe`.

## How to apply

These `.patch` files are **plain Rust source** (not unified diffs). Apply by
copying each file into the target path in the rust fork:

```bash
RUST_FORK=~/rust          # ormastes/rust checkout on branch `simpleos`
PAL=$RUST_FORK/library/std/src/sys/pal/simpleos
mkdir -p "$PAL"
while IFS= read -r name; do
    case "$name" in
        mod.rs.patch)            cp "$name" "$PAL/mod.rs" ;;
        sys_common_mod.rs.patch) cp "$name" "$RUST_FORK/library/std/src/sys/mod.rs" ;;
        *.rs.patch)              base="${name%.patch}"; cp "$name" "$PAL/$base" ;;
    esac
done < apply_order.txt
```

Or invoke the existing helper at `../apply.sh` which knows the paths.

## Requires from libsimpleos_c

`malloc`/`free`/`realloc`/`calloc`, `open`/`close`/`read`/`write`/`lseek`/
`ftruncate` (syscall 43), `opendir`/`readdir`/`closedir`, `clock_gettime`,
`_exit`, `getcwd`, `chdir`, `errno`/`__errno_location` (TLS slot),
`strerror_r`, plus the `__simpleos_argv_ptr` / `__simpleos_argc` runtime
symbols.

Any `TODO:` markers in a `.patch` file point at symbols not yet in
`src/os/libc/simpleos_libc_ext.c` — extend libc separately.
