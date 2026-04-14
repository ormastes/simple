# SimpleOS rustc fork patches

Local patch set applied against the `ormastes/rust` fork (branch `simpleos`).
Two independent pieces land together:

1. **Built-in target specs** under `compiler/rustc_target/src/spec/targets/`
   so `rustc --target x86_64-unknown-simpleos` (plus aarch64 / riscv64gc /
   riscv32imac) works without `--target <path>.json`.
2. **A libstd PAL** under `library/std/src/sys/pal/simpleos/` that backs the
   primitives libsimpleos_c exposes: allocator, argv, getenv, exit,
   stdio/fs, clock_gettime. Threads/process/pipe/net are Unsupported stubs.

## Workflow

```bash
cd ~/rust                                   # ormastes/rust checkout
git checkout simpleos                       # fork branch
/path/to/simple/src/os/port/rust/patches/apply.sh .
# ...edit the two mod.rs files per apply.sh's manual-follow-up notice...
./x.py build library/std --target x86_64-unknown-simpleos
```

## Prerequisites

- Nightly `rustc` that matches the fork's `rust-toolchain.toml`.
- `rust-src` component (already present in the fork's `config.toml`).
- libsimpleos_c installed in the sysroot under
  `<sysroot>/lib/rustlib/x86_64-unknown-simpleos/lib/` with the expected
  exports (`malloc`/`free`/`realloc`/`calloc`, `open`/`close`/`read`/`write`/
  `lseek`/`stat`, `getenv`, `_exit`, `clock_gettime`, `write`).

## Validation inside SimpleOS

After a successful stage0 build, run the hello-world smoke test from a
QEMU SimpleOS guest:

```bash
rustc --target x86_64-unknown-simpleos \
      -C link-arg=-Lpath/to/libsimpleos_c \
      examples/hello.rs -o hello
./hello
```

Expected: prints `hello, simpleos\n` via fd 1, returns 0.

## Known limitations

- **No threads.** `std::thread::spawn` returns `ErrorKind::Unsupported`;
  `available_parallelism()` reports 1.
- **No process spawning.** `Command::spawn` returns Unsupported. No pipes.
- **No networking.** TCP/UDP/hostname lookups all return Unsupported.
- **No filesystem beyond open/read/write/close/lseek/stat.** No directory
  iteration, no symlinks, no `rename`/`unlink`.
- **No thread-local storage** — the target spec disables TLS
  (`has-thread-local=false`); use explicit `OnceLock`-style globals.

## File map

```
patches/
  apply.sh                      # copy helper (idempotent)
  README.md                     # this file
  compiler/rustc_target/src/spec/
    targets/x86_64_unknown_simpleos.rs
    targets/aarch64_unknown_simpleos.rs
    targets/riscv64gc_unknown_simpleos.rs
    targets/riscv32imac_unknown_simpleos.rs
    mod.rs.patch.md              # supported_targets! insertion notes
  library/std/src/sys/pal/simpleos/
    mod.rs alloc.rs args.rs env.rs exit.rs fs.rs io.rs
    stdio.rs time.rs thread.rs process.rs pipe.rs net.rs
```
