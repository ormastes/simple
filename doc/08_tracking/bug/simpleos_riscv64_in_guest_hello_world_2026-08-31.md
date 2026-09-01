# SimpleOS riscv64 in-guest hello world: native GREEN, interpreter blocked on Stage2 admission

Date: 2026-08-31
Base: `goal/simpleos-b1-merge-clobber-restore-20260831` @ `91b6b9f28dd`
Compiler used for every artifact below: the **Rust bootstrap seed**, freshly built
(`cargo build --release --bin simple` in `src/compiler_rust`). The pure-Simple
self-hosted compiler still cannot compile anything, and `bin/simple` /
`bin/release/x86_64-unknown-linux-gnu/simple` do not exist in this worktree at all.

## Status

| row | state | evidence |
|---|---|---|
| build sanity (kernel builds) | **GREEN** | `scripts/os/build-simpleos-riscv64-hello-kernel.shs` |
| run sanity (native hello in-guest) | **GREEN** | `scripts/check/check-simpleos-riscv64-hello-world-in-guest-opensbi.shs` |
| hello world in the INTERPRETER, in-guest | **RED** | blocked, literal refusal below |

Boot is real OpenSBI v1.4 as `fw_payload` given to QEMU as `-bios` only. No
`-kernel`, no `isa-debug-exit`; the gate self-checks its own assembled argv for
both. Literal serial excerpt (the program's own output, not a boot log):

```
OpenSBI v1.4
Platform Name             : riscv-virtio,qemu
...
[hello] SimpleOS riscv64 hello-world in-guest (OpenSBI fw_payload)
[hello] serial up, invoking the Simple hello-world program
HELLO_NATIVE_SIMPLEOS_RISCV64_OK hello world from Simple
HELLO_NATIVE_SIMPLEOS_RISCV64 second line proves the program kept running
[hello] native program exited rc=0
[hello] parking
```

Honest scope: the program runs in S-mode (kernel mode), not as a U-mode task
loaded off the guest's own filesystem. See the entry file's header.

## THE REMAINING BLOCKER (interpreter row)

`scripts/os/simpleos-native-build-riscv64.shs`, which builds
`bin/release/riscv64-unknown-simpleos/simple` — the in-guest interpreter payload —
refuses to run:

```
warning: building with the Rust bootstrap seed (explicitly selected): .../release/simple
warning: the resulting payload is STAGING evidence only and will FAIL both install-image provenance guards
Compiler: .../release/simple
simpleos-guest-simple-fs: builder admission receipt is not canonical
error: selected compiler lacks canonical Stage2 admission authority
```

This is a **deliberate policy gate, not a defect**: the seed is denied authority to
produce a shippable SimpleOS guest payload, and the compiler that would have that
authority is a deployed pure-Simple binary that does not exist here (the same
`bin/release/<triple>/simple` gap the x86_64 sibling lane reports). Routing around
it would produce an artifact both install-image provenance guards reject, so it was
not attempted. **Unblocking the interpreter row requires a real bootstrap
deployment, not more work in this lane.**

Everything BELOW that gate is now built and green, which is new:
`build/os/sysroot-riscv64` is complete (`libsimpleos_c.a`, `crt0.o`, 11 riscv64 C
runtime objects, `libsimpleos_all.a` = libc + C runtime + simple-core + crt0), and
`build/os/simple-core-simpleos-riscv64/libsimple_runtime.a` built with
`parts_built=19 parts_failed=0`.

## Defects fixed on the way (each had NEVER compiled)

Same class as the `runtime_native.c` incident in `.claude/rules/vcs.md`: source
that is well-formed as bytes, non-conflicted, correctly sized and symbol-preserving
— and nonsense to a compiler. Every one of these blocked the SimpleOS libc/runtime
cross-build on **every** architecture, not just riscv64.

1. `src/os/libc/simpleos_process.c` — `getgid`/`geteuid`/`getegid` each defined
   TWICE (single-user `return 0` block, plus an ENOSYS block). Duplicates deleted.
2. `src/os/libc/simpleos_dlmalloc.c` — called `_checked_add` and
   `_checked_round_up`, which were defined nowhere, and called `_mmap_pages` with
   an out-parameter it did not have. Implemented; `_mmap_pages` now reports the
   post-page-rounding size, which the caller registers as the region size.
3. `src/os/libc/simpleos_pthread_rwlock.c`, `simpleos_pthread_cond.c`,
   `simpleos_libc.c` — used `ENOSYS`/`EINVAL` with no `errno.h` include.
4. `src/os/libc/include/sys/socket.h` — no `sa_family_t`, no `AF_INET`/`AF_INET6`
   (kernel pins `_AF_INET: u16 = 2`), no `send/recv/sendto/recvfrom/getsockopt/
   getsockname/getpeername`, no `struct sockaddr_storage`.
5. `src/os/libc/include/netinet/in.h` — no multicast options or `ip_mreq`/`ipv6_mreq`.
6. `src/os/libc/include/pthread.h` — `pthread_rwlock_*` implemented but never
   declared; the typedef now lives here rather than privately in the `.c`.
7. `src/os/libc/include/string.h` — `strpbrk` missing; the implicit declaration
   returned `int` into a `const char *`, truncating a 64-bit pointer.
8. `src/os/libc/include/sys/stat.h` — `fchmod`; `include/errno.h` — `EINPROGRESS`;
   `include/unistd.h` — `_SC_NPROCESSORS_ONLN`.

## Two further gaps fixed outside the libc

9. **Seed, cross bare-metal core-C injection.**
   `native_project/config.rs::selected_runtime_library` built the core-C archive
   with the plain host `cc` and no `--target=`, so a freestanding CROSS link got
   HOST-arch objects:
   `ld.lld: error: libsimple_runtime.a(runtime_memory.o) is incompatible with
   _boot_freestanding_runtime.o` (verified: boot object ARM aarch64, every archive
   member x86-64). Fixed by returning no archive for non-host `TargetOS::None`,
   where the boot dir's `freestanding_runtime.c` is the intended substitute.
   Scoped to non-host so x86_64-on-x86_64 SimpleOS lanes are byte-for-byte
   unchanged. **This also means `scripts/os/build-simpleos-aarch64-limine-kernel.shs`
   could not be reproduced from source with any recent seed** — it fails
   identically before this fix.
10. **`boot_entry` was defined nowhere.** `arch/riscv64/boot/crt0.S` does
    `call boot_entry`; a repo-wide grep found only that call site and its comment.
    The seed aliases `_start`/`spl_start`/`main` but never `boot_entry`, so **no**
    riscv64 entry `.spl` could link through this crt0 — which is why the existing
    `check-simpleos-riscv64-opensbi-guest-boot.shs` links a hand-written C probe
    with gcc instead of going through `native-build`. Added
    `arch/riscv64/boot/boot_entry.c`, the documented one-call shim.

## Files added

- `examples/09_embedded/simple_os/arch/riscv64/hello_world_sbi_entry.spl`
- `examples/09_embedded/simple_os/arch/riscv64/boot/boot_entry.c`
- `scripts/os/build-simpleos-riscv64-hello-kernel.shs`
- `scripts/check/check-simpleos-riscv64-hello-world-in-guest-opensbi.shs`
  (10 fatal selftest fixtures, incl. a must-FAIL on a boot-log-only capture and on
  a transcript with guest output but no firmware banner)

An aarch64 equivalent of the same three files also exists and is GREEN; it was
built before the riscv64-only priority change and is left in place.

## Known local-only workaround, not a fix

`build/os/fat32-riscv64.img` (16 MB, `mkfs.vfat`) had to be created by hand
because `arch/riscv64/boot/full_networking_runtime.c` `incbin`s it and the tracked
tree does not ship it (`Could not find incbin file 'build/os/fat32-riscv64.img'`).
The hello lane never mounts it. The real producer is
`scripts/check/rebuild-sosix-qemu-media.shs`; the build should either depend on
that or stop unconditionally incbin-ing media into every riscv64 entry.

Separately, autodiscovery compiles `*.inc.c` files as standalone translation
units, which fails for four of them under `arch/riscv64/boot/`. It is non-fatal
today (they are `#include`d by the real TU) but it makes every riscv64 build log
carry spurious "failed to compile" lines that mask real errors.
