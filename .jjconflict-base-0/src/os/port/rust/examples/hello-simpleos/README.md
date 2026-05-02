# hello-simpleos

Minimum-viable `#![no_std]` Rust binary that validates the SimpleOS Rust
cross-compile pipeline end-to-end. Uses only `core` and links against
`libsimpleos_c` for `write(2)` and `_exit(2)`.

## Prerequisites

- Nightly Rust toolchain (for `-Z build-std`)
- `rust-src` component: `rustup component add rust-src --toolchain nightly`
- `libsimpleos_c.a` sysroot built via `sh src/os/port/llvm/sysroot.shs`
- Target spec at `src/os/toolchain/rust/x86_64-unknown-simpleos.json` (Wave 1)

## Build

```bash
cd src/os/port/rust/examples/hello-simpleos
SIMPLEOS_SYSROOT=$(pwd)/../../../../../build/os/sysroot \
    cargo +nightly build --release
```

The crate-local `.cargo/config.toml` selects the custom JSON target and
enables `build-std` for `core`, `alloc`, and `compiler_builtins`.

## Output

```
target/x86_64-unknown-simpleos/release/hello-simpleos
```

Verify it is a statically-linked freestanding ELF:

```bash
file target/x86_64-unknown-simpleos/release/hello-simpleos
# Expected: ELF 64-bit LSB executable, x86-64, statically linked, ...
```

## Running (future)

Run under QEMU once the SimpleOS loader wiring lands in Workstream C:

```bash
# Placeholder: qemu-system-x86_64 -kernel ... -initrd hello-simpleos
```

## Known limitations

- No stdout buffering; message is emitted via raw `write(1, ...)`.
- Panic handler prints `rust panic\n` to fd 2 and exits 101; no unwinding.
- `alloc` is built but unused — kept so downstream examples can enable it
  without reconfiguring the crate.
- Requires nightly until `build-std` stabilizes.
