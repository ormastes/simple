# Clang 23.1 migration: ad-hoc bootstrap provider evidence

Date: 2026-08-04
Worktree: `/Users/ormastes/simple-clang-23-1-browser-demo`

## Provider provenance

- Authorized provider: `/Users/ormastes/simple/build/native_probe/simple`
- Identity: `simple-bootstrap 1.0.0-beta`
- Format: Mach-O 64-bit executable, arm64
- Size: 23,218,904 bytes
- SHA-256: `93480fcc6f062dbe6a80a8f1276fddf235520c36b4d2ef8b8ca4c8c9a4f570c1`
- The provider is outside the isolated worktree and was consumed read-only.

The previously reported native smoke was accepted as retained evidence and was
not repeated.

## Distinct no-stub ad-hoc bootstrap smoke

Command:

```sh
SIMPLE_BIN=/Users/ormastes/simple/build/native_probe/simple \
BUILD_DIR=build/clang_23_1_adhoc_bootstrap_zero_arg \
sh scripts/check/check-native-consecutive-zero-arg-receiver.shs
```

The wrapper sets `SIMPLE_NO_STUB_FALLBACK=1`, uses the Cranelift backend, builds
an entry closure from
`test/fixtures/compiler/native_consecutive_zero_arg_receiver.spl`, executes the
fresh result, and requires exact output `zero-arg-receiver-ok`.

Result: **PASS** (`native_consecutive_zero_arg_receiver_status=pass`).

- Fresh output: `build/clang_23_1_adhoc_bootstrap_zero_arg/probe`
- Output format: Mach-O 64-bit executable, arm64
- Output SHA-256: `945110ccb093fa8737e03679ff1de4c7e36cdaeea0a1d82bd88ab69cac3e2f13`
- Build receipt: 2 compiled, 0 cached, 0 failed; 0.1 s compile + 8.7 s link
- Build log: `build/clang_23_1_adhoc_bootstrap_zero_arg/native-build.log`

## Non-blocking provider-scope observation

`SIMPLE_BINARY=/Users/ormastes/simple/build/native_probe/simple sh
scripts/check/check-bootstrap-essential-tools-smoke.shs` was attempted once as
a broader candidate gate. It stopped at its first `simple run` probe with
`error: unknown command 'run'`. This provider is a bootstrap/native-build
artifact rather than the deployed all-command CLI, so that gate is outside its
admitted surface. It was not retried and does not invalidate the successful
no-stub native-build/execute smoke above.

## Clang 23.1 SimpleOS target smoke

The locally built upstream provider completed installation before this smoke:

- Prefix: `/Users/ormastes/simple-clang-23-1-browser-demo/build/toolchains/llvm-23.1.0-rc2`
- `bin/clang`: `clang version 23.1.0-rc2`, SHA-256
  `b366b29d23d6f04ff880666d0a2b8d43655574c9466c9b7a1f899f2fcac0023a`
- `bin/ld.lld`: `LLD 23.1.0`, SHA-256
  `37ecdea6b33ab13a3ec9bde20e586427c58a6f398e58912eb06fa3e1d3408f11`
- `bin/llvm-ar`: `LLVM version 23.1.0-rc2`, SHA-256
  `2b5477259e6ddfc0b1c5b45386e80e66474d8f4376506a5b1680483459773f3d`
- Source revision reported by Clang and LLD:
  `561093d94eb7156dea780c1c71a779824ef90e5b`

Distinct target command (shown with the absolute provider prefix abbreviated
as `P` only for readability):

```sh
P=/Users/ormastes/simple-clang-23-1-browser-demo/build/toolchains/llvm-23.1.0-rc2
D=/Users/ormastes/simple-clang-23-1-browser-demo/build/clang_23_1_adhoc_bootstrap_target
"$P/bin/clang" --target=x86_64-unknown-simpleos -ffreestanding -fno-pic \
  -mno-red-zone -c src/os/libc/simpleos_crt0.S -o "$D/simpleos_crt0.o"
"$P/bin/llvm-ar" rcs "$D/libsimpleos_crt0.a" "$D/simpleos_crt0.o"
"$P/bin/ld.lld" -m elf_x86_64 -r --whole-archive \
  "$D/libsimpleos_crt0.a" --no-whole-archive \
  -o "$D/simpleos_crt0_linked.o"
```

Result: **PASS** (`clang_23_1_simpleos_target_smoke=pass`). The exact Clang
23.1 provider emitted a freestanding `x86_64-unknown-simpleos` ELF object,
the matching `llvm-ar` archived it, and the matching LLD admitted and linked
the archive back into an ELF64 x86-64 relocatable object.

- `simpleos_crt0.o` SHA-256:
  `1e1055eb5e189c378be1927b09dc13ab57977b69e5d02b3059f6d7a3fcb3a5a2`
- `libsimpleos_crt0.a` SHA-256:
  `5d95adf040451f8109310e33936f30d6380586ab7b48cda8f24855214b4b238d`
- `simpleos_crt0_linked.o` SHA-256:
  `aac000cf3dc4f719d2650fec7b5d9d7d953791254535413d8ceefb3d1186cd30`

The first fixture candidate (`audit_stubs_fixture.c`) was rejected once
because a pure SimpleOS target correctly had no implicit host `stddef.h`.
Cycle 2 used the sysroot-independent production CRT assembly and converged;
there was no third cycle.

## Status

`STATUS: PASS` for both the authorized ad-hoc bootstrap provider lane and the
Clang 23.1-connected SimpleOS target lane. No source or implementation files
were edited by this lane.
