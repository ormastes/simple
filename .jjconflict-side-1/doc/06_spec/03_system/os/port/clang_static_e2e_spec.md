# Clang from the SimpleOS filesystem

Source: `test/03_system/os/port/clang_static_e2e_spec.spl`
Requirement: REQ-003
Status: active, fail-closed; source flow implemented, live proof blocked before QEMU.

## Primary flow

1. Require `SIMPLEOS_CLANG_FS_E2E=1`, the guest-native Clang payload, and the
   canonical `scripts/os/build_clang_disk.shs` QEMU wrapper.
   `SIMPLE_BUILD_COMPILER` must name a functional self-hosted compiler; Rust
   seeds and candidates that fail the exact `-c` output `2` smoke are rejected.
2. Run the wrapper and require exit code 0 plus SHA-256 identities for the
   current kernel and filesystem images. Skip modes, native-build failure,
   timeout, and unexpected QEMU exit codes fail.
3. Require its validated guest-produced ELF64 x86-64 relocatable object with
   an exact `main` symbol.
4. Require in-guest `/hello.elf` linking.
5. Require the resulting filesystem ELF to run in ring 3, emit the exact
   `hello-from-simpleos-clang` line, and exit with status 42. The shared
   production runner must report PASS before the Clang wrapper may report PASS.

## Evidence contract

```text
[clang-disk] PASS guest_exit=0 ... format=ELF64 type=REL machine=x86-64 symbol=main
[clang-disk] PASS guest_link=/hello.elf
hello-from-simpleos-clang
[syscall] exit status=42
[prod-ring3] PASS filesystem Simple ELF executed
[clang-disk] PASS guest_exec=/hello.elf output=hello-from-simpleos-clang
```

Historical LLVM bitcode, host-produced objects, marker-only output, missing
live prerequisites, and object-only runs fail this scenario.
