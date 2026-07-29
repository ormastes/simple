# Stage2 RV64 desktop native-build nil receiver

## Status

Open. Attempts 7–9 exhausted the bounded RV64 build window.

## Evidence

The retained attempt is:

`build/test-artifacts/shared_multilingual_gpu_fonts/rv64-current-stage2-llvm-lib/attempt-9/`

The canonical Stage2 process parsed the repaired package, network, syscall,
and driver sources, then printed:

```text
runtime error: field access on nil receiver
```

`build.exit` records wrapper exit `132`; `build.time` records terminating
signal `4`, elapsed `34.59s`, and maximum RSS `486380 KiB`.
`cache-file-count.txt` records `0`. No
`build/os/simpleos_riscv64_display_smoke.elf` was produced.

Disassembly localizes the nil trap at `0x43c8ad` to `Config.set`; its caller at
`0x8a40e0` is `CompilerDriver.parse_all_impl`, line 693. That caller
incorrectly assigned the result of `Dict.set`, poisoning `entry_modules`.
A one-line bracket mutation and flipped existing source-contract assertions
landed after attempt 9. This root-cause repair is build-unverified.

The explicit no-default `syscall6` wrapper and its final ABI contract assertions
landed in the dirty source overlay after this failed run. They are not evidence
for attempt 9 and must be verified in the next fresh bounded session.

## Exact resume

Run from the repository root in a fresh session:

```bash
sh test/01_unit/os/riscv64_syscall_abi_contract_test.shs

RV64_ATTEMPT_ROOT="$PWD/build/test-artifacts/shared_multilingual_gpu_fonts/rv64-current-stage2-llvm-lib/attempt-10"
RV64_CACHE_ROOT="$PWD/build/native_probe/shared-font-rv64-current-stage2-llvm-lib-cache/attempt-10"
mkdir -p "$RV64_ATTEMPT_ROOT" "$RV64_CACHE_ROOT/home" "$RV64_CACHE_ROOT/tmp"
set +e
/usr/bin/time -v -o "$RV64_ATTEMPT_ROOT/build.time" \
  /usr/bin/timeout --kill-after=30s 3600s \
  /usr/bin/env -i \
    HOME="$RV64_CACHE_ROOT/home" \
    TMPDIR="$RV64_CACHE_ROOT/tmp" \
    PATH="/usr/lib/llvm-18/bin:$PATH" \
    LD_LIBRARY_PATH=/usr/lib/llvm-18/lib \
    LC_ALL=C LANG=C \
    SIMPLE_LIB="$PWD/src" \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_NATIVE_ARENA_DECLS=1 \
    SIMPLE_BOOT_MINIMAL=1 \
    SIMPLE_OS_LOG_MODE=on \
    SIMPLE_NATIVE_BUILD_LINKER_SCRIPT="$PWD/examples/09_embedded/simple_os/arch/riscv64/linker.ld" \
    SIMPLE_LLVM_PATH=/usr/lib/x86_64-linux-gnu/libLLVM-18.so.1 \
    "$PWD/build/test-artifacts/shared_multilingual_gpu_fonts/stage2-bootstrap/attempt-6/bootstrap/stage2/x86_64-unknown-linux-gnu/simple" \
    native-build \
    examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl \
    --backend=llvm-lib \
    --target=riscv64-unknown-none \
    --cache-dir="$RV64_CACHE_ROOT/native" \
    --threads=1 \
    --low-memory \
    -o "$PWD/build/os/simpleos_riscv64_display_smoke.elf" \
    >"$RV64_ATTEMPT_ROOT/build.stdout" \
    2>"$RV64_ATTEMPT_ROOT/build.stderr"
status=$?
printf '%s\n' "$status" >"$RV64_ATTEMPT_ROOT/build.exit"
exit "$status"
```

Retain the exact command, identity, dirty-source patch, both streams, wrapper
exit, timing/RSS, cache inventory, and—only on success—ELF SHA-256,
`readelf`, and `nm` receipts. Do not rerun attempts 7–9.
