# Pure-Simple ARM32 `--emit-object` is ignored

## Status

OPEN — blocks linking Pure-Simple Cosmos HAL owners into the ARMv7 firmware.

## Historical observation

At repository revision `227049b0c4518e2173851692562eaf5e03a89a75`, an
external Stage-2 artifact warned that `--emit-object` was ignored, produced an
ARM `ET_EXEC` rather than `ET_REL`, and retained
`__aeabi_unwind_cpp_pr0`. Its admission receipt and raw artifacts were not
committed, so this is diagnostic history, not durable evidence. The Rust seed
must not be substituted for a current full Pure-Simple Stage-4 compiler.

## Current source and exact pending acceptance

The driver source now carries `SIMPLE_NATIVE_BUILD_EMIT_OBJECT`, makes entry
closure implicit for non-executable output, copies a single backend object or
combines several through `ld.lld -r`, and returns without the executable link
path. ARM32 target selection distinguishes explicit
`armv7-unknown-none-eabihf` from the conservative `...-eabi` default.

The pending command is:

```sh
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 --backend=llvm --mode=dynload \
  --jobs=half --output=build/bootstrap/cosmos-object-probe-stage2 \
  --no-mcp --no-verify --progress
```

```sh
SIMPLE=build/bootstrap/cosmos-object-probe-stage2/stage2/x86_64-unknown-linux-gnu/simple
"$SIMPLE" native-build --backend llvm \
  --source test/fixtures/os/cosmos \
  --entry test/fixtures/os/cosmos/simple_object_link_probe.spl \
  --entry-closure --target armv7-unknown-none-eabihf --emit-object \
  -o build/hal-link-probe/simple_object_link_probe.o
file build/hal-link-probe/simple_object_link_probe.o
readelf -h build/hal-link-probe/simple_object_link_probe.o
readelf -Ws build/hal-link-probe/simple_object_link_probe.o
nm -u build/hal-link-probe/simple_object_link_probe.o
```

The exploratory run reported:

- the compiler warns `unknown option '--emit-object', ignoring`;
- it reports a freestanding link rather than relocatable-object emission;
- `file` identifies the output as `ELF 32-bit ... executable, ARM`;
- `readelf` reports `Type: EXEC`, not `REL`;
- `nm -u` reported an unresolved `__aeabi_unwind_cpp_pr0` symbol.

That exploratory artifact used an equivalent scalar exported function before
the stable fixture above was committed. The commands above have not yet been
rerun against the committed fixture; a future closing receipt must bind the
compiler hash, fixture blob, command, output hash, ELF type, and symbol table.

The same compiler's `native-build --help` does not advertise either
`--emit-object` or `--target`, despite those options existing in the current
Pure-Simple driver source. Do not feed this executable to the Cosmos firmware
relocatable link or fall back to the Rust seed. The migration prerequisite is
a Stage-4 Pure-Simple compiler that emits an ARM32 `REL` object and preserves
the exported C symbol in this fixture.

## Unblocked adjacent work

The Cosmos mock-MMIO oracle now executes each stateful case in a separate
normally exiting process. That preserves test isolation without `fork` plus
`_exit` and allows an enabled per-process coverage handler to flush. Coverage
file naming and cross-process merge policy remain the responsibility of the
selected coverage runner.
