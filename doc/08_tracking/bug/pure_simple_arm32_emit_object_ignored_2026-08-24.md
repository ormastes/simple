# Pure-Simple ARM32 `--emit-object` is ignored

## Status

SOURCE FIX PRESENT; EXECUTION OPEN — the current Pure Simple source accepts
`--emit-object`, preserves an explicit ARM32 `eabihf` bare-metal target, and
has an exact Cosmos relocatable-link acceptance runner. A freshly admitted
Pure Simple compiler has not executed that runner in this lane, so the
firmware prerequisite is not yet claimed closed.

## Reported observation

Repository revision: `227049b0c4518e2173851692562eaf5e03a89a75`.

One admitted Pure-Simple Stage-2 compiler supplied by the active bootstrap lane
had SHA-256:
`fdf6ab23361bedf5b0ec0502c2e58675d7150fcff61ed1ce716a40e6e672c1b5`.
Its external producing worktree reported the planner admission receipt at
`build/bootstrap/codex-placeholder-stage2/stage3-planner-admission.receipt`
but that receipt is not committed with this record. Therefore the result below
is an observed blocker, not durable cross-worktree proof.

To acquire a fresh compiler from the pinned revision for confirmation, use the
repository's documented Stage-2 admission flow:

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

## Current source implementation

The current Pure Simple CLI recognizes and advertises `--emit-object`, carries
the selection through `SIMPLE_NATIVE_BUILD_EMIT_OBJECT`, and makes entry
closure implicit for non-executable output. The driver copies a single backend
object or combines multiple objects with `ld.lld -r`, then returns without the
ET_EXEC/native link path.

The ARM32 target owner now distinguishes an explicit
`armv7-unknown-none-eabihf` request from the conservative `...-eabi` default.
Previously the bare-metal triple builder collapsed both requests to `eabi`, so
the emitted ELF attributes could disagree with a hard-float Cosmos consumer.

Exact pending execution coverage is:

```sh
SIMPLE_BIN=<fresh-pure-simple-compiler> \
SIMPLE_ADMITTED_COMPILER_SHA256=<sha256-of-that-compiler> \
  sh test/02_integration/os/cosmos/run_pure_simple_arm32_emit_object_test.shs
```

The runner requires an exact admission hash, successful nonempty identity,
rejects Rust/bootstrap/debug identity and ignored-option diagnostics,
then checks ELF32, ET_REL, EM_ARM, hard-float ABI attributes, the exact exported
`cosmos_simple_object_link_probe` global function, a real ARM call relocation,
successful `ld.lld -r` consumption, and absence of
`__aeabi_unwind_cpp_pr0` before and after combination.

This update is source-only and unverified by explicit instruction. Closing the
bug still requires binding the compiler hash, fixture blob, command, object
hash, ELF header/symbol/relocation output, and combined-object result.

## Unblocked adjacent work

The Cosmos mock-MMIO oracle now executes each stateful case in a separate
normally exiting process. That preserves test isolation without `fork` plus
`_exit` and allows an enabled per-process coverage handler to flush. Coverage
file naming and cross-process merge policy remain the responsibility of the
selected coverage runner.
