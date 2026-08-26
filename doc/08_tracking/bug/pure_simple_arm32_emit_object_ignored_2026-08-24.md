# Pure-Simple ARM32 `--emit-object` admission remains open

## Status

**SOURCE CANDIDATE PRESENT; EXECUTION OPEN.** Current Pure-Simple source accepts
`--emit-object` and preserves explicit ARM32 `eabihf`, and this lane adds an
exact relocatable-link runner for the Cosmos FSBL candidate. No freshly
provenance-admitted Stage-4 compiler has executed that runner here. The
firmware prerequisite and production cutover are therefore not closed.

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
SIMPLE_BINARY=/absolute/path/to/fresh-admitted-stage4/simple \
  sh test/02_integration/os/cosmos/run_pure_simple_arm32_emit_object_test.shs
```

The runner canonicalizes the compiler path, validates its adjacent Stage-4
provenance receipt, rejects Rust/bootstrap/debug identity, and binds the
compiler digest before and after the run. It compiles the actual
`src/os/kernel/arch/arm32/cosmos/cosmos_fsbl.spl` candidate and checks ELF32,
ET_REL, EM_ARM, hard-float attributes, the exact exported
`cosmos_fsbl_validate_handoff` and `cosmos_fsbl_selftest` functions, real ARM
consumer relocations, successful `ld.lld -r` combination, and no remaining
undefined symbol.

The consumer supplies only `cosmos_fsbl_mmio_read32` and
`cosmos_fsbl_platform_is_qemu`. These are required volatile-I/O/platform ABI
shims, not foreign owners of FSBL validation policy.

## Closure evidence and limits

Closing this blocker requires a retained result binding the admitted compiler
and provenance, command, candidate source, object digest, ELF header, symbols,
relocations, and combined object. This source-only candidate has not been run
or verified in this lane. Even a passing ET_REL runner does not authorize
removing production `cosmos_fsbl.c`: physical ARM/QEMU boot, package wiring,
and reproducible x86-host bootstrap/build evidence remain separate cutover
gates.
