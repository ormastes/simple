# Pure Simple `rt_free(ptr, size)` ABI mismatch

- **ID:** `pure_simple_rt_free_two_argument_abi_mismatch_2026-08-02`
- **Status:** FIXED — claimed and repaired by `pure_parser_close` on 2026-08-02
- **Severity:** High (cross-platform runtime ABI mismatch)

## Reproduction

The canonical runtime ABI, C implementations, SDK header, codegen declaration,
and Rust JIT export all define `rt_free(ptr)`. Twenty pure-Simple source/test
files retained declarations or calls with a second size argument. Extra
arguments happen to be tolerated by common hosted x86_64 ABIs, but are not part
of the contract and cannot be relied upon across Windows, BSD, macOS, aarch64,
or SimpleOS toolchains.

## Scope

Migrate every pure-Simple declaration and call coherently to the one-pointer
ABI. This is an allocator-boundary repair only; it does not alter Stage 4 or
compiled-GC ownership/wiring.

## Fix and verification

All pure-Simple declarations and calls now pass one pointer. The repository
guard rejects any future two-argument declaration/call and verifies the C,
Rust, codegen, and SimpleOS boundary signatures. Its static platform matrix
covers hosted Linux/macOS/Windows/BSD on x86_64/aarch64 and the SimpleOS libc
or documented bump-arena boundary.

- `sh scripts/check/check-rt-free-abi.shs`: PASS
- focused `rt_free_abi_contract_spec.spl` interpreter run: PASS
- `bin/simple check src/lib`: PASS (existing warnings only)
- `git diff --check`: PASS
