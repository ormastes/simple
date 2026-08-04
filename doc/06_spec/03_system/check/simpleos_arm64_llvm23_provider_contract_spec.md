# SimpleOS ARM64 LLVM 23.1 Provider Contract

**Executable spec:** `test/03_system/check/simpleos_arm64_llvm23_provider_contract_spec.spl`

`scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` is the
canonical ARM64 desktop producer. Before it invokes the pure-Simple LLVM
backend, it requires both `LLVM_23_1_PREFIX` and `SIMPLE_LLVM_PREFIX`, resolves
both prefixes physically, and rejects a mismatch. It forbids per-tool
`CLANG`, `LINKER`, and `LLVM_AR` overrides so the resolver can only admit
`clang`, `ld.lld`, `llvm-ar`, `opt`, `llc`, `llvm-config`, and `llvm-objcopy` below that one
prefix. Each tool must be a non-symlink canonical path under the physical
provider prefix and report major/minor version `23.1`.
The prefix is restricted to manifest-safe absolute path characters so the
recorded command remains an exact replayable environment contract.

Before the build, the producer also executes the signed provider builder in
`--verify-only` mode against `LLVM_23_1_SOURCE_DIR`, then requires the exact
signed `llvmorg-23.1.0-rc2` peeled commit
`561093d94eb7156dea780c1c71a779824ef90e5b`. The builder receipt, source path,
tag, and commit are recorded; QMP repeats that authenticated verification before
launching the artifact.

Providers installed before this contract may lack `opt`, `llc`, `llvm-config`,
or `llvm-objcopy`. Re-run
`scripts/setup/build-llvm-23-1-provider.shs` with the signed source checkout;
its `--verify-only` mode deliberately rejects that incomplete layout.

The admitted shared provider contains eight tools, including `llvm-as`. The
ARM64 producer consumes and records its seven-tool subset: `clang`, `ld.lld`,
`llvm-ar`, `opt`, `llc`, `llvm-config`, and `llvm-objcopy`, with parsed versions
and SHA-256 values. It freezes the exact provider environment before
the build, re-hashes the tools afterwards, and the downstream QMP evidence
runner revalidates those paths, versions, hashes, and frozen command before it
can boot the produced kernel. The resolver is also part of the frozen source
fingerprint, so a change to admission code invalidates a prior receipt.

The companion shell gate
`scripts/check/check-simpleos-arm64-llvm23-provider-contract.shs` executes
negative cases for a provider tool escaping its prefix, an LLVM 18 tool, and a
retargeted tag receipt. It does not merely inspect source text.

This is **host-provider readiness** for an ARM64 SimpleOS native build. It
does not prove that a compiler runs inside the ARM64 guest or that guest output
executes. Those are separate claims and require a guest serial/QEMU execution
transcript showing the in-guest compiler invocation and the resulting program's
execution.
