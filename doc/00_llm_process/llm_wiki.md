# LLVM 23.1 Backend and Platform Evidence

LLVM backend/bootstrap work and every related platform lane use the
repository-managed Clang/LLVM 23.1 provider.  Until the stable upstream release
exists, the provider is pinned to the signed `llvmorg-23.1.0-rc2` source tag
(commit `561093d`); describe it as a release candidate, not as LLVM 23.1.0
final.  Build or verify it with
[`scripts/setup/build-llvm-23-1-provider.shs`](../../scripts/setup/build-llvm-23-1-provider.shs),
set `LLVM_23_1_PREFIX` (and normally `SIMPLE_LLVM_PREFIX`) to that one prefix,
and retain the provider verification/evidence for `clang`, `ld.lld`,
`llvm-ar`, and `llvm-config` reporting 23.1.x.

Do not silently fall back to LLVM 18, a host LLVM, or the Rust in-process LLVM
lane.  The Rust LLVM path is legacy/bootstrap-only and is not evidence for the
production pure-Simple LLVM backend.  A rollback is valid only when requested
explicitly and recorded as such (for example an explicit
`--backend=cranelift` diagnostic lane); it must not change the normal provider
contract or be presented as LLVM 23.1 success.

Keep platform evidence precise:

- A native macOS ARM64 build/run proves only native macOS behavior.  A Linux
  cross compile or Mach-O object proves target-object generation, not Darwin
  linking, SDK availability, bootstrap, or execution.
- An AArch64 QEMU result proves the stated guest/QEMU path only.  It is not
  native ARM hardware evidence, and a QEMU capability/readiness check is not a
  guest compiler/bootstrap proof.
- Record the exact provider prefix, provider/tag hash, output hashes, command,
  host/guest target, and whether the result is native, cross, or emulated.

For the canonical commands, admission checks, browser staging, and bounded QEMU
evidence workflow, see
[Clang 23.1 Bootstrap, Browser, and QEMU Workflow](../07_guide/app/llm/clang_23_1_bootstrap_browser_qemu_workflow.md)
and the [SimpleOS LLVM toolchain guide](../07_guide/os/simpleos_llvm_toolchain.md).
