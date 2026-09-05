# SimpleOS three-architecture QEMU evidence admission test plan

## Scope

This plan covers the hardware-independent admission boundary for retained
x86_64, AArch64, and RV64GC SimpleOS QEMU bundles. It excludes builds, QEMU
execution, physical hardware, and performance claims. The adapter consumes the
canonical SOSIX evidence schema; it is not another evidence producer.

## Acceptance

| Requirement | Executable scenario | Evidence | Status |
|---|---|---|---|
| REQ-ARCH-EVIDENCE-001 rejects missing/open evidence and symlinked compiler material | `simpleos_three_arch_qemu_evidence_admission_spec.spl` | checker self-test output | implemented; execution blocked on admitted Stage-4 runtime |
| REQ-ARCH-EVIDENCE-001 freezes the three target/firmware profiles | same | checker `--schema` output | implemented |
| REQ-ARCH-EVIDENCE-001 requires immutable compiler/kernel/image/program/firmware/argv/transcript/marker artifacts | same | checker `--schema` and future bundle admission | implemented; live bundles blocked |

Pass requires a source-matched pure-Simple Stage-4 compiler receipt, target
ELF/ABI checks, hash-exact retained files, real UEFI/OpenSBI firmware, no
QEMU-only `-kernel`/loader shortcut, ordered mounted-filesystem execution,
exit 37/reap evidence, and one terminal `TEST PASSED`. Those file-level checks
are non-authorizing diagnostics until a canonical owner verifies a signed
campaign envelope and hashes every artifact through the same already-open
no-follow descriptor. The current `--check` therefore always returns BLOCKED
and nonzero after reporting record structure.

Run the source-contract scenarios with:

```sh
bin/simple test test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl --mode=interpreter
```

Do not run that command through a Rust seed or bootstrap-only compiler.

## Manual and capture policy

All three source-contract scenarios are visible. The future live rows retain
binary, artifact, exec, and log evidence; no screenshots are required for this
filesystem-execution boundary.
