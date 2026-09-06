# SimpleOS target-native image continuity — artifact-gated

Status: **BLOCKED — source continuity implemented; target artifacts absent**

The earlier SDN path-injection blocker is closed statically. Role admission and
manifest rendering both reject empty/trimmed, control/NUL/newline, quote,
backslash, dot/traversal, duplicate-separator, and otherwise noncanonical host
artifact paths before image construction. The public renderer reconstructs
role inputs, reruns full role/SMF/digest/duplicate admission, emits only the
canonical guest-path set, and rejects supplied digest or guest-path mismatch.
Behavioral specs cover adversarial paths and forged role fields. Target
artifacts and guest execution evidence remain absent, so the feature status
stays `BLOCKED`.

Scope: the Phase-2 disk-image bake now admits explicit target-native init,
compiler, interpreter, and loader payloads once, then feeds the same admitted
paths and bytes to both the FAT32 image and `initramfs_pack`. Generic `/bin/simple`, `/usr/bin/simple`,
and `/sys/apps/simple` aliases are compiler-role aliases only. Every role is
required to be non-empty and has a pure-Simple SHA-256 digest; paths and
digests must be pairwise distinct. Browser and version evidence are explicit
inputs rather than hello-ELF/generated-text stand-ins.

## Artifact inventory captured read-only

The workspace has no `build/os/llvm/cross-x86_64-unknown-simpleos`,
`build/os/llvm/cross-aarch64-unknown-simpleos`, or
`build/os/llvm/cross-riscv64gc-unknown-simpleos` directory, and no populated
`build/os/sysroot` was present. Therefore no target-native compile/link/run
claim is made for any row.

| target row | canonical triple | state | required next evidence |
|---|---|---|---|
| x86_64 | `x86_64-unknown-simpleos` | BLOCKED: LLVM/sysroot/roles absent | admitted filesystem `clang` + `ld.lld` compile/link/run receipt |
| AArch64 | `aarch64-unknown-simpleos` | BLOCKED: LLVM/sysroot/roles absent | same receipt with AArch64 target identity |
| RV64GC | `riscv64gc-unknown-simpleos` | BLOCKED: LLVM/sysroot/roles absent | same receipt with RV64GC/LP64D identity |

The canonical RV64 spelling is `riscv64gc-unknown-simpleos`; no alternate
`riscv64-unknown-simpleos` row is admitted.

## Guardrails

- `SIMPLETOOL.SDN` and all canonical role paths remain required.
- Missing artifacts fail before FAT32 or initramfs construction.
- Host `PATH`, host compilers, fixed responder text, and Rust-seed output are
  not evidence of target-native guest execution.
- A future target row may move from BLOCKED only after the guest-resident
  artifact is admitted, its manifest digest is bound, and an arbitrary
  filesystem source is compiled, linked, loaded, and run with exact output.
