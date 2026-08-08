# SimpleOS ARM64 LLVM 23.1 Provider Contract

**Executable spec:** `test/03_system/check/simpleos_arm64_llvm23_provider_contract_spec.spl`

The spec executes four bounded shell contracts with a 120-second outer
deadline. It does not treat source-text markers as evidence. Builder,
snapshot, and FreeBSD receipt contracts must exit successfully and emit their
canonical `PASS:` receipt. Any failure, timeout, or unexpected exit is a test
failure.

## Provider authority

The ARM64 producer admits one explicitly selected LLVM provider and records
the authenticated origin receipt and its caller-selected SHA-256 digest. It
does not use an arbitrary host `PATH` or per-tool override. The signed source
checkout and the checked-in Tobias Hieta release key are separate inputs to
that admission decision.

The provider contains ten canonical tools, all below the admitted prefix:

`clang`, `ld.lld`, `llvm-ar`, `llvm-as`, `opt`, `llc`, `llvm-config`,
`llvm-objcopy`, `llvm-nm`, and `llvm-readobj`.

Each tool is admitted at LLVM `23.1.0` and is recorded in the provider
receipt with its exact executable path and SHA-256 digest. The receipt also
records the provider schema, origin manifest digest, private snapshot
manifest digest, source tag, and peeled tag commit. The ARM build command is
bound to the private snapshot and the downstream QMP evidence path revalidates
the same receipt inputs and all ten tool hashes.

## Private snapshot contract

The snapshot contract creates or reuses a private, content-addressed provider
generation selected by the authenticated origin receipt digest. It copies the
origin receipt into `origin-provider.env`, copies the ten admitted tools into
the generation, computes the snapshot receipt, and seals the published
generation and receipt against ordinary mutation. It checks ownership, exact
paths, executable contents, receipt hashes, reuse, lock handling, unsafe
parents, and tampering rejection. The snapshot is the compiler authority;
the mutable shared provider is not consumed after snapshot admission.

## Contract statuses

The ARM shell contract runs its executable negative cases for escaped tools,
LLVM 18 tools, retargeted tag receipts, isolated signing-key rejection, and
the signed builder verification path. When
`SIMPLE_LLVM_23_1_TEST_SOURCE_DIR` is not configured, the signed-checkout
portion reports exit code `2` and an `UNAVAILABLE:` line. The SSpec accepts
that one explicit environment-dependent result, but never treats it as a
pass. With the signed checkout configured, the ARM contract must emit all
negative-case `*_status=pass` receipts and its final `PASS:` line.

The FreeBSD contract is receipt and admission evidence for the QEMU bootstrap
path; it does not claim that a FreeBSD VM was booted. Live guest compiler
execution requires a separate QEMU serial transcript. Likewise, host-provider
readiness does not prove that a compiler runs inside the ARM64 guest or that
guest output executes.
