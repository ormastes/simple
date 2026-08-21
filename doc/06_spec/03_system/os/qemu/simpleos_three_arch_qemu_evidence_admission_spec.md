# SimpleOS three-architecture QEMU evidence admission

> Operator manual for the no-QEMU structural admission scenarios.

| Field | Value |
|---|---|
| Evidence class | source-contract |
| Executable source | `test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl` |
| Live claim | none |
| Required guests | x86_64, AArch64, RV64GC |

## Preconditions

Use a source-matched pure-Simple Stage-4 runtime. The Rust seed, a stale
receipt, and a symlinked compiler are inadmissible.

## Workflow

1. Exercise the production receipt adapter without starting QEMU.
2. Read the closed admission profile from the production adapter.
3. Inspect the immutable artifact contract.

The scenarios require real assertions over the production checker. A passing
source-contract run proves only that the adapter rejects incomplete evidence;
it does not prove any guest booted.

## Live bundle admission

After a prepared-host run, invoke the adapter separately for each retained
canonical bundle:

```sh
sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check x86_64 BUNDLE_DIR
sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check arm64 BUNDLE_DIR
sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check riscv64 BUNDLE_DIR
```

Every command must pass against immutable bytes from the same source campaign.
Missing compiler admission, firmware code/UEFI variable store, target ABI, image/program hash, ordered
marker, or transcript evidence is BLOCKED/FAIL, never a skip.

At present every live `--check` returns nonzero with
`campaign-authority-and-no-follow-fd-owner-unavailable`. A claimed `status=pass`,
signed-looking text, argv, hashes, or `TEST PASSED` transcript cannot promote a
row. File paths are not re-opened for a live decision because an `! -L` check
followed by hashing is TOCTOU-prone. Promotion resumes only when one canonical
authority verifies the campaign signature and descriptor-bound no-follow
identity/hash evidence.

## Current limitation

No current bundle satisfies the profile. The existing x86_64 and AArch64
filesystem-exec rows use direct QEMU boot shortcuts, RV64 uses an opaque
default firmware selection, and canonical bundles do not yet retain the
Stage-4 compiler bytes plus source-bound admission receipt. The repository also
lacks the signed campaign and no-follow descriptor owner required to trust
those bytes.
