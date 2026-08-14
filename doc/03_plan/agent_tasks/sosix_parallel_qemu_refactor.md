# SOSIX parallel QEMU refactor plan

## Objective

Complete the four-host, six-guest SimpleOS filesystem-execution matrix without
shared mutable-media races or false promotion. Every implemented row must boot,
list real `/SYS/APPS`, run a mounted filesystem program, return exit 37, reap
the exact task, and publish a canonical evidence bundle. macOS is postponed
only until a Darwin executor is available.

## Shared contract — owned by root

The following are immutable shared interfaces. Architecture/host lanes consume
them; they must not fork their own variants.

| Interface | Owner | Rule |
| --- | --- | --- |
| Settings/storage | `simple-qemu-settings.shs`, `simple-big-storage-root.shs` | Each worktree resolves its configured big-storage root; all mutable output lives below the per-run root. |
| Admission | `simple-qemu-host-admission.shs` | Produced before QEMU; binds actual host, QEMU binary/hash/version and accelerator. |
| Media | `make_os_disk.*`, `prepare_qemu_nonce_media.shs` | Base images are immutable; each row receives a copied image with separate collector and workload nonce slots. |
| Evidence | native producer + 24-row collector | Row producer owns artifacts; collector is the only parent-authoritative matrix commit. |
| Status ledger | `sosix_qemu_matrix_evidence_status_2026-08-13.md` | Every unavailable row stays visible with owner and exact resume command. |

The operator-facing settings, storage, admission, nonce, and evidence contract
is [SOSIX shared QEMU settings](../../07_guide/platform/simpleos/sosix_qemu_shared_settings.md).

Before a native-host run, an operator validates the reusable producer with:

```sh
sh scripts/check/produce-sosix-qemu-native-pass-bundle.shs --self-test
```

The fixture emits a temporary direct-kernel bundle only; it never substitutes
for a host admission or a row's real evidence.

## Parallel lanes

| Lane | Scope / exclusive owner files | Current state | Acceptance evidence | Sidecar | Merge owner | Final reviewer |
| --- | --- | --- | --- | --- | --- | --- |
| L0 shared matrix | settings, admission, producer, collector, matrix docs | active | self-tests; one pre-admitted bundle per changed schema; collector reject unless exactly 24 | N/A | root | root/high |
| L1 Linux x86_64 | x86_64 OVMF/GRUB fs-exec entry and boot artifacts | canonical PASS | OVMF→GRUB→guest-entry, real listing, mounted program stdout, exit37/reap/PASS | N/A | root | root/high |
| L2 Linux ARM64 | ARM64 direct-kernel fs-exec entry, nonce reader and EL0 lifecycle | canonical PASS | direct-kernel v2 bundle, exact ordered serial lifecycle | N/A | root | root/high |
| L3 Linux RV32 | RV32 direct-kernel trap lifecycle and nonce media | canonical PASS | direct-kernel v2 bundle, M-mode recovery and exact reap | N/A | root | root/high |
| L4 Linux RV64 | RV64 compiler operand transport, then live fs-exec | blocked | admitted compiler must lower named/immediate asm operands; fresh rebuild then canonical run | N/A | compiler owner | root/high |
| L5 Linux x86_32 | x86_32 GDT/TSS, CPL3 trap/token/stack and mounted ELF staging | blocked | live iret/int80/exit37 continuation plus exact scheduler reap | N/A | x86_32 kernel owner | root/high |
| L6 Linux ARM32 | ARM32 vector/SVC, token auth, staging and mounted ELF entry | blocked | real vector/TTBR lifecycle, target listing/program and exact reap | N/A | ARM32 kernel owner | root/high |
| L7 Windows | PowerShell matrix execution and native producer | blocked external host | actual Windows admission plus all six bundles; no Linux relabeling | N/A | Windows operator | root/high |
| L8 FreeBSD | image/bootstrap and native FreeBSD matrix execution | blocked external host | checksum-pinned image/bootstrap, then all six FreeBSD bundles | N/A | FreeBSD operator | root/high |
| L9 macOS | Darwin QEMU/firmware/native execution | postponed external host | prepared Darwin host, actual admission and six bundles | N/A | macOS operator | root/high |

## Parent-authoritative parallel protocol

1. Root freezes the shared scripts and the row descriptor before launching
   child lanes. Each lane gets a unique run ID, artifact directory, nonce pair,
   and no permission to edit shared collector state.
2. Each lane performs only its own source fixes, focused gates, one admitted
   rebuild and one bounded QEMU attempt per fresh diagnostic cycle. It writes
   either a complete producer bundle or a typed blocker receipt.
3. Child lanes return artifact paths, hashes, source commit/tree, first blocker
   and exact resume command. They do not copy a predecessor's PASS into a new
   source lineage.
4. Root verifies source/lineage, calls the producer for a valid row, and invokes
   the collector only with the aggregate source root. Collector rejection is
   expected until all 24 valid bundles exist.

## Dependency order

```text
L0 settings/admission/media/evidence
 ├─ L1 x86_64 PASS
 ├─ L2 ARM64 PASS
 ├─ L3 RV32 PASS
 ├─ L4 RV64 compiler fix → runtime closure
 ├─ L5 x86_32 privilege lifecycle → runtime closure
 ├─ L6 ARM32 privilege lifecycle → runtime closure
 └─ L7/L8/L9 actual-host operators
                       ↓
             root collector: exactly 24 bundles
```

## Current-host next sequence

1. Do not rerun L1–L3 unchanged green rows.
2. L4 first requires a clean admitted compiler that transports named and
   immediate inline-asm constraints; the bootstrap seed's debug spelling is not
   an acceptable workaround.
3. L5 and L6 proceed only through their frozen scalar trap ABIs; do not add
   untrusted user token pointers, weak dispatch bridges, or host test doubles.
4. L7–L9 retain their acceptance IDs as blocked/postponed, with the exact
   target-host commands in the status ledger.
