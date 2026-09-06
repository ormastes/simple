# Agent Task Plan: SimpleOS Complete OS Hardening

## Frozen coordination contract

Shared names: `FsDriver`, `DriverInstance`, `MountTable`, `WmService`, `ExecutableManifestV1`, `ExecutableAdmissionV1`, `ExecutableImageHandleV1`, `ServerLifecycleV1`, `ProtocolCapabilityManifestV1`, `SimpleOsCapabilityLedgerV1`, `SimpleOsEvidenceReceiptV1`.

Shared SSpec step/setup/checker names are frozen in `doc/03_plan/sys_test/simpleos_complete_os_hardening.md`. Placeholders fail with `fail("UNIMPLEMENTED: <REQ-ID>")`.

## Dependency DAG

```text
A00 contracts/owner map/evidence schemas
 ├─ F10 filesystem convergence → F20 authenticated exec → F30 per-ISA roles/toolchains
 ├─ W10 canonical WmService migration
 └─ E10 receipt validator/ledger owner
F30 → S10 server lifecycle integration
F10 + F20 + F30 + S10 + W10 + E10 → H10 architecture campaigns
H10 → P10 performance/security/duplication convergence → V10 final review
```

## Non-overlapping lanes

| Lane | Exclusive edit ownership | Inputs/results |
|---|---|---|
| A00 root merge | shared contracts/codecs, architecture/docs, integration ordering | sole shared-contract writer and merge owner |
| F10 filesystem | `fs_driver`, backend adapters, VFS mount/conformance tests | returns portable-core/durability receipts; no loader/server edits |
| F20 executable | manifests/admission/loader/cache/invalidation and ISA spawn paths | consumes F10 handles; returns authenticated process receipts |
| F30 toolchains | target catalog, role builders, sysroots, LLVM profile, tool manifest | isolated target caches; returns image/admission/guest receipts |
| S10 lifecycle | `ServerLifecycleV1`, HTTP/DB/SSH adapters | consumes admitted handles; bounded worker results |
| S20 protocols | protocol manifests and protocol conformance tests | immutable declarations/probe receipts; no lifecycle owner edits |
| W10 WM | `WmService`, input/render/framebuffer adapters and WM tests | sole scene/focus/window owner |
| E10 evidence | evidence receipt validation and ledger publication | sole ledger commit owner; runners submit candidates only |
| H11 x86_64 | x86 QEMU/native/physical scripts/evidence paths | no common production-source edits |
| H12 AArch64 | ARM QEMU/board scripts/evidence paths | no common production-source edits |
| H13 RISC-V 64 | RV QEMU/board/FPGA scripts/evidence paths | no common production-source edits |
| P10 perf/dedup | benchmarks, campaign analyzers, duplicate-owner reports | begins after functional merge; no capability promotion |
| V10 final review | verification report only | may reject; does not repair implementation |

## Parallel ownership

- VFS, loader, scheduler, server lifecycle, DB mutation, WM, and ledger each own one mutable root.
- Cross-domain values are explicitly copy, frozen share, owned move, scoped loan, handle, encoded payload, or lease.
- Child lanes write isolated artifacts/results. A00 validates dependencies and merges deterministically; E10 alone commits evidence status.
- Target/build workspaces and caches are separate per architecture and keyed by admitted compiler/target/sysroot/schema.
- Overlapping files require owner coordination before editing. Other-agent dirty files remain untouched.

## Sidecars and review

Lower-model sidecars used for design (all read-only, accepted only after `/root` merged findings into the draft):

- `/root/design_fs_exec` — `gpt-5.6-luna`, high: filesystem/authenticated-exec structure; accepted into filesystem/admission sections.
- `/root/design_toolchains` — `gpt-5.6-luna`, high: Simple/LLVM/userland construction; accepted into target/toolchain sections.
- `/root/design_servers` — `gpt-5.6-luna`, high: lifecycle/protocol/security; accepted into server sections.
- `/root/design_wm_arch` — `gpt-5.6-luna`, high: WM ownership/evidence/performance; accepted into WM sections.
- `/root/design_systest` — `gpt-5.6-luna`, high: SSpec/manual matrix; accepted into test plan subject to scaffold creation.
- `/root/design_ui_wm` — `gpt-5.6-luna`, medium: TUI/GUI evidence design; accepted into UI drafts.
- `/root/design_integration_tasks` — `gpt-5.6-luna`, high: dependency/ownership/merge plan; accepted into this plan.

Lower-model implementation sidecars may own only the non-overlapping lanes above. `/root` is merge owner. `/root/design_final_review` (`gpt-5.6-sol`, high) is the independent design acceptance reviewer; it returned FAIL on the first draft and its findings must be closed before design handoff. A fresh named highest-capability reviewer will own final generated-manual and production verification acceptance.

## Merge sequence

1. A00 contracts and codec/negative tests.
2. E10 validation/ledger without PASS promotion.
3. F10 filesystem convergence.
4. F20 admission/loader and per-ISA adapters.
5. F30 toolchains/userland, then S10/S20 servers and W10 WM where dependencies allow.
6. H11/H12/H13 campaign runners and evidence candidates.
7. P10 performance/security/duplication convergence.
8. V10 verification; release only on `STATUS: PASS` and `release_blockers=none`.

## Three-cycle limit

Cycle 1: contract/static/codec/owner guards. Cycle 2: behavioral integration and QEMU. Cycle 3: physical campaigns, fuzz/soak/performance, duplication/stub/doc gates. Do not rerun unchanged green commands; unresolved rows remain blocked with exact resume plans.
