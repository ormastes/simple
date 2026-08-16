# SOSIX QEMU matrix remaining owners

Status: OPEN

Canonical plan:
[`sosix_parallel_qemu_refactor.md`](../../03_plan/agent_tasks/sosix_parallel_qemu_refactor.md)

## Guest/runtime blockers

| Owner | Evidence location | Blocker | Unblock condition |
| --- | --- | --- | --- |
| RV64 compiler owner | `scripts/check/check-rv64-inline-asm-operand-transport.shs`; `examples/09_embedded/simple_os/arch/riscv64/`; `test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl` | Named/immediate transport and real lifecycle are implemented, but the new result-boundary spec has no provenance-admitted Stage-4 runner and no fresh admitted kernel/image row. | Run the focused spec once on a Stage-4 CLI, then rebuild and run the canonical Linux RV64 row for ordered exit-37/reap evidence and a producer bundle. |
| x86_32 kernel owner | `scripts/check/check-x86-32-cpl3-lifecycle-contract.shs`; `scripts/check/rebuild-sosix-qemu-media.shs`; `examples/09_embedded/simple_os/arch/x86_32/` | Source now binds `esp0` to the execution token's task/generation and the rebuild profile includes the parent SimpleOS, `src/os`, and `src/lib`, but the retained ELF predates the fix and lacks strong `rt_x86_32_tss_set_esp0`/`rt_x86_32_tss_bind_task`. | Rebuild once with an admitted Stage-4 CLI; require `--admit KERNEL_ELF` to prove strong entry/TSS binding/token symbols before the canonical exit-37/reap row. |
| ARM32 kernel owner | `scripts/check/check-arm32-user-lifecycle-contract.shs`; `examples/09_embedded/simple_os/arch/arm32/boot/`; `src/os/kernel/arch/arm32/user_entry.spl`; `examples/09_embedded/simple_os/arch/arm32/fs_exec_entry.spl` | Source owners and the retained linked ELF pass the strong EL0/vector/SVC/token admission gate; no fresh canonical live row proves exit 37 and exact reap. | Run the canonical Linux ARM32 row once with admitted source/media and retain its producer bundle. |
| Full-CLI owner | `release/x86_64-unknown-linux-gnu/simple`; canonical plan replacement-lane receipt | The deployed full CLI exits 139 on `check` and focused interpreter `test`; Stage 3 lacks the full command surface and cannot substitute. | A source-matched admitted Stage 4 CLI passes the remaining compiler/lib/MCP and focused checks once. |

## External-host blockers

| Owner | Blocker | Exact first resume | Unblock condition |
| --- | --- | --- | --- |
| Windows + guest owners | The six descriptors and x86_64 producer-backed path are source-present, but x86_32/ARM32/ARM64/RV32/RV64 lack the distinct `/SOSIXNON.TXT` echo and fail closed. No path has native Windows evidence. | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -AllGuests -Run` | Add five guest collector-nonce readers, verify native PowerShell/QEMU semantics, and retain six bundles; RISC-V64 also needs explicit OpenSBI path/id/version. |
| FreeBSD operator | Checksum-admitted FreeBSD 14.4 media and native execution are unavailable. | `sh scripts/qemu/simple-freebsd-media.shs --check` | Run all six rows on FreeBSD with admitted media and retain producer bundles. |
| macOS operator | No prepared Darwin executor has generated the six required bundles. | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --all-guests --run --parallel` | Generate six Darwin-host bundles; TCG remains correctness-only and cannot prove native timing. |

## Shared-owner implementation / verification

| Owner/source | Gap | Unblock condition |
| --- | --- | --- |
| Collector: `scripts/check/collect-sosix-qemu-evidence.shs` | Source repair implemented: any non-PASS row produces pending promotion. | Run the behavioral shared-owner gate and modern SSpec once on the admitted full CLI. |
| Media: `scripts/os/prepare_qemu_nonce_media.shs` | Source repair implemented: resolved source/run aliases are rejected before mutation. | Run direct, normalized, and symlink-alias behavioral fixtures once. |
| Matrix: `scripts/check/check-sosix-qemu-matrix.shs` | Source repair implemented: compiler validation receives the admitted runtime. | Prove path/SHA identity and pre/post runtime immutability in the behavioral gate. |
| System-test/docgen owner | The executable typed 24-row SSpec exists, but the deployed self-hosted runtime exits 139 both executing that spec and running docgen. | With a repaired source-matched admitted full CLI, run `release/x86_64-unknown-linux-gnu/simple test test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --mode=interpreter`, then `release/x86_64-unknown-linux-gnu/simple spipe-docgen test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --output doc/06_spec --no-index`; require PASS and zero stubs. |
| SOSIX positioned-I/O owner | `src/os/sosix/core/`; `src/os/sosix/fs/`; `src/os/kernel/abi/syscall_shim_positioned.spl`; `scripts/check/check-sosix-positioned-live-route.shs` | The live x86_64 dispatcher reaches strong 134/135 Simple leaves and adopts value-threaded state, but the default backend is explicitly unavailable and no production owner installs a true positioned backend. FAT32 still has no positioned primitive. The deployed pure-Simple CLI exited 139 before scenario output. | Add a true production backend/install owner, admit the rebuilt linked route, then run each focused spec once on a repaired provenance-admitted Stage-4 CLI. Do not substitute Stage 3 or the Rust seed. |
| Typed evidence importer owner | `sosix_qemu_v2_admission_record_hash_binding_2026-08-16.md`; `src/os/sosix/qemu_evidence/` | Collector hash binding and the closed v2 trusted importer are source-present. Focused mutation/late-row/artifact specs have not run on an admitted Stage-4 CLI; fd-pinned snapshot primitives are unavailable, leaving hostile concurrent replacement as a residual hardening gap. | Run both focused specs once on an admitted Stage-4 CLI; add fd-pinned read/hash support before claiming adversarial concurrent-filesystem hardening. |

All rows retain stable acceptance IDs in the canonical plan. This record may be
closed only after the matching implementation and canonical evidence land; a
plan-document completion or current-host handoff does not close it.
