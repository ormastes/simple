# SOSIX QEMU matrix remaining owners

Status: OPEN

Canonical plan:
[`sosix_parallel_qemu_refactor.md`](../../03_plan/agent_tasks/sosix_parallel_qemu_refactor.md)

## Guest/runtime blockers

| Owner | Evidence location | Blocker | Unblock condition |
| --- | --- | --- | --- |
| RV64 compiler owner | `scripts/check/check-rv64-inline-asm-operand-transport.shs`; `examples/09_embedded/simple_os/arch/riscv64/` | No fresh admitted compiler/kernel/image row proves named/immediate inline-asm transport through live filesystem execution. Related: `asm_template_placeholders_never_bind_2026-08-07.md`. | Focused operand guard passes on the admitted full CLI, then the canonical Linux RV64 row emits ordered exit-37/reap evidence and a producer bundle. |
| x86_32 kernel owner | `scripts/check/check-x86-32-cpl3-lifecycle-contract.shs`; `examples/09_embedded/simple_os/arch/x86_32/` | The legacy path lacks the strong CPL3 entry, GDT/TSS/`esp0`, authenticated token, trap return, scheduler restoration, and mounted ELF lifecycle. | `--admit` proves strong linked owners, then the canonical Linux x86_32 row emits ordered exit-37/reap evidence and a producer bundle. |
| ARM32 kernel owner | `scripts/check/check-arm32-user-lifecycle-contract.shs`; `examples/09_embedded/simple_os/arch/arm32/boot/`; `src/os/kernel/arch/arm32/user_entry.spl`; `examples/09_embedded/simple_os/arch/arm32/fs_exec_entry.spl` | The current probe lacks real `enter_user_first.s`, exception-vector/SVC, authenticated token/result, mounted ELF entry, and exact reap. | `--admit` proves the vector/EL0/link owners, then the canonical Linux ARM32 row emits ordered exit-37/reap evidence and a producer bundle. |
| Full-CLI owner | `release/x86_64-unknown-linux-gnu/simple`; canonical plan replacement-lane receipt | The deployed full CLI exits 139 on `check` and focused interpreter `test`; Stage 3 lacks the full command surface and cannot substitute. | A source-matched admitted Stage 4 CLI passes the remaining compiler/lib/MCP and focused checks once. |

## External-host blockers

| Owner | Blocker | Exact first resume | Unblock condition |
| --- | --- | --- | --- |
| Windows operator | The PowerShell peer is preflight-only and no native Windows row has producer evidence. | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -AllGuests -Preflight` | Add the producer-backed native guest-run phase, then generate all six Windows bundles on Windows. |
| FreeBSD operator | Checksum-admitted FreeBSD 14.4 media and native execution are unavailable. | `sh scripts/qemu/simple-freebsd-media.shs --check` | Run all six rows on FreeBSD with admitted media and retain producer bundles. |
| macOS operator | No prepared Darwin executor has generated the six required bundles. | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --all-guests --run --parallel` | Generate six Darwin-host bundles; TCG remains correctness-only and cannot prove native timing. |

## Shared-owner implementation / verification

| Owner/source | Gap | Unblock condition |
| --- | --- | --- |
| Collector: `scripts/check/collect-sosix-qemu-evidence.shs` | Source repair implemented: any non-PASS row produces pending promotion. | Run the behavioral shared-owner gate and modern SSpec once on the admitted full CLI. |
| Media: `scripts/os/prepare_qemu_nonce_media.shs` | Source repair implemented: resolved source/run aliases are rejected before mutation. | Run direct, normalized, and symlink-alias behavioral fixtures once. |
| Matrix: `scripts/check/check-sosix-qemu-matrix.shs` | Source repair implemented: compiler validation receives the admitted runtime. | Prove path/SHA identity and pre/post runtime immutability in the behavioral gate. |
| System-test/docgen owner | The executable typed 24-row SSpec exists, but the deployed self-hosted runtime exits 139 both executing that spec and running docgen. | With a repaired source-matched admitted full CLI, run `release/x86_64-unknown-linux-gnu/simple test test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --mode=interpreter`, then `release/x86_64-unknown-linux-gnu/simple spipe-docgen test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --output doc/06_spec --no-index`; require PASS and zero stubs. |

All rows retain stable acceptance IDs in the canonical plan. This record may be
closed only after the matching implementation and canonical evidence land; a
plan-document completion or current-host handoff does not close it.
