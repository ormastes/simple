# Lane 07 accepted review evidence

Accepted classifications captured: 31. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

## setup_shs_fails_on_dash_sh_2026-09-13 — scripts/setup/setup.shs fails on a dash /bin/sh host (rc=2, `bin/simple` never created)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/setup_shs_fails_on_dash_sh_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/setup_shs_fails_on_dash_sh_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/setup.shs:39](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/setup.shs#L39); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:40](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L40)
- Review rationale: Report describes dash abort before Windows guard. Current caller explicitly uses bash and helper exits non-Windows before set -o pipefail (line 54), removing both reported trigger paths. Owners identical at inventory/review targets; historical defect and duplicate remain valid, current execution untested.
- Review corrections: solution: worker unknown -> known; inspection_level: worker report_reviewed -> source_reviewed

## setup_shs_pipefail_dash_abort_before_windows_guard_2026-09-13 — `scripts/setup/setup.shs` aborts on Linux: `set -o pipefail` under dash fires before the Windows-only early-exit guard

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/setup_shs_pipefail_dash_abort_before_windows_guard_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/setup_shs_pipefail_dash_abort_before_windows_guard_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/setup.shs:39](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/setup.shs#L39); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:40](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L40)
- Review rationale: Full report reproduces fatal pipefail before uname. Exact target helper performs uname/exit first, then pipefail; caller also selects bash. Existing local control-flow remedy addresses the original cause without weakening failure propagation. Both owners unchanged since inventory; require fresh dash setup verification.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## setup_shs_pipefail_dash_incompatible_2026-09-13 — `setup.shs` fails on every Linux host where `/bin/sh` is dash

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/setup_shs_pipefail_dash_incompatible_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/setup_shs_pipefail_dash_incompatible_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/setup.shs:39](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/setup.shs#L39); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:40](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L40)
- Review rationale: Report distinguishes helper POSIX no-op contract from merely changing caller shell. Current helper itself puts non-Windows exit ahead of pipefail, satisfying that contract, and caller uses bash. Identical to inventory source; no current execution claim and no invalid closure.
- Review corrections: structural_change: worker yes -> no; inspection_level: worker report_reviewed -> source_reviewed

## sfnt_fvar_option_match_nil_baremetal_2026-08-04 — val-assigned Option match yields nil on freestanding native lane; table.offset faults

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/encoding/sfnt.spl:85](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/encoding/sfnt.spl#L85); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md)
- Review rationale: Report binds nil fall-through to freestanding value-position Option extraction disassembly. Current parse_fvar_axes replaces extraction with scalar table scan and explicitly labels it a workaround, leaving compiler marshalling unresolved. Owner unchanged between targets. Accept keep-open/unknown root remedy; hosted success cannot qualify freestanding extraction.

## sheets_ascii_width_ambiguous_string_builder_owner_2026_10_12 — Spreadsheet ASCII width HIR import selects wrong string builder owner

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sheets_ascii_width_ambiguous_string_builder_owner_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sheets_ascii_width_ambiguous_string_builder_owner_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/office/sheets/ascii_width.spl:2](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/office/sheets/ascii_width.spl#L2); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/string_builder.spl:62](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/string_builder.spl#L62); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/common/string_builder.spl:1](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/common/string_builder.spl#L1); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/hir/string_builder_owner_collision_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/hir/string_builder_owner_collision_spec.spl); `history:5ef5ec6879d`
- Review rationale: Current ASC/JIS source imports std.common.string_builder.RtStringBuilder; library declares RtStringBuilder while app provider declares StringBuilder. Regression loads both physical providers, expects qualified import success and ambiguous import rejection. Commit 5ef5ec6879d supplies local owner repair, unchanged since inventory. Runtime/HIR execution remains unqualified.
- Review corrections: structural_change: worker unknown -> no; recommended_action: worker fix_candidate -> fixed_pending_verification

## simpleos_arm64_riscv64_embedded_gui_missing_theme_install_call_2026-09-06 — arm64 and riscv64 embedded GUI entries import but never call `install_generated_simpleos_wm_theme()`

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_arm64_riscv64_embedded_gui_missing_theme_install_call_2026-09-06.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_arm64_riscv64_embedded_gui_missing_theme_install_call_2026-09-06.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl:128](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl#L128); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl:50](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl#L50); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/simpleos_cross_arch_theme_install_source_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/os/simpleos_cross_arch_theme_install_source_spec.spl)
- Review rationale: Both exact-target production entries invoke theme installation and identity receipt before framebuffer/scanout setup; focused source regression asserts exactly one install and ordering before override/VFS/engine. Owners unchanged across inventory/review; accept local source repair with live architecture-specific QEMU and performance qualification pending.
- Review corrections: solution: worker unknown -> known; structural_change: worker yes -> no; inspection_level: worker report_reviewed -> source_reviewed

## simpleos_bump_heap_no_free_interactive_session_2026-07-26 — x86_64 bump allocator never frees: the first post-boot keypress panics heap exhausted

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_bump_heap_no_free_interactive_session_2026-07-26.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_bump_heap_no_free_interactive_session_2026-07-26.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:725](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c#L725)
- Review rationale: Current freestanding free(void*) is explicit no-op and realloc always allocates again. Full report attributes large buffers to genuine software surfaces/atlas and labels heap enlargement mitigation. Accept historical/live-source reclamation problem with unknown safe remedy; retained versus frame-local lifetime audit remains necessary before arena reset.

## simpleos_combined_server_qemu_gate_stale_auth_toolchain_2026-08-21 — Combined SimpleOS server QEMU gate uses stale authority

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_combined_server_qemu_gate_stale_auth_toolchain_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_combined_server_qemu_gate_stale_auth_toolchain_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-simpleos-servers-qemu.shs:25](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-simpleos-servers-qemu.shs#L25); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-simpleos-servers-qemu.shs:139](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-simpleos-servers-qemu.shs#L139)
- Review rationale: Exact wrapper still selects src/compiler_rust/target/release/simple and runs sshpass -p simpleos with ignored SSH exit, then inspects serial. Report requires admitted compiler and configured public-key identity. Accept valid keep-open mismatch; complete remedy needs current server auth owner and transcript admission, not relaxed guard.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## simpleos_evidence_cryptographic_admission_gap_2026-08-20 — SimpleOS evidence cryptographic admission gap

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_evidence_cryptographic_admission_gap_2026-08-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_evidence_cryptographic_admission_gap_2026-08-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/evidence/admission_gates.spl:4](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/services/evidence/admission_gates.spl#L4)
- Review rationale: Current admission_gates has independent trust/policy/time/crypto/serialization gates false; first reason is trust-root-owner-unavailable. Full report describes exact-root/time and performance catalog source progress but no admitted proof. Accept valid keep-open qualification gap with unknown remaining implementation; flipping gates is not repair.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## simpleos_in_guest_toolchain_execution — Guest proves clang/rust fixtures exist but cannot execute a real compiler process or

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_in_guest_toolchain_execution.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_in_guest_toolchain_execution.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/port/guest_toolchain_execution_gate.spl:501](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/port/guest_toolchain_execution_gate.spl#L501); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/port/guest_toolchain_execution_gate.spl:563](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/port/guest_toolchain_execution_gate.spl#L563)
- Review rationale: Full report distinguishes prepared task/SMF stub markers from actual guest compiler operation. Current gate validates target/ABI/artifact/transcript receipt and explicitly returns BLOCKED even for structural completeness or legacy staging booleans. Accept valid evidence gap; real guest payload/control transfer remains untested and no root code remedy established.
- Review corrections: structural_change: worker yes -> unknown

## skia_raw_rgba_magic_constant_wrong_value_2026-09-06 — `RAW_RGBA_MAGIC` constant value does not match its documented 'RBPA' byte pattern

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/skia_raw_rgba_magic_constant_wrong_value_2026-09-06.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/skia_raw_rgba_magic_constant_wrong_value_2026-09-06.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/skia/feature/codec/raw_rgba.spl:14](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/skia/feature/codec/raw_rgba.spl#L14)
- Review rationale: Full report and complete codec show constant 1380012353 despite RBPA/0x52425041 contract; big-endian writer emits the constant and reader compares the same wrong value, so self-roundtrip masks defect. Correct value is 1380077633. Local constant correction is supported; current execution remains untested. Owner unchanged since inventory.
- Review corrections: solution: worker unknown -> known; structural_change: worker unknown -> no; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker keep_open -> fix_candidate

## smf_enum_def_serializes_variant_names_only_2026-08-21 — SMF `EnumDef` serializes variant NAMES only — arity, types, field names and discriminants are dropped

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_enum_def_serializes_variant_names_only_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_enum_def_serializes_variant_names_only_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/ast.spl:37](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/ast.spl#L37); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/smf_serialization.spl:339](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/smf_serialization.spl#L339); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize/deferred_deserialize.spl:515](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/40.mono/monomorphize/deferred_deserialize.spl#L515)
- Review rationale: Historical names-only EnumDef is superseded: current AST carries payload/discriminant lists; ENV2 writer serializes them, reader rejects missing marker and validates parallel list lengths before constructing fields. Coordinated format remedy is present, supporting fixed_pending_verification; constructor population and round-trip execution still need qualification, not invalid closure. Inspected codec unchanged since inventory.
- Review corrections: solution: worker unknown -> known; structural_change: worker unknown -> yes; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker keep_open -> fixed_pending_verification

## smf_manifest_written_but_never_verified_2026-08-17 — SmfManifest written but never verified on load

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_manifest_written_but_never_verified_2026-08-17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_manifest_written_but_never_verified_2026-08-17.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_api_interpret.spl:56](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_api_interpret.spl#L56)
- Review rationale: Full report and current try_load_smf_cached show source/ABI/interface admission added, but validate_smf still receives compile_options_hash_zero at100. Thus report is partially superseded yet options comparison remains a concrete unqualified surface. Requested options are not passed into this API; complete cache-key compatibility remedy remains unknown without inspecting all gate fields.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## sosix_full_bootstrap_concurrent_rust_input_drift_2026-08-11 — SOSIX release lineage blocked by concurrent Rust input drift

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_full_bootstrap_concurrent_rust_input_drift_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sosix_full_bootstrap_concurrent_rust_input_drift_2026-08-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:3625](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-from-scratch.sh#L3625)
- Review rationale: Full report plus current bootstrap guard compare Rust input fingerprints after Cargo and again before authority commit, rejecting both drift windows. This supports a genuine historical provenance blockage with functioning guard, not a compiler defect or invalid record. Current occurrence and operational recovery remain uncertain without stable snapshot evidence.
- Review corrections: validity: worker valid -> uncertain; inspection_level: worker report_reviewed -> source_reviewed

## sosix_owned_ipc_v1_continuation_and_cross_arch_reachability_2026-08-11 — SOSIX Owned IPC v1 Continuation and Cross-Architecture Reachability

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_owned_ipc_v1_continuation_and_cross_arch_reachability_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sosix_owned_ipc_v1_continuation_and_cross_arch_reachability_2026-08-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/ipc/syscall_ipc.spl:124](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/ipc/syscall_ipc.spl#L124); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/vfs/vfs_service.spl:176](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/services/vfs/vfs_service.spl#L176)
- Review rationale: Full report and current owned receive reject nonzero args3/4 with ENOSYS, preserving continuation gap. VFS now imports owned-v1 receive/reply and poll_once dispatches copied records, superseding the un-migrated VFS claim. Cross-architecture reachability and capability enforcement remain unproved; aggregate remedy/structural scope unknown.
- Review corrections: validity: worker valid -> uncertain; structural_change: worker yes -> unknown; inspection_level: worker report_reviewed -> source_reviewed

## sosix_qemu_v2_admission_record_hash_binding_2026-08-16 — v2 matrix manifest recorded admission_record_path_b64 without a sha256 binding the

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_qemu_v2_admission_record_hash_binding_2026-08-16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sosix_qemu_v2_admission_record_hash_binding_2026-08-16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/sosix/qemu_evidence/trusted_importer.spl:398](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/sosix/qemu_evidence/trusted_importer.spl#L398); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/sosix/qemu_evidence/trusted_importer.spl:480](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/sosix/qemu_evidence/trusted_importer.spl#L480)
- Review rationale: Full report and current trusted importer bind admission bytes via SHA256 before constructing trusted row and reject path/type changes; wire grew from report31 to current42 fields. Snapshot still uses path-based read with pre/post checks, so full adversarial replacement guarantee is unproved. Supported partial repair, complete root remedy unknown; current runtime untested.
- Review corrections: structural_change: worker yes -> unknown

## sosix_vfs_ipc_receive_abi_mismatch_2026-08-11 — SOSIX VFS IPC Receive ABI Mismatch

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_vfs_ipc_receive_abi_mismatch_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sosix_vfs_ipc_receive_abi_mismatch_2026-08-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/vfs/vfs_service.spl:176](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/services/vfs/vfs_service.spl#L176); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/ipc/syscall_ipc.spl:124](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/ipc/syscall_ipc.spl#L124)
- Review rationale: Full report legacy ABI contradictions are partly superseded: current VFS poll_once calls owned-v1 receive and parses bounded32-byte header, current kernel receive validates capacity then copies FIFO head. This is meaningful migration evidence but SOSIX caller/correlation and legacy compatibility are untraced; current aggregate validity and remedy remain uncertain.
- Review corrections: validity: worker valid -> uncertain; inspection_level: worker report_reviewed -> source_reviewed

## spec_gen_flattens_output_and_silently_drops_specs_2026-08-18 — `simple spec-gen` flattens mirror paths and silently drops most specs

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_gen_flattens_output_and_silently_drops_specs_2026-08-18.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spec_gen_flattens_output_and_silently_drops_specs_2026-08-18.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spec_gen/main.spl:33](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/spec_gen/main.spl#L33); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spec_gen/main.spl:126](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/spec_gen/main.spl#L126); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spec_gen/main.spl:191](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/spec_gen/main.spl#L191)
- Review rationale: Full report and current generator show all three specific corrections: _is_block accepts parenthesized calls, spec_relative_dir anchors test root independently of scope, skipped documents are counted/named and return2. Local remedy is source-present, so fixed_pending_verification rather than invalid; no runtime result claimed.
- Review corrections: solution: worker unknown -> known; structural_change: worker unknown -> no; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker keep_open -> fixed_pending_verification

## spec_it_block_last_expect_wins_masks_earlier_failure_2026-07-03 — Bug: `std.spec` `it` block only reports the LAST `expect()`/assertion, silently masking earlier failures

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_it_block_last_expect_wins_masks_earlier_failure_2026-07-03.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spec_it_block_last_expect_wins_masks_earlier_failure_2026-07-03.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:373](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/spec.spl#L373); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:1572](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/spec.spl#L1572)
- Review rationale: Full report and current nogc_sync_mut _execute_it/fail_assertion now accumulate error array and reset only at case start, superseding last-error overwrite in this implementation. Need matcher success/provisional cleanup and other spec-family/interpreter interception paths before asserting complete repair. Conservative uncertain/unknown classification accepted after this matching owner investigation; complete repair remains unqualified.
- Review corrections: validity: worker valid -> uncertain; solution: worker known -> unknown; inspection_level: worker report_reviewed -> source_reviewed

## spec_pending_call_still_counts_it_block_as_pass_2026-07-25 — `pending(...)` inside an `it` block is counted and reported as a PASS

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_pending_call_still_counts_it_block_as_pass_2026-07-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spec_pending_call_still_counts_it_block_as_pass_2026-07-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:373](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/spec.spl#L373); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:589](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/spec.spl#L589)
- Review rationale: Full report plus current _execute_it snapshots test_pending and returns pending without incrementing passes when pending count grows; failures win over pending, and pending() increments tally or records policy error. Source mechanism differs from old report; separate intrinsic/runner consumption not yet traced, so aggregate disposition remains uncertain with unknown complete remedy.
- Review corrections: validity: worker valid -> uncertain; inspection_level: worker report_reviewed -> source_reviewed

## spirv_builder_emit_function_ignores_preallocated_entry_point_id_2026-08-11 — `SpirvBuilder.emit_function()` cannot be paired with a pre-allocated entry-point id

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spirv_builder_emit_function_ignores_preallocated_entry_point_id_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spirv_builder_emit_function_ignores_preallocated_entry_point_id_2026-08-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vulkan/vulkan/spirv_builder.spl:138](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/plugins/backend_vulkan/vulkan/spirv_builder.spl#L138); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vulkan/vulkan/spirv_builder.spl:307](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/plugins/backend_vulkan/vulkan/spirv_builder.spl#L307)
- Review rationale: Full report and relocated builder show additive emit_function_with_id emits caller-supplied id and returns it; emit_entry_point consumes same id while old allocating method is preserved. This implements requested API remedy rather than raw-emit caller workaround. Known local source repair; Khronos/native regression execution still pending.
- Review corrections: solution: worker unknown -> known; structural_change: worker unknown -> no; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker keep_open -> fixed_pending_verification

## spkc_p2_authority_publication_journal_first_use_mkdir_race_2026-08-26 — SPKC P2 authority-publication journal first-use mkdir race

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spkc_p2_authority_publication_journal_first_use_mkdir_race_2026-08-26.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spkc_p2_authority_publication_journal_first_use_mkdir_race_2026-08-26.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/05_stdlib/spipe/src/storage/authority_publication_journal.js:21](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/05_stdlib/spipe/src/storage/authority_publication_journal.js#L21)
- Review rationale: Full report and complete current journal owner differ from frozen candidate: constructor/writeDurable/#lock use recursive mkdir, so cited nonrecursive EEXIST instruction is absent here. Parent durability and publisher composition remain unqualified; report is not invalidated by evolved source. Conservative uncertainty retained; owner unchanged since inventory.

## spkc_p3_authority_publication_atomic_journal_nonadmission_2026-08-26 — SPKC P3 authority-publication atomic journal is non-admitted

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spkc_p3_authority_publication_atomic_journal_nonadmission_2026-08-26.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spkc_p3_authority_publication_atomic_journal_nonadmission_2026-08-26.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/05_stdlib/spipe/src/storage/authority_publication_journal.js:49](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/05_stdlib/spipe/src/storage/authority_publication_journal.js#L49); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/05_stdlib/spipe/src/storage/authority_publication_journal.js:91](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/05_stdlib/spipe/src/storage/authority_publication_journal.js#L91)
- Review rationale: Full admission report and complete journal owner expose public mutable root/current/lock paths, public constructor, openSync wx lock without durable owner receipt, and finally path-only unlink. WeakSet brands journal instances but does not supply the required private P2 authority bridge. Current code cannot substantiate required durable authority contract; coordinated structural remedy required, exact repair unknown. Unchanged since inventory.
- Review corrections: structural_change: worker unknown -> yes; inspection_level: worker report_reviewed -> source_reviewed

## spl_thread_current_id_arity_mismatch_2026-09-16 — spl_thread_current_id: 0-arg source call vs 1-arg runtime backing

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spl_thread_current_id_arity_mismatch_2026-09-16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spl_thread_current_id_arity_mismatch_2026-09-16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2397](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/interpreter_extern/mod.rs#L2397); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:576](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs#L576)
- Review rationale: Full report resolution matches current seed: spl_thread_current_id is registered to dedicated zero-argument thread-local ID function; one-argument rt_thread_id retains its separate arity check. Local mapping repair is source-present and unchanged since inventory. No current execution; fixed_pending_verification, not invalidity.
- Review corrections: structural_change: worker yes -> no; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker fix_candidate -> fixed_pending_verification

## sql_stmt_cache_dict_get_never_hits_2026-07-20 — SQL `StatementCache.get_or_prepare` never hits cache — `Dict.get()` present-key landmine

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sql_stmt_cache_dict_get_never_hits_2026-07-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sql_stmt_cache_dict_get_never_hits_2026-07-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:32](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/database/sql/stmt_cache.spl#L32)
- Review rationale: Full report explicitly calls Dict.get/Some causation a hypothesis. Current cache uses contains_key then direct indexing, resets cached statement and preserves LRU insertion/eviction. This bypasses reported get/Option boundary but does not repair interpreter representation or prove repeated SQL execution; root solution remains unknown. Source unchanged since inventory.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## sqrt_f64_not_correctly_rounded_2026-09-01 — `std.math.special.sqrt_f64` is not correctly rounded (diverges from `rt_math_sqrt`)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sqrt_f64_not_correctly_rounded_2026-09-01.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sqrt_f64_not_correctly_rounded_2026-09-01.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/math/special.spl:82](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/math/special.spl#L82); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/math/special.spl:485](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/math/special.spl#L485)
- Review rationale: Full report closed header conflicts with OPEN body. Current sqrt delegates to range-reduced Newton kernel, stops at relative1e-15 threshold, rescales and returns without final correctly-rounded primitive. This supports ongoing rounding qualification gap, while another Newton iteration is not proven sufficient for every input. Root remedy unknown; report's decimal exact-representability wording is not relied on.
- Review corrections: validity: worker uncertain -> valid; solution: worker known -> unknown; inspection_level: worker report_reviewed -> source_reviewed

## ssa_write_count_quadratic_scan_2026_10_25 — ssa write count quadratic scan (workaround registered)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ssa_write_count_quadratic_scan_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/ssa_write_count_quadratic_scan_2026-10-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:1158](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl#L1158)
- Review rationale: Full report and current SSA counter agree on indexed dictionary counting, nonnegative local IDs, original-order second scan and count reset to emit each repeated ID once. This removes the identified linear lookup per instruction; output push cost remains and frozen producer is not repaired by source edits. Known local source fix pending admitted native original-workload verification.
- Review corrections: structural_change: worker unknown -> no; recommended_action: worker keep_open -> fixed_pending_verification

## sshd_password_verifier_zeroization_gap_2026-08-20 — SSHD password verifier zeroization gap

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sshd_password_verifier_zeroization_gap_2026-08-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sshd_password_verifier_zeroization_gap_2026-08-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_session.spl:435](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/apps/sshd/ssh_session.spl#L435); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_auth.spl:121](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/apps/sshd/ssh_auth.spl#L121); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/sshd.spl:385](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/apps/sshd/sshd.spl#L385)
- Review rationale: Full report plus production session435–441 confirm password requests are rejected, send publickey-only failure and close. ssh_auth still retains plaintext SshUser/authenticate_password/default-user helpers, but current daemon session does not call them. Guard is not invalidity: wipe/KDF verification remains an unmet capability, and restoring these legacy helpers would not be a root remedy. No compiler-resistant wipe proof inspected; solution/structural scope unknown.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## sspec_hollow_expect_clobbers_failure_message_2026-08-19 — sspec: hollow-expect provisional text clobbers real failure message (2026-08-19)

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sspec_hollow_expect_clobbers_failure_message_2026-08-19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sspec_hollow_expect_clobbers_failure_message_2026-08-19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/bdd.rs:122](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/interpreter_call/bdd.rs#L122); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/bdd.rs:1050](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/interpreter_call/bdd.rs#L1050)
- Review rationale: Full report's stale provisional-message mechanism differs from current BDD source: separate BDD_PROVISIONAL_MSG and BDD_FAILURE_MSG slots reset at example start; result takes real failure first and provisional only as fallback. This supports partial repair, but matcher-producer writes/pass cleanup not fully traced, so exact root closure remains uncertain, unknown remedy.
- Review corrections: solution: worker known -> unknown; structural_change: worker yes -> unknown; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker fixed_pending_verification -> keep_open

## sspec_no_dir_wide_prevention_scope_2026-08-07 — SSpec has no per-directory config hook so directory-wide prevention-mock scope is

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sspec_no_dir_wide_prevention_scope_2026-08-07.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sspec_no_dir_wide_prevention_scope_2026-08-07.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:1172](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/spec.spl#L1172)
- Review rationale: Full report and current prevent_file body confirm it forwards immediate prevent, with docstring requiring explicit per-example use; it is not automatic file/directory enforcement. Current config/discovery hook not fully traced, so broad absence claim remains uncertain. Convention workaround does not establish enforcement or known root repair.
- Review corrections: validity: worker valid -> uncertain; structural_change: worker yes -> unknown

## stage2_capsule_source_identity_is_sha256_of_empty_2026-09-13 — Site 12: the Stage-2 candidate freezes every native capsule's source identity as sha256("")

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_capsule_source_identity_is_sha256_of_empty_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_capsule_source_identity_is_sha256_of_empty_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_types.spl:1065](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_types.spl#L1065)
- Review rationale: Full report isolates released-source hash ordering. Current identity selector hashes nonempty held source or exact aligned phase1 owner row, requires unique module/path and consistent aliases, rejects empty digest and returns empty on ambiguity. This is substantive repair evidence, but phase1 capture population and freeze/collect fail-closed wiring still need tracing before complete fix acceptance.
- Review corrections: solution: worker known -> unknown; inspection_level: worker report_reviewed -> source_reviewed
