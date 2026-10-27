# V2 lane 07 accepted review evidence

Accepted classifications captured: 49. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

## selfhost_parser_no_explicit_enum_values_2026-07-27 — Self-hosted parser has no `Variant = value` enum support — seed-only language feature

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/selfhost_parser_no_explicit_enum_values_2026-07-27.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/selfhost_parser_no_explicit_enum_values_2026-07-27.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:386](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl#L386); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:556](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl#L556)
- Review rationale: Full historical parser gap is partly superseded: current parse_enum_decl consumes TOK_ASSIGN, parses expression, stores each discriminant and passes the list to decl_enum_def at584. Downstream bridge/codegen behavior remains unqualified, so uncertain validity/unknown complete remedy is supported rather than a new implementation or invalid closure.
- Review corrections: validity: worker valid -> uncertain; solution: worker known -> unknown; structural_change: worker yes -> unknown; inspection_level: worker report_reviewed -> source_reviewed

## selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30 — Self-hosted stage4 `run` prints the literal placeholder x={x} instead of interpolating

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval.spl:524](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/interpreter/eval.spl#L524)
- Review rationale: Historical report explicitly records candidate ae4c3d56ce3 still printing placeholders and crashing its regression. Current eval_string_lit still returns raw s_val, but parser promotion may precede it; no inventory-to-target owner change. Next trace expand_string_interpolations invocation and promoted-node evaluation with the current regression. Static candidate presence is not a fix. Accepted only as a conservative unresolved classification after matching current-owner inspection; no current defect reproduction or complete repair is claimed.
- Review corrections: validity: worker valid -> uncertain; structural_change: worker yes -> unknown; inspection_level: worker report_reviewed -> source_reviewed

## set_method_route_dict_returns_nil_array_tuple_silent_noop_2026-08-02 — dict .set() returns nil under the seed JIT while the mutation lands; array/tuple .set

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/set_method_route_dict_returns_nil_array_tuple_silent_noop_2026-08-02.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/set_method_route_dict_returns_nil_array_tuple_silent_noop_2026-08-02.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3080](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl#L3080)
- Review rationale: Current pure-Simple MIR recognizes Dict.set, emits rt_dict_set and returns receiver_local. Original report concerns seed JIT nil return and array/tuple no-op; this owner cannot settle those engines or receivers. Inventory and target owner equal. Next inspect seed dict routing and array/tuple setters with original cross-engine fixture. Accepted only as a conservative unresolved classification after matching current-owner inspection; no current defect reproduction or complete repair is claimed.
- Review corrections: validity: worker valid -> uncertain; structural_change: worker yes -> unknown

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

## sffi_out_param_capability_violation_blocks_stage2_2026-08-27 — `ec6a500b42` breaks every Stage-2 build: `&mut` out-param fails the capability checker

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_out_param_capability_violation_blocks_stage2_2026-08-27.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sffi_out_param_capability_violation_blocks_stage2_2026-08-27.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/sffi/dynamic.spl:91](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/sffi/dynamic.spl#L91)
- Review rationale: Historical capability report is partly superseded: current checked dispatch scopes spl_wffi_try_call_i64_out under unsafe ffi/raw_ptr, distinguishes success0 from rejected transport, probes null pointer then validates two-element fallback. This is matching successor-path investigation, but capability checker/deployed producer behavior remains unqualified; uncertain classification and unknown complete root remedy accepted.
- Review corrections: validity: worker valid -> uncertain; inspection_level: worker report_reviewed -> source_reviewed

## sffi_ssh_aes256_gcm_decrypt_empty_failure_2026-08-27 — SSH AES-256-GCM SFFI decrypt collapses failure into an empty byte array

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_ssh_aes256_gcm_decrypt_empty_failure_2026-08-27.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sffi_ssh_aes256_gcm_decrypt_empty_failure_2026-08-27.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_cipher_live.spl:262](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/apps/sshd/ssh_cipher_live.spl#L262)
- Review rationale: Report tracks typed failure versus empty-array sentinel and documents v2 containment. Current direct wrapper calls v2 once, pops trailing status, rejects 0/1/unknown statuses and bounds payload length. Need confirm native/interpreter/registration owners and cross-lane negative conformance; report-level claim alone cannot admit complete remedy. Owner identical to inventory. Accepted valid unresolved classification for the supported historical failure and current containment; complete provider remedy remains unknown.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## sffi_torch_dynamic_facade_lexical_owner_gap_2026-08-27 — Dynamic Torch facade bypasses lexical raw-SFFI ownership

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_torch_dynamic_facade_lexical_owner_gap_2026-08-27.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sffi_torch_dynamic_facade_lexical_owner_gap_2026-08-27.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/torch/dyn_sffi_ops.spl:53](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/torch/dyn_sffi_ops.spl#L53)
- Review rationale: Current availability and lifecycle/linear-algebra calls have always-inline lexical unsafe helpers; clone checks availability/input/result. That disproves a blanket claim all facade paths remain unscoped, but does not audit all approximately129 calls or establish provider admission. Next enumerate every raw call against canonical owner and sealed-provider contract. Accepted only as a conservative unresolved classification after matching current-owner inspection; no current defect reproduction or complete repair is claimed.
- Review corrections: validity: worker valid -> uncertain; inspection_level: worker report_reviewed -> source_reviewed

## sfnt_fvar_option_match_nil_baremetal_2026-08-04 — val-assigned Option match yields nil on freestanding native lane; table.offset faults

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/encoding/sfnt.spl:85](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/encoding/sfnt.spl#L85); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md)
- Review rationale: Report binds nil fall-through to freestanding value-position Option extraction disassembly. Current parse_fvar_axes replaces extraction with scalar table scan and explicitly labels it a workaround, leaving compiler marshalling unresolved. Owner unchanged between targets. Accept keep-open/unknown root remedy; hosted success cannot qualify freestanding extraction.

## shard_mem_clamp_ignores_enclosing_cgroup_memory_max_2026-10-19 — Managed Linux worker filters SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB out of the compiler environment and shard_mem_clamp reads no cgroup memory.max, so HIR fanout inside a cgroup-contained build is sized by host MemAvailable

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `/tmp/simple-bug-triage-review-20261027/input/open_bugs_07.tsv#shard_mem_clamp_ignores_enclosing_cgroup_memory_max_2026-10-19`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/shard_mem_clamp.spl:400](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/cli/shard_mem_clamp.spl#L400)
- Review rationale: Current Linux owner walks memory.max from leaf cgroup to root, selects minimum numeric cap and combines it with declared tree budget even when host estimate opt-out is set. Historical enclosing-cap omission has an implemented local remedy; need relevant cgroup regression and mount-namespace behavior qualification. Source-level local remedy accepted as fixed_pending_verification; mount-namespace/runtime cases remain explicitly untested. No standalone report blob exists at target; frozen raw inventory record and inspected owner are the evidence.

## sheets_ascii_width_ambiguous_string_builder_owner_2026_10_12 — Spreadsheet ASCII width HIR import selects wrong string builder owner

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sheets_ascii_width_ambiguous_string_builder_owner_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sheets_ascii_width_ambiguous_string_builder_owner_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/office/sheets/ascii_width.spl:2](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/office/sheets/ascii_width.spl#L2); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/string_builder.spl:62](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/string_builder.spl#L62); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/common/string_builder.spl:1](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/common/string_builder.spl#L1); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/hir/string_builder_owner_collision_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/hir/string_builder_owner_collision_spec.spl); `history:5ef5ec6879d`
- Review rationale: Current ASC/JIS source imports std.common.string_builder.RtStringBuilder; library declares RtStringBuilder while app provider declares StringBuilder. Regression loads both physical providers, expects qualified import success and ambiguous import rejection. Commit 5ef5ec6879d supplies local owner repair, unchanged since inventory. Runtime/HIR execution remains unqualified.
- Review corrections: structural_change: worker unknown -> no; recommended_action: worker fix_candidate -> fixed_pending_verification

## shim_init_keepalive_function_ptr_cast_breaks_interpreter_2026-08-06 — shim_init calls _shim_keepalive whose fn-ptr-to-u64 casts fail: cannot cast function to...

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/shim_init_keepalive_function_ptr_cast_breaks_interpreter_2026-08-06.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/shim_init_keepalive_function_ptr_cast_breaks_interpreter_2026-08-06.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/abi/syscall_shim.spl:154](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/abi/syscall_shim.spl#L154); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/abi/syscall_shim.spl:272](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/abi/syscall_shim.spl#L272)
- Review rationale: Current shim_init unconditionally invokes _shim_keepalive, which converts spl_handle_* functions to u64 despite comment claiming no runtime call. Report's direct-state test bypasses this entry and is not repair. Need current interpreter function-cast semantics and a native DCE-preservation regression before selecting gating versus interpreter support. Accepted only as a conservative unresolved classification after matching current-owner inspection; no current defect reproduction or complete repair is claimed.
- Review corrections: validity: worker valid -> uncertain

## simple_timeout_seconds_ignored_by_light_daemon_budget_2026-08-17 — `SIMPLE_TIMEOUT_SECONDS` does not raise the light-daemon budget — specs report `daemon-no-response` instead of a verdict

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_timeout_seconds_ignored_by_light_daemon_budget_2026-08-17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simple_timeout_seconds_ignored_by_light_daemon_budget_2026-08-17.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/timeout_budget.spl:97](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/test_runner_new/timeout_budget.spl#L97); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_client.spl:122](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/test_runner_new/test_runner_client.spl#L122)
- Review rationale: Current timeout owner resolves flag > environment > default, client initializes from client_default_timeout_secs then overwrites valid explicit flags. This implements env propagation; report also describes no-response verdict honesty separately. Owners equal across snapshots; require env precedence spec and no-response verdict fixture before whole-record acceptance. Accepted fixed_pending_verification for named environment-budget propagation only; separate no-response verdict remains unqualified.
- Review corrections: structural_change: worker unknown -> no; inspection_level: worker report_reviewed -> source_reviewed

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

## simpleos_cpu_interrupt_quiescence_arch_adapter_blocker_2026-08-24 — SimpleOS CPU interrupt-quiescence architecture adapter blocker

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_cpu_interrupt_quiescence_arch_adapter_blocker_2026-08-24.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_cpu_interrupt_quiescence_arch_adapter_blocker_2026-08-24.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/x86_64/cpu.spl:369](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/arch/x86_64/cpu.spl#L369)
- Review rationale: Report requires scheduler-enforced CPU pin and exact saved mask/readback. Current x86_64 cpu_id resolves observed APIC identity through boot-sealed map, superseding reported constant zero. Need inspect all six arch adapters, pin enforcement and boot publication before accepting blanket missing-owner diagnosis. Accepted only as a conservative unresolved classification after matching current-owner inspection; no current defect reproduction or complete repair is claimed.
- Review corrections: validity: worker valid -> uncertain; structural_change: worker yes -> unknown; inspection_level: worker report_reviewed -> source_reviewed

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

## simpleos_installer_host_file_read_toctou_2026-08-20 — SimpleOS installer host file read TOCTOU and allocation bound

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_installer_host_file_read_toctou_2026-08-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_installer_host_file_read_toctou_2026-08-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/installer/image_bounded_file_reader.spl:10](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/installer/image_bounded_file_reader.spl#L10)
- Review rationale: Full report and complete bounded-reader owner show role/bound/type validation followed by unconditional bounded-nofollow-fd-reader-unavailable error for regular files; text wrapper propagates same error. Thus unsafe pathname reopen is contained by refusing reads, not replaced with functional bound/identity-safe reader. Valid unmet reader capability, root solution unknown; no invalid or fixed claim.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## simpleos_sftp_vfs_live_path_unavailable_2026-08-21 — SimpleOS SFTP VFS live path unavailable

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_sftp_vfs_live_path_unavailable_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/simpleos_sftp_vfs_live_path_unavailable_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_sftp_v3.spl:53](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/apps/sshd/ssh_sftp_v3.spl#L53); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_sftp_v3.spl:567](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/apps/sshd/ssh_sftp_v3.spl#L567)
- Review rationale: Current SFTP owner contains real VFS imports, bounded path/packet limits and _open path calling g_vfs_positioned_open with handle allocation, superseding report's negotiation-only assertion. Need authenticated session capability/root confinement and all operation dispatch plus live transcript before fixed status; missing original functionality is not invalid. Accepted only as a conservative unresolved classification after matching current-owner inspection; no current defect reproduction or complete repair is claimed.
- Review corrections: validity: worker valid -> uncertain; inspection_level: worker report_reviewed -> source_reviewed

## skia_raw_rgba_magic_constant_wrong_value_2026-09-06 — `RAW_RGBA_MAGIC` constant value does not match its documented 'RBPA' byte pattern

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/skia_raw_rgba_magic_constant_wrong_value_2026-09-06.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/skia_raw_rgba_magic_constant_wrong_value_2026-09-06.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/skia/feature/codec/raw_rgba.spl:14](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/skia/feature/codec/raw_rgba.spl#L14)
- Review rationale: Full report and complete codec show constant 1380012353 despite RBPA/0x52425041 contract; big-endian writer emits the constant and reader compares the same wrong value, so self-roundtrip masks defect. Correct value is 1380077633. Local constant correction is supported; current execution remains untested. Owner unchanged since inventory. Compatibility qualification is required before implementation: existing RAQA snapshots would fail a strict RBPA-only decoder; caller/fixture and version policy were not audited.
- Review corrections: solution: worker unknown -> known; structural_change: worker unknown -> no; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker keep_open -> fix_candidate

## slice_index_range_form_unimplemented_and_misnamed_2026-08-25 — `a[start:end]` vs `a[start..]`: two unimplemented slice features, and one misnamed diagnostic (2026-08-25)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/slice_index_range_form_unimplemented_and_misnamed_2026-08-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/slice_index_range_form_unimplemented_and_misnamed_2026-08-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:3407](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl#L3407); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3539](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl#L3539)
- Review rationale: Full report is partly superseded: current fatal range diagnostic names a[start..end]/a[start..] and explicitly distinguishes supported colon text form. Array method dispatch now routes runtime arrays to lower_runtime_array_slice, while text fallback excludes array types. Range rejection remains intentional protection for incomplete lowering; aggregate functionality/complete remedy unknown, not invalid.
- Review corrections: structural_change: worker yes -> unknown; inspection_level: worker report_reviewed -> source_reviewed

## smf_enum_def_serializes_variant_names_only_2026-08-21 — SMF `EnumDef` serializes variant NAMES only — arity, types, field names and discriminants are dropped

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_enum_def_serializes_variant_names_only_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_enum_def_serializes_variant_names_only_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/ast.spl:37](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/ast.spl#L37); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/smf_serialization.spl:339](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/smf_serialization.spl#L339); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize/deferred_deserialize.spl:515](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/40.mono/monomorphize/deferred_deserialize.spl#L515)
- Review rationale: Historical names-only EnumDef is superseded: current AST carries payload/discriminant lists; ENV2 writer serializes them, reader rejects missing marker and validates parallel list lengths before constructing fields. Coordinated format remedy is present, supporting fixed_pending_verification; constructor population and round-trip execution still need qualification, not invalid closure. Inspected codec unchanged since inventory.
- Review corrections: solution: worker unknown -> known; structural_change: worker unknown -> yes; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker keep_open -> fixed_pending_verification

## smf_gotrel32_applied_as_symbol_value_2026-09-18 — SMF wire relocation 4 (`GotRel32`) is applied with S = symbol address in both live loaders

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_gotrel32_applied_as_symbol_value_2026-09-18.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_gotrel32_applied_as_symbol_value_2026-09-18.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/smf_elf_parser.spl:246](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/smf_elf_parser.spl#L246); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/99.loader/module_loader_compat.spl:1460](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/99.loader/module_loader_compat.spl#L1460); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/smf/smf_dynlib.spl:775](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/smf/smf_dynlib.spl#L775)
- Review rationale: Full static report plus current emitter and both loaders show partial supersession: ELF GOTPCREL still maps wire4; compatibility loader allocates/fills one GOT slot per target and passes slot address to relocation formula; os dynlib explicitly rejects wire4 because GOT synthesis is unavailable. Silent symbol-as-slot misuse is contained, but full cross-loader functionality/qualification remains unresolved; no runtime reproduction claimed.
- Review corrections: solution: worker known -> unknown; inspection_level: worker report_reviewed -> source_reviewed

## smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10 — Simple and Rust SMF headers disagree on every offset from section_table_offset onward

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/smf_header.spl:28](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/smf_header.spl#L28); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/smf_header.spl:506](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/smf_header.spl#L506); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/common/src/smf/header.rs:7](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/common/src/smf/header.rs#L7)
- Review rationale: Full amended report and current definitions confirm Simple packed128 header reads section offset20, whereas repr(C) Rust fields require padding before first u64 after section_count and decode raw native struct with size_of. This is real cross-format incompatibility, not a missing-path inference. Migration must coordinate producers/readers/caches; exact safe remedy unknown and historical artifacts are not current execution.
- Review corrections: structural_change: worker unknown -> yes

## smf_manifest_written_but_never_verified_2026-08-17 — SmfManifest written but never verified on load

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_manifest_written_but_never_verified_2026-08-17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_manifest_written_but_never_verified_2026-08-17.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_api_interpret.spl:56](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_api_interpret.spl#L56)
- Review rationale: Full report and current try_load_smf_cached show source/ABI/interface admission added, but validate_smf still receives compile_options_hash_zero at100. Thus report is partially superseded yet options comparison remains a concrete unqualified surface. Requested options are not passed into this API; complete cache-key compatibility remedy remains unknown without inspecting all gate fields.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## smf_reader_writer_externs_unimplemented_2026-07-31 — SMF reader/writer externs are unimplemented scaffolding (2026-07-31)

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_reader_writer_externs_unimplemented_2026-07-31.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_reader_writer_externs_unimplemented_2026-07-31.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/smf_reader.spl:74](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/smf_reader.spl#L74); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/smf_writer.spl:1](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/smf_writer.spl#L1); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/smf_writer.spl:349](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/smf_writer.spl#L349)
- Review rationale: Full report and current reader now read bytes through SmfReaderMemory and populate full ordered symbols. Current writer validates relocation symbol/section/range and computes real serialized section/symbol layout instead of returning Ok([]). Obsolete scaffolding claim is superseded, but full output/reader contract not qualified; uncertain aggregate validity and unknown complete remedy supported after this semantic investigation.
- Review corrections: validity: worker valid -> uncertain; inspection_level: worker report_reviewed -> source_reviewed

## smf_writer_kernel_trailer_layout_skew — No compiler-emitted .smf is accepted as a role-2 library: writer and kernel trailer

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_writer_kernel_trailer_layout_skew.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/smf_writer_kernel_trailer_layout_skew.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/smf.spl:28](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/loader/smf.spl#L28); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/smf.spl:108](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/loader/smf.spl#L108); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/smf_header.spl:513](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/smf_header.spl#L513)
- Review rationale: Full report closed header is unsupported by body. Current kernel decodes role/arch/ABI bytes60/61/62, while compiler generic header decodes module_hash at60 and arch in identification. Their byte contracts still differ. Current envelope adaptation/target selection not fully traced, so no claim every emitted module fails today; coordinated format/admission remedy unknown.

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
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_gen_flattens_output_and_silently_drops_specs_2026-08-18.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spec_gen_flattens_output_and_silently_drops_specs_2026-08-18.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spec_gen/main.spl:33](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/spec_gen/main.spl#L33); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spec_gen/main.spl:126](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/spec_gen/main.spl#L126); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spec_gen/main.spl:191](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/spec_gen/main.spl#L191); `history:23d471bf267`
- Review rationale: Full report and current generator show all three specific corrections: _is_block accepts parenthesized calls, spec_relative_dir anchors test root independently of scope, skipped documents are counted/named and return2. Local remedy is source-present, so fixed_pending_verification rather than invalid; no runtime result claimed. Relevant source diff independently read in history 23d471bf267.
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
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spl_thread_current_id_arity_mismatch_2026-09-16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/spl_thread_current_id_arity_mismatch_2026-09-16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2397](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/interpreter_extern/mod.rs#L2397); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:576](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs#L576); `history:a4610d2fb15`
- Review rationale: Full report resolution matches current seed: spl_thread_current_id is registered to dedicated zero-argument thread-local ID function; one-argument rt_thread_id retains its separate arity check. Local mapping repair is source-present and unchanged since inventory. No current execution; fixed_pending_verification, not invalidity. Relevant source diff independently read in history a4610d2fb15.
- Review corrections: structural_change: worker yes -> no; inspection_level: worker report_reviewed -> source_reviewed; recommended_action: worker fix_candidate -> fixed_pending_verification

## sql_stmt_cache_dict_get_never_hits_2026-07-20 — SQL `StatementCache.get_or_prepare` never hits cache — `Dict.get()` present-key landmine

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sql_stmt_cache_dict_get_never_hits_2026-07-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sql_stmt_cache_dict_get_never_hits_2026-07-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:32](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/database/sql/stmt_cache.spl#L32)
- Review rationale: Full report explicitly calls Dict.get/Some causation a hypothesis. Current cache uses contains_key then direct indexing, resets cached statement and preserves LRU insertion/eviction. This bypasses reported get/Option boundary but does not repair interpreter representation or prove repeated SQL execution; root solution remains unknown. Source unchanged since inventory.
- Review corrections: inspection_level: worker report_reviewed -> source_reviewed

## sqlite_sffi_execute_close_return_code_contract_mismatch_2026-08-08 — sqlite_sffi return-code checks match the Rust seed but are inverted for the native C runtime

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sqlite_sffi_execute_close_return_code_contract_mismatch_2026-08-08.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/sqlite_sffi_execute_close_return_code_contract_mismatch_2026-08-08.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_sqlite.c:170](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/runtime/runtime_sqlite.c#L170); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/sqlite_sffi.spl:120](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io/sqlite_sffi.spl#L120); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/sqlite_sffi.spl:10](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io/sqlite_sffi.spl#L10); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/sqlite_embedded.spl:195](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io/sqlite_embedded.spl#L195); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs:1570](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs#L1570)
- Review rationale: Full report mismatch is source-repaired and ownership changed: current wrapper imports sqlite_embedded raw API rather than rt_sqlite externs; close and execute/batch use1 success0 failure. Legacy C providers now match1/0, and seed close/batch also match. Thus specific polarity defect is fixed_pending_verification with structural provider migration, not invalidity; current native qualification remains untested.
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
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ssa_write_count_quadratic_scan_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/ssa_write_count_quadratic_scan_2026-10-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:1158](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl#L1158); `history:b1a30d05283`
- Review rationale: Full report and current SSA counter agree on indexed dictionary counting, nonnegative local IDs, original-order second scan and count reset to emit each repeated ID once. This removes the identified linear lookup per instruction; output push cost remains and frozen producer is not repaired by source edits. Known local source fix pending admitted native original-workload verification. Relevant source diff independently read in history b1a30d05283.
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
