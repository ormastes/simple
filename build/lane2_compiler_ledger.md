# Compiler Lane 2 Ledger — failing test/02_integration/compiler specs

Date: 2026-11-12. Agent: COMPILER-LANE-2. Worktree: C:/dev/fix-lane2c-wt, branch
work/fix-lane2-compiler-20261112 (base origin/release/1.0.0).

## List provenance

The provided `/c/dev/phase2-wt/build/lane2_compiler_fails.txt` listed 37 **rendering**
specs — another lane's scope. The lane log's `=== DIR compiler ===` section was empty
(the full-lane run was still in progress), so this list was re-derived by running the
compiler lane in this worktree:

    ./bin/simple.exe test test/02_integration/compiler --timeout 300

The run was killed at the 2-hour budget with **41 failed spec files** accumulated
(~70% of the lane executed; it had reached driver/native_build_hir_sharding_spec).
Final fail list: `build/lane2_compiler_fail_list_final.txt`; full log:
`build/lane2_compiler_run.log`.

## Root-cause groups

### G1. LLVM serial lane: llc spawned via shell with unquoted path — PRODUCT-BUG, FIXED
- Symptom: `llc failed (exit 1): 'C:\Program' is not recognized as an internal or
  external command` whenever the resolved llc lives under `C:\Program Files\...`
  (ROCm LLVM 7.2 is the only llc on this host).
- Cause: `compile_ir_to_object` built a shell string `cmd.exe /c "{llc} {args} 2>&1"`.
  Through the seed runtime no quoting of the tool path survives (see G7).
- Fix: `src/compiler/70.backend/backend/llvm_backend_tools.spl` now spawns llc with
  the argv form `process_run(llc, llc_args)` — the same `llvm_llc_object_argv_v1`
  argv shared with the process-parallel pool — for both the initial run and the
  flaky-spawn retry (2>&1 merge dropped; `llvm_llc_error_diagnostic` already reads
  stdout/stderr separately). Shell string kept only for the error message.
- Verified: probe driver calling `compile_to_smf` advanced past the llc stage after
  the fix; it now stops at the independent SMF/COFF host check (G2).

### G2. SMF packaging requires ELF; Windows host target yields COFF — HOST-GAP
- `SMF packaging needs ELF object code, but the backend produced a COFF object for
  this host target` (fail-closed check, driver_aot_smf_output.spl:260). Intentional
  design: the SMF loader's `extract_code_from_object` only understands ELF.
- Affects: advanced_types_spec "compiles a try-operator program into an smf artifact"
  (facade `compile_to_smf`, host target, Windows host). Cannot pass on Windows as
  designed; host-gate or ledger.

### G3. Native-build process pool: shell form breaks with space-path llc — PRODUCT-BUG, ROOT-CAUSED, FIX BLOCKED (runtime/seed scope)
- `native_codegen_pool_v1.spl` spawns each job as `cmd.exe /c "{tool} {argv} > log 2>&1"`
  via `rt_process_spawn_async_value` (needs async spawn + poll + timeout tree-kill,
  and uses the shell for `> log 2>&1` redirect).
- The pool cannot be repaired from Simple code: quoting the tool path still fails
  through the seed spawn (G7), and the runtime exposes no async spawn-with-redirect
  that would allow bypassing the shell.
- Required fix (another lane's scope): give the seed's `rt_process_spawn_async` the
  same `/S` verbatim handling `native_shell_command` has for `rt_shell_exec`
  (src/compiler_rust/runtime/src/value/sffi/env_process.rs:524-545 vs 987-1017), or
  add an async spawn-with-stdout-to-file runtime API.

### G4. `union Name:` declarations with payloads/pattern matching — NEVER-IMPLEMENTED
- Not a wired keyword in the seed frontend; only union *type annotations* (`A | B`,
  `parser_parse_type_with_union`) exist. Parse error `unexpected token in expression:
  : ':'` at the decl colon. No `union X:` anywhere in src/. Do NOT implement.
- Affects: advanced_types_spec "accepts unions with payloads...", "compiles
  union-based control flow...".

### G5. SIMD `vec[N, T]` type annotations — NEVER-IMPLEMENTED
- No `vec` keyword/grammar in lexer or parser. Parse errors `expected type
  annotation`, `expected ], got IntLit '4'`. Do NOT implement.
- Affects: advanced_types_spec "accepts SIMD vector annotations...", "compiles a
  program with SIMD-typed signatures".

### G6. Spec-stale parser-error message expectations — SPEC-STALE, FIXED
- advanced_types_spec expected token-kind display names "Ampersand"/"Where"; the
  compiler's stable `tok_kind_name` rendering is "&"/"where" (both spec and renderer
  blame to the same 2026-08-11 commit, so the assertions never matched).
- Fix: `test/02_integration/compiler/advanced_types_spec.spl` now expects "got &" /
  "got where", matching the actual `expected ), got & '&'` / `got where 'where'`
  messages observed in the failing runs.

### G7. Seed `rt_process_run` lacks `/S` verbatim handling — SEED/RUNTIME-SCOPE, LEDGERED WITH EVIDENCE
- The C runtime's `win_cmd_build_line` has a verbatim `/S` passthrough for quoted
  cmd.exe payloads (src/runtime/platform/windows_command_line_private.h:122-137, fix
  for windows_cmd_shell_string_mangled_by_argv_quoting_2026-09-02). The **seed**
  runtime's argv spawns (`rt_process_run` env_process.rs:779-857 via `script_command`
  + plain `.arg()`, and `rt_process_spawn_async` :987-1017) do NOT: Rust argv quoting
  turns embedded `"` into `\"`, which cmd.exe keeps as literal quote characters.
  Reproduced in this worktree: `backend_shell_tuple("\"C:\Program Files\...\llc.exe\"
  --version")` → `'\"C:\Program Files\...\"' is not recognized`.
- Impact: every compiler shell-string spawn site that embeds a space-path tool breaks
  under the seed on this host (G1 pre-fix, G3 pool, WASM lane llvm_backend_tools.spl:730
  llc_cmd_str, link steps that name lld/clang with spaces).
- Runtime-lane scope; compiler side has routed the serial llc lane around it (G1).

## Per-file dispositions (41 files)

| Spec | Disposition |
|---|---|
| advanced_types_spec | PARTIALLY FIXED: 2 spec-stale tests fixed (G6); try-operator smf = host-gap (G2); 2 union + 2 SIMD tests = never-implemented (G4/G5, ledgered) |
| backend/array_value_copy_native_spec | HOST-GAP + G3: build refused by 24 GiB memory reserve under parallel lane load; then `sh -c` harness and pool shell space-path llc |
| backend/cranelift_arithmetic_spec | UNTRIAGED (timeout) — cranelift exec lane, "power/signed remainder" false |
| backend/cranelift_cross_module_call_abi_spec | UNTRIAGED — expected compile-time rejection `arg 0 is i64 but the callee declares f64`, call succeeded at runtime |
| backend/cranelift_narrow_cast_spec | UNTRIAGED — integer width matrix false |
| backend/gnu_runtime_owner_index_spec | UNTRIAGED — p2_p3 collection payload preservation, exit -1 |
| backend/guarded_optional_reference_native_spec | G3-suspect (native-build, 182 s) + UNTRIAGED detail |
| backend/llvm_env_get_local_owner_native_spec | UNTRIAGED (4 failed, 1.4 s — fast interpreter failure, likely product-bug) |
| backend/optional_collection_provenance_native_spec | G3-suspect (native-build, 182 s) + UNTRIAGED detail |
| bootstrap_intensive_spec | UNTRIAGED |
| bootstrap_planner_portable_hash_spec | UNTRIAGED |
| bootstrap_stage3_folded_module_const_type_spec | UNTRIAGED |
| cache/coherent_snapshot_cas_spec | UNTRIAGED |
| cache/cold_hir_compact_output_index_spec | UNTRIAGED |
| cache/cold_hir_package_drafts_scc_integration_spec | UNTRIAGED |
| cache/cooperative_namespace_host_admission_spec | DRIFT-SUSPECT: expected MissingPrerequisite(ImmutableSyncUnavailable), actual (...QualifiedEvidenceUnavailable) — spec-or-product drift, needs triage |
| cache/driver_store_catalog_spec | UNTRIAGED |
| cache/gateway_reader_pin_spec | UNTRIAGED |
| cache/generic_rr_edit_rebuild_spec | UNTRIAGED |
| cache/package_index_acceptance_binding_schedule_spec | DRIFT-SUSPECT: expected `destination-parent-not-canonical`, actual `destination-parent-unavailable` — needs triage |
| cache/package_index_acceptance_metadata_spec | UNTRIAGED |
| cache/package_index_acceptance_snapshot_spec | UNTRIAGED |
| cache/phase2_phase3_compatibility_manifest_spec | UNTRIAGED |
| cache/reader_pin_gc_guard_spec | UNTRIAGED |
| cache/reverse_reference_macro_generic_lifecycle_spec | UNTRIAGED |
| cache/reverse_reference_projection_receipt_spec | UNTRIAGED |
| cache/scv_build_validation_receipt_archive_v1_spec | UNTRIAGED |
| cache/three_payload_confined_object_broker_spec | UNTRIAGED |
| cache/three_payload_driver_coordinator_spec | UNTRIAGED |
| cache/three_payload_physical_file_broker_spec | UNTRIAGED |
| collection_builtin_resolution_spec | UNTRIAGED |
| compiler_interpreter_integration_spec | UNTRIAGED — largest group (27/30 failed), needs first triage priority |
| cross/aarch64_windows_cross_spec | HOST-GAP/toolchain: ARM64 PE link fails rc=-1073740791 on this Windows host toolchain |
| cross/i686_cross_spec | HOST-GAP/toolchain: `codegen init: Support for this target has not been implemented yet` (i386 PE) |
| cross/riscv_baremetal_cross_spec | HOST-GAP/toolchain: RV64 link `1 error generated` |
| cross/riscv_simpleos_cross_spec | HOST-GAP/toolchain: same family |
| data/attr_eval_order_parity_spec | UNTRIAGED |
| demand_compile_observability_integration_spec | UNTRIAGED (fast failure, 317 ms) |
| driver/hir_entry_payload_formation_guard_spec | UNTRIAGED |
| driver/hir_shard_scope_reclaim_spec | UNTRIAGED |
| driver/native_build_hir_optin_boundary_spec | UNTRIAGED (native-build family, G3-adjacent) |

## What was verified in this session
- G1 fix: probe `compile_to_smf` on a try-operator program — llc stage passes (was
  `'C:\Program' is not recognized`); fails next at the independent G2 ELF check.
- G6 fix: new expectation strings copied from the actual compiler error text captured
  in the single-file run of advanced_types_spec (the 2 repaired tests were not
  re-executed green — the lane was killed at budget; evidence is the verbatim error
  output).
- Lane re-run of the two repaired advanced_types tests plus a compiler-lane re-run
  remain as follow-up.

## Fix-cycle budget
Per-group verify/fix cycles used: G1 = 2 (diagnose+fix, probe verify). G6 = 1.
No group approached the 6-cycle cap; work stopped on the 2-hour wall-clock budget,
not on cycle exhaustion.
